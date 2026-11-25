#!/usr/bin/env python3
"""Assemble the existing five-root evidence once, in its original private checkout."""
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

ROOT = Path("/workspace/p2-1-20261125")
TOOLS = ROOT / "verification/part2"
sys.path.insert(0, str(TOOLS))
from check_p21_joint_imports import public_targets
from repack_winner9_private_evidence import encoded, path_info, require, sha, write_new
from supervise_p21_resume import TARGETS, git, identity, selection, snapshots


def read(path):
    return json.loads(path.read_bytes())


def clean_head():
    identity()
    require(not git("status", "--porcelain", "--untracked-files=no"), "Tracked source or index changed")
    return git("rev-parse", "HEAD")


def run(out, label, tool, *args):
    log = out / (label + ".log")
    with log.open("x") as stream:
        result = subprocess.run([sys.executable, TOOLS / tool, *args], stdout=stream, stderr=subprocess.STDOUT)
    require(result.returncode == 0, f"{label} failed, see {log}")
    return log


def inspect_export(manifest, targets, public, native):
    rows = {r["module"]: r for r in targets["modules"]}
    archived = {p: entry["sha256"] for p, entry in manifest["files"].items() if entry["role"] == "verified project source"}
    require(archived == {"sources/" + r["source"]: r["source_sha256"] for r in rows.values()},
            "Exported project source members differ")
    selected, objects = manifest["accepted_modules"], manifest["object_manifest"]
    require(len(rows) == manifest["accepted_module_count"] == 140 and rows.keys() == selected.keys() == objects.keys()
            and not manifest["unselected_modules"] and not manifest["duplicate_owned_declarations"]
            and manifest["owned_declaration_count"] == manifest["unique_owned_declaration_count"],
            "Incomplete or duplicate project coverage")
    bindings = [v["binding"] for v in manifest["external_snapshots"].values()]
    require(len(bindings) == 2 and sorted((len(b["native_modules"]), b["snapshot"], b["snapshot_sha256"]) for b in bindings)
            == [(n, r["path"], r["sha256"]) for n, r in zip((515, 518), native)], "Unexpected native contexts")
    for name, r in rows.items():
        require(selected[name]["source_sha256"] == objects[name]["source_sha256"] == r["source_sha256"]
                and selected[name]["object_sha256"] == objects[name]["object_sha256"],
                "Exported source/object differs: " + name)
    wanted = {}
    for owner in public:
        member, = (p for p in selected[owner]["artifact_paths"] if p.endswith("/declarations.json"))
        wanted[member] = owner
    types = {}
    for package in manifest["packages"]:
        archive = Path(package["path"])
        require(path_info(archive)["sha256"] == package["sha256"], "Export package changed: " + str(archive))
        owners = set(package["modules"]) & public.keys()
        if owners:
            with tarfile.open(archive, "r|gz") as tar:
                for member in tar:
                    owner = wanted.get(member.name)
                    if owner not in owners:
                        continue
                    raw = tar.extractfile(member).read()
                    require(sha(raw) == manifest["files"][member.name]["sha256"], "Declaration member changed")
                    records = json.loads(raw)["declarations"]
                    for name in public[owner]:
                        row, = (r for r in records if (r["module"], r["name"]) == (owner, name))
                        require(name not in types and isinstance(row["type"], str) and row["type"].strip()
                                and "⋯" not in row["type"], "Missing, duplicate or truncated public type: " + name)
                        types[name] = {"owner": owner, "type": row["type"]}
    require(len(types) == 26 and types.keys() == {n for names in public.values() for n in names},
            "Public type coverage differs")
    return types


def main():
    require(Path.cwd().resolve() == ROOT, "Run in " + str(ROOT))
    head = clean_head()
    groups, roots, _, _ = selection()
    targets = read(TARGETS)
    public = public_targets(targets["roots"])
    modules = [n for group in groups for n in group]
    paths = snapshots()
    require(len(paths) == 2 and all(paths), "Both authorized snapshots must be qualified")
    native = [path_info(p) for p in paths]
    anchor = targets["source_snapshot_commit"]
    sources = [r["source"] for r in targets["modules"]]
    subprocess.run(["git", "diff", "--quiet", anchor, head, "--", *sources], check=True)
    reuse = TARGETS.with_name("REUSED_EVIDENCE.json")
    inputs = [path_info(p.resolve()) for p in (TARGETS, reuse)]
    parent = ROOT / ".lake/p2-private/exports"
    parent.mkdir(exist_ok=True, parents=True)
    out = Path(tempfile.mkdtemp(dir=parent, prefix="p21-final-"))
    print("Evidence directory", out, flush=True)
    export = out / "export"
    run(out, "export", "export_winner9_private_evidence.py", "--output-dir", export, "--split", "group",
        "--extra-evidence", TARGETS, "--extra-evidence", reuse, *modules)
    manifest_path = export / "manifest.json"
    manifest_info = path_info(manifest_path)
    m = read(manifest_path)
    for path, info in zip((TARGETS, reuse), inputs):
        require(m["files"]["worktree/" + str(path)]["sha256"] == info["sha256"], "Exported input changed")
    types = inspect_export(m, targets, public, native)
    joint_output = run(out, "joint", "check_p21_joint_imports.py", "--export-manifest", manifest_path,
                       "--targets", TARGETS, "--memory-mb", "11264")
    receipt = Path(joint_output.read_text().strip())
    joint = read(receipt)
    probe, log = Path(joint["probe"]), ROOT / joint["command_result"]["log"]
    require(joint["status"] == "JOINT_IMPORT_COMPATIBLE" and joint["inputs_unchanged"] is True
            and joint["roots"] == roots and joint["project_modules"] == sorted(modules)
            and len(joint["public_checks"]) == 26 and set(joint["public_checks"]) == types.keys()
            and all(joint[k] is False for k in ("compile_credit", "kernel_credit", "audit_credit"))
            and joint["frozen_files"][str(manifest_path)] == manifest_info["sha256"],
            "Joint receipt differs from selected evidence")
    joint_files = [path_info(p) for p in (receipt, probe, log)]
    require(joint_files[1]["sha256"] == joint["frozen_files"][str(probe)]
            and joint_files[2]["sha256"] == joint["command_result"]["log_sha256"], "Joint evidence changed")
    tool = "repack_winner9_private_evidence.py"
    catalog, archive, verified = (out / n for n in ("catalog.json", "p21.tar.xz", "verification.json"))
    run(out, "catalog", tool, "catalog", "--repo", ROOT, "--output", catalog)
    catalog_info = path_info(catalog)
    run(out, "repack", tool, "repack", export, "--manifest-sha256", manifest_info["sha256"],
        "--catalog", catalog, "--output", archive)
    run(out, "verify", tool, "verify", archive, "--repo", ROOT, "--git-tree", head, "--output", verified)
    with tarfile.open(archive, "r|xz") as tar:
        member = next(m for m in tar if m.name == "REPOSITORY_SOURCE_CATALOG.json")
        require(member.size == catalog_info["bytes"] and sha(tar.extractfile(member).read()) == catalog_info["sha256"],
                "Archived catalog differs from standalone catalog")
    report = read(verified)
    require(clean_head() == head and report["git_tree"] == git("rev-parse", head + "^{tree}")
            and report["archive"] == path_info(archive) and report["accepted_module_count"] == 140
            and report["owned_declaration_count"] == m["owned_declaration_count"], "Archive verification differs")
    packages = [{k: p[k] for k in ("path", "bytes", "sha256")} for p in m["packages"]]
    attached = inputs + native + [manifest_info, *packages, *joint_files, catalog_info]
    require(all(path_info(Path(r["path"])) == r for r in attached), "Finalization input changed")
    summary = {"scope": "P2.1 five-root evidence packaging", "full_p2_complete": False,
               "source_snapshot_commit": anchor, "git_commit": head, "git_tree": report["git_tree"],
               "accepted_modules": 140, "owned_declarations": m["owned_declaration_count"], "public_types": types,
               "inputs": inputs, "export_manifest": manifest_info, "export_packages": packages,
               "joint_receipt_probe_log": joint_files, "native_snapshots": native, "catalog": catalog_info, "archive": report["archive"],
               "verification": path_info(verified), "stage_logs": [path_info(p) for p in sorted(out.glob("*.log"))]}
    final = out / "FINALIZATION.json"
    write_new(final, encoded(summary))
    print(json.dumps({"finalization": path_info(final), "accepted_modules": 140, "public_types": types}, ensure_ascii=False))


if __name__ == "__main__":
    main()
