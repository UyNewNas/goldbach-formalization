#!/usr/bin/env python3
"""Verify a pinned, complete P3 owned-evidence archive without running Lean or cloud jobs.

The profile is a separately reviewed, fixed input. Receipt declarations never choose
the expected scope, commit, or content hashes. Dependency bytes absent from the tar
remain hash-bound evidence, not a new local replay or new dependency credit.
"""
from __future__ import annotations
import argparse
import base64
from collections import Counter
from datetime import datetime, timezone
import hashlib
import importlib.util
import io
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}
PINNED_VERIFIERS = {
    "verification/p36/compile_p36_local.py": "be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709",
    "verification/verify_part3_continuation.py": "9afe49d061639c5d98926185b4e6301e3ff7222e35550839fbfe1a4c785bdcc8",
    "verification/verify_part3_distribution.py": "bef3b8ba73736d7a787aaf31fe49cb8017de4f8d7c71ee4220c6c3dbc47607f4",
    "verification/Part3DistributionAudit.lean": "45b20653d5510b9639a653913ba39fdc21d402f45342d6dd7d2c51439f01ed93",
    "verification/verify_variable_envelope_boxes.py": "8979f29bda930f19f06b29d840ea1f997d1de631b45a6eeb35d8a801149bc916",
}

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_sha(path):
    with Path(path).open("rb") as source:
        digest = hashlib.sha256()
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()

def digest_json(value):
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())

def safe_relative(name):
    require(isinstance(name, str) and name not in ("", ".") and "\\" not in name and "\x00" not in name,
            "Invalid evidence path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and path.as_posix() == name,
            "Non-canonical evidence path: " + name)
    return path

def preserve(path, content):
    path = Path(path)
    require(not path.is_symlink(), "Refusing to write through symlink")
    if path.exists():
        require(path.is_file() and path.read_bytes() == content, "Existing bytes differ: " + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)

def safe_unpack(archive_bytes, files, destination):
    destination.mkdir(parents=True, exist_ok=True)
    require(not destination.is_symlink(), "Extraction root is a symlink")
    root = destination.resolve()
    for name, record in files.items():
        safe_relative(name)
        require(set(record) == {"path", "sha256", "bytes"} and isinstance(record["path"], str)
                and PurePosixPath(record["path"]).is_absolute()
                and re.fullmatch(r"[0-9a-f]{64}", record["sha256"])
                and type(record["bytes"]) is int and record["bytes"] >= 0,
                "Invalid receipt file record")
    with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:xz") as tar:
        members = tar.getmembers()
        require(len(members) == len(files) and len({m.name for m in members}) == len(members)
                and {m.name for m in members} == set(files), "Tar membership differs")
        for member in members:
            rel = safe_relative(member.name)
            record = files[member.name]
            require(member.type == tarfile.REGTYPE and not member.issparse()
                    and member.size == record["bytes"], "Nonregular or wrong-sized tar payload")
            payload = tar.extractfile(member).read()
            require(len(payload) == member.size and sha(payload) == record["sha256"],
                    "Payload bytes/hash differ: " + member.name)
            path = destination.joinpath(*rel.parts)
            require(path.resolve().is_relative_to(root), "Extraction path escaped root")
            for parent in [path, *path.parents]:
                if parent == root:
                    break
                require(not parent.is_symlink(), "Extraction path contains symlink")
            preserve(path, payload)

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module

def fixed_git_blobs(project, commit, paths):
    paths = list(paths)
    for path in paths:
        safe_relative(path)
    command = ["git", "--no-optional-locks", "-C", str(project), "cat-file", "--batch"]
    result = subprocess.run(command, input="".join(commit + ":" + p + "\n" for p in paths).encode(),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    data, pos, blobs = result.stdout, 0, {}
    for path in paths:
        end = data.index(b"\n", pos)
        header = data[pos:end].split()
        require(len(header) == 3 and header[1] == b"blob", "Missing fixed-commit blob: " + path)
        size = int(header[2])
        body = data[end + 1:end + 1 + size]
        require(len(body) == size and data[end + 1 + size:end + 2 + size] == b"\n",
                "Invalid Git batch framing")
        require(hashlib.sha1(b"blob " + str(size).encode() + b"\0" + body).hexdigest() == header[0].decode(),
                "Git blob object identity differs")
        blobs[path] = body
        pos = end + 2 + size
    require(pos == len(data), "Unexpected Git batch output")
    return blobs

def validate_transport(profile, work, transport):
    """Recheck captured terminal states, pages and decoded payloads independently."""
    terminals = json.loads((work / "EXPORT_TERMINALS.json").read_bytes())
    expected = profile["exports"]
    records = transport["exports"]
    page_size = profile["page_bytes"]
    require(type(page_size) is int and 0 < page_size <= 65536
            and transport["transport_page_bytes"] == page_size
            and len(expected) == len(terminals) == len(records), "Transport task/page profile differs")
    chunks = []
    for spec, terminal, record in zip(expected, terminals, records):
        kind, index = spec["kind"], spec["index"]
        require(terminal["task_id"] == record["task_id"] == spec["task_id"]
                and terminal["kind"] == kind and terminal["index"] == index
                and terminal["status"] == record["status"] == "succeeded"
                and terminal["exit_code"] == record["exit_code"] == 0
                and terminal["output_truncated"] is record["output_truncated"] is False,
                "Transport task identity or terminal state differs")
        stem = "receipt" if kind == "receipt" else "archive-" + str(index)
        stdout = (work / (stem + ".stdout")).read_bytes()
        require(len(stdout) == terminal["output_bytes"] == record["stdout_bytes"]
                and sha(stdout) == record["stdout_sha256"], "Transport stdout capture differs")
        offsets = list(range(0, len(stdout), page_size))
        names = {stem + "-page-" + str(n).zfill(7) + ".b64" for n in offsets}
        require(record["page_count"] == len(offsets)
                and {p.name for p in work.glob(stem + "-page-*.b64")} == names,
                "Transport page membership/count differs")
        for offset in offsets:
            page = work / (stem + "-page-" + str(offset).zfill(7) + ".b64")
            data = base64.b64decode("".join(page.read_text().split()), validate=True)
            require(data == stdout[offset:offset + page_size], "Transport page bytes/offset differ")
        lines = stdout.splitlines()
        require(len(lines) == 4 and lines[0].startswith(b"P36_EXPORT_META ")
                and lines[1] == b"P36_EXPORT_BASE64_BEGIN"
                and lines[3] == b"P36_EXPORT_BASE64_END", "Transport stdout envelope differs")
        meta = json.loads(lines[0][len(b"P36_EXPORT_META "):])
        payload = base64.b64decode(lines[2], validate=True)
        require(meta == record["payload"] and meta["kind"] == kind and meta["index"] == index
                and len(payload) == meta["bytes"] and sha(payload) == meta["sha256"],
                "Transport decoded payload differs")
        if kind == "receipt":
            require(index == -1 and meta["offset"] == 0 and meta["total_bytes"] == len(payload)
                    and payload == (work / "RECEIPT.json").read_bytes(), "Transport receipt differs")
        else:
            require(kind == "archive" and index == len(chunks)
                    and meta["offset"] == sum(len(c) for c in chunks)
                    and meta["total_bytes"] == profile["archive_bytes"], "Transport archive segment differs")
            chunks.append(payload)
    require(b"".join(chunks) == (work / "evidence.tar.xz").read_bytes(), "Transport archive assembly differs")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--profile", type=Path, required=True)
    ap.add_argument("--check-only", action="store_true")
    args = ap.parse_args()
    profile_path = args.profile.resolve()
    profile_bytes = profile_path.read_bytes()
    profile = json.loads(profile_bytes)
    verifier_sha256 = file_sha(Path(__file__))
    work = profile_path.parent
    project = Path(profile["project"]).resolve()
    destination = Path(profile["destination"])
    expected_targets = profile["targets"]
    require(expected_targets and len(set(expected_targets)) == len(expected_targets), "Invalid pinned targets")
    for name in expected_targets:
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", name),
                "Invalid target module name")
    receipt_path, archive = work / "RECEIPT.json", work / "evidence.tar.xz"
    receipt_bytes, archive_bytes = receipt_path.read_bytes(), archive.read_bytes()
    require(sha(receipt_bytes) == profile["receipt_sha256"], "Pinned original receipt hash differs")
    require(len(archive_bytes) == profile["archive_bytes"]
            and sha(archive_bytes) == profile["archive_sha256"], "Pinned archive size/hash differs")
    receipt = json.loads(receipt_bytes)
    require(receipt["status"] == "VERIFIED_OWNED" and receipt["p36_closed"] is False
            and receipt["targets"] == expected_targets and receipt["source_commit"] == profile["source_commit"]
            and receipt["archive_sha256"] == profile["archive_sha256"]
            and receipt["archive_bytes"] == profile["archive_bytes"], "Receipt scope or identity differs")
    for field in ("strict_compilation", "bundled_kernel_replay", "complete_transitive_axiom_audit",
                  "fresh_target_compilation_this_task", "kernel_replay_this_task"):
        require(receipt[field] is True, "Missing formal phase: " + field)
    require(set(receipt["allowed_transitive_axioms"]) == ALLOWED, "Receipt axiom allowlist differs")
    original_terminal = json.loads((work / "ORIGINAL_TASK_TERMINAL.json").read_bytes())
    require(original_terminal["task_id"] == profile["original_task_id"]
            and original_terminal["status"] == "succeeded" and original_terminal["exit_code"] == 0
            and original_terminal["output_truncated"] is False, "Original formal task did not finish intact")
    transport = json.loads((work / "TRANSPORT_VERIFICATION.json").read_bytes())
    require(transport["status"] == "PASS" and transport["archive_sha256"] == profile["archive_sha256"]
            and transport["receipt_sha256"] == profile["receipt_sha256"], "Transport verification differs")
    validate_transport(profile, work, transport)
    expanded = work / "expanded"
    safe_unpack(archive_bytes, receipt["files"], expanded)
    files = receipt["files"]
    def member(name):
        require(name in files, "Missing archived evidence member: " + name)
        return expanded / name
    def object_record(base, mapping):
        require(isinstance(mapping, dict) and base in mapping and mapping
                and set(mapping) <= {base, base + ".private", base + ".server"},
                "Object/sidecar set differs: " + base)
        for path, digest in mapping.items():
            require(re.fullmatch(r"[0-9a-f]{64}", digest), "Invalid object digest")
            require(snapshots.get(path) == digest, "Object absent/different in original snapshot: " + path)
    report = json.loads(member("run/report.json").read_bytes())
    binding = json.loads(member("binding.json").read_bytes())
    state = json.loads(member("lineage/local-state.json").read_bytes())
    require(file_sha(member("run/report.json")) == receipt["runner_report_sha256"]
            and file_sha(member("binding.json")) == receipt["binding_sha256"], "Report/binding digest differs")
    require(report["status"] == "VERIFIED_OWNED" and report["strict_owned"] is True
            and report["targets"] == expected_targets and not report["blockers"], "Original run did not pass")
    require(binding["source_commit"] == receipt["source_commit"]
            and binding["source_tree"] == receipt["source_tree"], "Source commit/tree binding differs")
    actual_tree = subprocess.check_output(["git", "--no-optional-locks", "-C", str(project),
                       "rev-parse", profile["source_commit"] + "^{tree}"], text=True).strip()
    require(actual_tree == binding["source_tree"], "Fixed local Git tree differs")
    remote = PurePosixPath(report["project"])
    run = PurePosixPath(receipt["runner_run"])
    build = PurePosixPath(report["build_dir"])
    objdir = build / "lib/lean"
    require(remote.is_absolute() and build.is_relative_to(remote) and run.parent == build / "runs",
            "Unexpected original project/build/run path")
    require(report["runner_sha256"] == binding["runner_sha256"] == receipt["runner_sha256"]
            == PINNED_VERIFIERS["verification/p36/compile_p36_local.py"], "Runner identity differs")
    snapshots = binding["snapshot_sha256"]
    require(len(snapshots) == receipt["snapshot_count"], "Snapshot count differs")
    require(all(PurePosixPath(p).is_absolute() and re.fullmatch(r"[0-9a-f]{64}", h)
                for p, h in snapshots.items()), "Malformed original snapshot")
    initial = binding["initial_project_sha256"]
    initial_rel = {}
    for path, digest in initial.items():
        p = PurePosixPath(path)
        require(p.is_relative_to(remote), "Initial project binding escapes project")
        rel = p.relative_to(remote).as_posix()
        safe_relative(rel)
        initial_rel[rel] = digest
        require(path not in snapshots or snapshots[path] == digest, "Initial/snapshot source binding differs")
    blobs = fixed_git_blobs(project, profile["source_commit"], initial_rel)
    for rel, digest in initial_rel.items():
        require(sha(blobs[rel]) == digest and file_sha(project / rel) == digest,
                "Fixed-commit or current selected/config bytes differ: " + rel)
    for name, spec in files.items():
        if name.startswith("config/"):
            rel = name.removeprefix("config/")
            require(rel in initial_rel and file_sha(member(name)) == initial_rel[rel]
                    and member(name).read_bytes() == blobs[rel], "Archived fixed config differs: " + rel)
    for rel, digest in PINNED_VERIFIERS.items():
        require(file_sha(member("config/" + rel)) == digest, "Previously accepted verifier bytes differ: " + rel)
    config_dir = expanded / "config"
    sys.path.insert(0, str(config_dir / "verification"))
    helper = load_module("p36_local_original_audit_helper", config_dir / "verification/verify_part3_continuation.py")
    runner = load_module("p36_local_original_runner_definitions", config_dir / "verification/p36/compile_p36_local.py")
    require(Path(helper.baseline.__file__).resolve() ==
            (config_dir / "verification/verify_part3_distribution.py").resolve(), "Validator imported outside archive")
    require(set(helper.baseline.ALLOWED) == ALLOWED, "Original validator allowlist differs")
    require(runner.digest_json({"check": [1, False, "x"]}) == digest_json({"check": [1, False, "x"]}),
            "JSON digest implementation differs")
    source_manifest = json.loads(member("SOURCE_SELECTION.json").read_bytes())
    require(receipt["source_manifest"] == report["source_manifest"]
            and receipt["source_manifest"]["sha256"] == profile["source_manifest_sha256"]
            and file_sha(member("SOURCE_SELECTION.json")) == profile["source_manifest_sha256"],
            "Selected source manifest identity differs")
    require(files["SOURCE_SELECTION.json"]["path"] == receipt["source_manifest"]["path"]
            and snapshots[receipt["source_manifest"]["path"]] == profile["source_manifest_sha256"]
            and initial[receipt["source_manifest"]["path"]] == profile["source_manifest_sha256"],
            "Source manifest path/snapshot binding differs")
    selections = source_manifest["sources"]
    selected = {e["module"]: e for e in selections}
    require(len(selected) == len(selections) and set(expected_targets) <= set(selected),
            "Duplicate or absent selected source")
    for name, selection in selected.items():
        rel = name.replace(".", "/") + ".lean"
        require(selection["selected_path"] == rel
                and initial_rel[rel] == selection["selected_sha256"], "Selected source binding differs: " + name)
    pins = {p["name"]: p["rev"] for p in json.loads(member("config/lake-manifest.json").read_bytes())["packages"]}
    require(report["dependency_pins"] == binding["dependency_pins"] == receipt["dependency_pins"] == pins,
            "Dependency pins differ")
    require(pins["goldbach"] == "09b97db5764ade1246bfb77206baa1b124760958"
            and pins["mathlib"] == "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1", "Accepted dependency pins differ")
    compiler = report["compiler"]
    require(compiler == receipt["compiler"] and snapshots[compiler["path"]] == compiler["sha256"],
            "Compiler snapshot differs")
    toolchain = PurePosixPath(compiler["path"]).parent.parent
    checker = str(toolchain / "bin/leanchecker")
    require(snapshots[checker] == receipt["checker_sha256"]
            and "version 4.33.0-rc1," in compiler["version"]
            and "62eed1db4d67327ec8120be05f1a1b0847d74561" in compiler["version"],
            "Bundled compiler/checker version binding differs")
    require(member("config/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.33.0-rc1",
            "Toolchain pin differs")
    lean_path = report["lean_path"]
    require(lean_path == binding["lean_path"] == receipt["lean_path"]
            and lean_path[0] == str(objdir) and lean_path[-1] == str(toolchain / "lib/lean")
            and len(set(lean_path)) == len(lean_path), "LEAN_PATH identity/order differs")
    stages = report["commands"]
    require(stages and len({s["name"] for s in stages}) == len(stages)
            and all(s["exit_code"] == 0 for s in stages), "Duplicated or failed original stage")
    by_stage = {s["name"]: s for s in stages}
    def log_body(record, archive_name):
        path = member(archive_name)
        require(files[archive_name]["path"] == record["log"]
                and file_sha(path) == record["log_sha256"], "Command log digest/path differs")
        first, body = path.read_text().split("\n", 1)
        require(first == "command=" + json.dumps(record["command"]), "Command log header differs")
        return body
    bodies = {}
    for stage in stages:
        require(PurePosixPath(stage["log"]) == run / (stage["name"] + ".log"), "Stage log path differs")
        bodies[stage["name"]] = log_body(stage, "run/" + stage["name"] + ".log")
    require(by_stage["lean-version"]["command"] == [compiler["path"], "--version"]
            and bodies["lean-version"].strip() == compiler["version"], "Compiler version command differs")
    package_roots = {}
    for package, pin in pins.items():
        stage = by_stage["pin-" + package]
        command = stage["command"]
        require(len(command) == 6 and command[:3] == ["git", "--no-optional-locks", "-C"]
                and command[-2:] == ["rev-parse", "HEAD"]
                and PurePosixPath(command[3]).name == package
                and bodies["pin-" + package].strip() == pin, "Dependency HEAD log differs")
        package_roots[package] = PurePosixPath(command[3])
        require(by_stage["clean-" + package]["command"] ==
                ["git", "--no-optional-locks", "-C", command[3], "status", "--porcelain", "--untracked-files=no"]
                and not bodies["clean-" + package].strip(), "Dependency clean log differs")
    expected_lean_path = [str(objdir)] + [str(package_roots[k] / ".lake/build/lib/lean")
                         for k in sorted(package_roots)] + [str(toolchain / "lib/lean")]
    require(lean_path == expected_lean_path, "LEAN_PATH does not match recorded package roots")
    modules = report["modules"]
    order = report["topological_order"]
    require(len(order) == len(set(order)) and set(order) == set(modules), "Incomplete topological graph")
    require(report["counts"] == dict(Counter(m["kind"] for m in modules.values()))
            and report["project_module_count"] == sum(m["package"] == "project" for m in modules.values()),
            "Graph module counts differ")
    require(state["schema"] == 1, "Unsupported archived local-state schema")
    require(not report.get("transferred_verified_objects"), "Transferred bundle requires its own explicit profile review")
    signatures, reuse_count, compiled_count = {}, 0, 0
    for name in order:
        node = modules[name]
        imports = list(node["imports"])
        require(len(imports) == len(set(imports)) and all(i in signatures for i in imports),
                "Missing, cyclic, duplicated, or late import: " + name)
        dependencies = {i: signatures[i] for i in imports}
        if node.get("source"):
            require(snapshots.get(node["source"]) == node["source_sha256"], "Source snapshot differs: " + name)
        if node["package"] == "project":
            rel = name.replace(".", "/") + ".lean"
            require(name in selected and node["source"] == str(remote / rel)
                    and node["source_sha256"] == initial_rel[rel], "Project module source differs")
            source_text = blobs[rel].decode()
            source_imports = runner.parse_imports(source_text)
            if name != "Init" and not re.search(r"(?m)^\s*prelude\b", runner.lean_code(source_text)):
                source_imports = list(dict.fromkeys(["Init", *source_imports]))
            require(source_imports == imports, "Actual project import list differs: " + name)
        objects = node["objects"]
        if node["kind"] in {"cached", "core"}:
            require(node["action"] == "external_cache", "Cached dependency action differs")
            object_record(node["cached_object"], objects)
            signatures[name] = digest_json({"objects": objects, "imports": dependencies,
                                           "source": node.get("source_sha256")})
            continue
        require(node["kind"] == "build" and node["action"] in {"compiled", "reused"}, "Unsupported build action")
        old = state["modules"][name]
        require(old["exit_code"] == 0 and old["source"] == node["source"]
                and old["source_sha256"] == node["source_sha256"] and old["objects"] == objects,
                "Archived local-state lineage differs")
        strict = old["strict"]
        require(type(strict) is bool, "Invalid warning policy")
        input_data = {"source": node["source"], "source_sha256": node["source_sha256"],
                      "compiler": compiler, "strict": strict, "imports": dependencies,
                      "lean_path": lean_path, "trust": 0, "threads": 1}
        key = digest_json(input_data)
        require(key == old["input_key"] == node["input_key"]
                and all(old.get(k) == value for k, value in input_data.items()),
                "Recursive compile input key differs: " + name)
        object_record(str(objdir / (name.replace(".", "/") + ".olean")), objects)
        source_suffix = name.replace(".", "/") + ".lean"
        require(node["source"].endswith("/" + source_suffix), "Source does not retain module suffix")
        source_root = node["source"][:-len(source_suffix)-1]
        command = [compiler["path"], "-t0", "-j1", "-R", source_root]
        if strict:
            command.append("-DwarningAsError=true")
        command += ["-o", str(objdir / (name.replace(".", "/") + ".olean")), node["source"]]
        require(old["command"] == command, "Historical compile command differs: " + name)
        if node["action"] == "compiled":
            compiled_count += 1
            require(node["command"] == command and node["exit_code"] == 0
                    and by_stage["compile-" + name]["command"] == command, "Fresh compile record differs")
        else:
            reuse_count += 1
            require(name not in expected_targets and node["previous_log"] == old["log"], "Owned target reused or wrong lineage")
            old_log = PurePosixPath(old["log"])
            require(old_log.is_relative_to(build / "runs"), "Reuse log escapes original build")
            log_body(old, "lineage/" + old_log.relative_to(build).as_posix())
        signatures[name] = digest_json({"input_key": key, "objects": objects})
    mirrors = report.get("external_cache_mirrors", {})
    require(mirrors == binding["external_cache_mirrors"]
            and set(mirrors) == set(report["planned_external_cache_mirrors"])
            and len(mirrors) == receipt["external_cache_mirror_count"], "Mirror membership/binding differs")
    mirror_facets = 0
    for name, record in mirrors.items():
        node = modules[name]
        require(node["kind"] in {"cached", "core"} and record["source_objects"] == node["objects"]
                and record["mirrored_objects"] == node["mirrored_objects"], "Mirror source/target record differs")
        cached = node["cached_object"]
        base = str(objdir / (name.replace(".", "/") + ".olean"))
        expected = {base + p[len(cached):]: digest for p, digest in record["source_objects"].items()}
        require(expected == record["mirrored_objects"], "Mirror changed an object or sidecar")
        object_record(base, expected)
        mirror_facets += len(expected)
    aliases = report.get("native_research_aliases", [])
    require(aliases == binding["native_research_aliases"], "Native alias binding differs")
    for index, alias in enumerate(aliases):
        name = "native-aliases/" + str(index) + "/source.lean"
        require(files[name]["path"] == alias["source"] and file_sha(member(name)) == alias["sha256"]
                and snapshots.get(alias["source"]) == alias["sha256"] and alias["tracked_matches"],
                "Native alias source binding differs")
        for match in alias["tracked_matches"]:
            rel = safe_relative(match["path"])
            name = "native-aliases/" + str(index) + "/tracked/" + rel.as_posix()
            expected_path = str(package_roots["goldbach"] / rel)
            require(files[name]["path"] == expected_path and file_sha(member(name)) == alias["sha256"]
                    and snapshots.get(expected_path) == alias["sha256"], "Tracked native alias differs")
    require({s["name"] for s in stages if s["name"].startswith("replay-")} ==
            {"replay-" + name for name in expected_targets}, "Kernel replay owner set differs")
    owned_details = []
    for name in expected_targets:
        node = modules[name]
        rel = name.replace(".", "/") + ".lean"
        base = str(objdir / (name.replace(".", "/") + ".olean"))
        command = [compiler["path"], "-t0", "-j1", "-R", str(remote), "-DwarningAsError=true",
                   "-o", base, str(remote / rel)]
        require(node["package"] == "project" and node["action"] == "compiled" and node["strict"] is True
                and node["exit_code"] == 0 and node["command"] == command
                and by_stage["compile-" + name]["command"] == command, "Owned strict fresh command differs")
        source = member("source/" + rel)
        require(source.read_bytes() == blobs[rel] and file_sha(source) == node["source_sha256"]
                == receipt["source_sha256"][name] and files["source/" + rel]["path"] == node["source"],
                "Owned source bytes or path differ")
        require(receipt["objects_sha256"][name] == node["objects"], "Receipt owned object set differs")
        for path, digest in node["objects"].items():
            objname = "objects/" + PurePosixPath(path).relative_to(objdir).as_posix()
            require(files[objname]["path"] == path and file_sha(member(objname)) == digest, "Owned object payload differs")
        replay = by_stage["replay-" + name]
        require(replay["command"] == [checker, "--verbose", name]
                and "replaying " + name in bodies[replay["name"]].splitlines(), "Exact bundled kernel replay absent")
        owned_details.append({"module": name, "source_sha256": node["source_sha256"],
                              "object_facets": len(node["objects"]), "strict_compile_exit": 0, "kernel_replay_exit": 0})
    audit = member("run/P36OwnedAudit.lean")
    expected_audit = helper.render_audit(tuple(expected_targets)).encode()
    require(audit.read_bytes() == expected_audit
            and files["run/P36OwnedAudit.lean"]["path"] == str(run / "P36OwnedAudit.lean")
            and snapshots[str(run / "P36OwnedAudit.lean")] == sha(expected_audit), "Original audit bytes differ")
    require(stages[-1]["name"] == "owned-inventory-audit" and stages[-1]["command"] ==
            [compiler["path"], "-t0", "-j1", "-DwarningAsError=true", "-R", str(run), str(run / "P36OwnedAudit.lean")],
            "Complete final audit command differs")
    records, counts = helper.baseline.validate_inventory(bodies["owned-inventory-audit"], modules=tuple(expected_targets))
    require(records == json.loads(member("run/declarations.json").read_bytes())
            and report["declarations_file"] == str(run / "declarations.json")
            and report["declaration_count"] == receipt["complete_owned_declaration_count"]
            == profile["declaration_count"] == len(records)
            and report["module_counts"] == receipt["module_counts"] == counts,
            "Saved full declaration inventory differs")
    require([c["module"] for c in counts] == expected_targets
            and [c["count"] for c in counts] == profile["expected_module_counts"], "Pinned owner counts differ")
    require(all("⋯" not in r["type"] for r in records), "Truncated pretty-printed declaration type")
    kinds = {name: dict(Counter(r["kind"] for r in records if r["module"] == name)) for name in expected_targets}
    require(kinds == receipt["module_declaration_kinds"], "Declaration kind summary differs")
    observed_axioms = sorted({a for r in records for a in r["axioms"]})
    require(set(observed_axioms) <= ALLOWED, "Unapproved transitive axiom")
    prior = binding.get("prior_owner_sources_preserved_without_new_credit", {})
    require(not set(prior) & set(expected_targets), "Earlier owners were granted duplicate credit")
    for name, digest in prior.items():
        require(initial_rel[name.replace(".", "/") + ".lean"] == digest, "Prior owner bytes changed")
    # Seal the very buffers that will be installed; do not reread unbound bytes.
    install_receipt, install_archive = receipt_path.read_bytes(), archive.read_bytes()
    require(install_receipt == receipt_bytes and sha(install_receipt) == profile["receipt_sha256"]
            and install_archive == archive_bytes and len(install_archive) == profile["archive_bytes"]
            and sha(install_archive) == profile["archive_sha256"], "Verified evidence changed before installation")
    require(profile_path.read_bytes() == profile_bytes and file_sha(Path(__file__)) == verifier_sha256,
            "Pinned profile or local verifier changed during verification")
    for rel, digest in initial_rel.items():
        require(file_sha(project / rel) == digest, "Current source/config changed before installation: " + rel)
    final = {
        "status": "PASS_COMPLETE_LOCAL_EVIDENCE_VERIFICATION",
        "verified_utc": datetime.now(timezone.utc).isoformat(),
        "source_commit": profile["source_commit"], "source_tree": receipt["source_tree"],
        "original_task_id": profile["original_task_id"],
        "original_task_terminal": {"status": original_terminal["status"],
            "exit_code": original_terminal["exit_code"], "output_truncated": original_terminal["output_truncated"],
            "capture_sha256": file_sha(work / "ORIGINAL_TASK_TERMINAL.json")},
        "local_verifier_sha256": verifier_sha256, "pinned_profile_sha256": sha(profile_bytes),
        "receipt": {"bytes": len(install_receipt), "sha256": profile["receipt_sha256"]},
        "archive": {"bytes": len(install_archive), "sha256": profile["archive_sha256"],
                    "regular_payload_files": len(files), "all_member_hashes_and_sizes_verified": True},
        "transport": {"export_count": len(transport["exports"]),
                      "page_count": sum(e["page_count"] for e in transport["exports"]),
                      "all_export_tasks_succeeded_exit_zero_untruncated": True,
                      "transport_verification_sha256": file_sha(work / "TRANSPORT_VERIFICATION.json")},
        "owned_module_count": len(expected_targets), "owned_declaration_count": len(records),
        "module_counts": counts, "module_declaration_kinds": kinds,
        "declaration_kind_totals": dict(Counter(r["kind"] for r in records)),
        "observed_transitive_axioms": observed_axioms, "allowed_transitive_axioms": sorted(ALLOWED),
        "complete_serialized_owner_inventory_and_full_types_verified": True,
        "owned_modules": owned_details,
        "original_execution": {"runner_sha256": receipt["runner_sha256"],
            "runner_report_sha256": receipt["runner_report_sha256"],
            "runner_run": receipt["runner_run"], "all_command_stages_exit_zero": len(stages),
            "fresh_strict_owned_compilations": len(expected_targets),
            "bundled_kernel_replays": len(expected_targets), "complete_owned_audit_exit": 0,
            "original_audit_sha256": sha(expected_audit), "original_audit_bytes": len(expected_audit)},
        "identity": {"source_manifest_sha256": profile["source_manifest_sha256"],
            "selected_source_count": len(selections), "fixed_commit_and_current_project_files_verified": len(initial_rel),
            "all_owned_sources_match_current_repository": True,
            "binding_sha256": receipt["binding_sha256"], "recorded_snapshot_count": len(snapshots),
            "compiler": compiler, "checker_sha256": receipt["checker_sha256"],
            "dependency_pins": pins, "lean_path": lean_path,
            "graph_module_count": len(modules), "recursive_signatures_recomputed": len(signatures),
            "compiled_graph_modules": compiled_count, "reused_graph_modules": reuse_count,
            "external_cache_mirror_count": len(mirrors), "external_cache_mirror_facets": mirror_facets,
            "native_research_alias_count": len(aliases),
            "snapshot_boundary": "The archived binding preserves the original runner's immutable hash map. The original runner/wrapper checked it after compilation, after replay/audit, and around packaging. Local verification recomputes archived and current project payload hashes, graph signatures and mirror mappings; it does not reread later remote state or rehash unavailable dependency bytes.",
            "dependency_bytes_in_archive": receipt["dependency_bytes_in_archive"]},
        "scope": profile["mathematical_scope"],
        "local_lean_compilation_or_kernel_replay_performed": False,
        "new_remote_jobs_submitted": False, "whole_p36_closed": False
    }
    result = json.dumps(final, indent=2, ensure_ascii=False).encode() + b"\n"
    require(not (work / "LOCAL_VERIFICATION.json").is_symlink(), "Local result path is a symlink")
    (work / "LOCAL_VERIFICATION.json").write_bytes(result)
    if not args.check_only:
        destination.mkdir(parents=True, exist_ok=True)
        require(not destination.is_symlink(), "Acceptance destination is a symlink")
        preserve(destination / "RECEIPT.json", install_receipt)
        preserve(destination / "evidence.tar.xz", install_archive)
        require(not (destination / "LOCAL_VERIFICATION.json").is_symlink(), "Installed result path is a symlink")
        (destination / "LOCAL_VERIFICATION.json").write_bytes(result)
    print(json.dumps({"status": final["status"], "owners": len(expected_targets), "declarations": len(records),
                      "archive_members": len(files), "snapshots": len(snapshots), "graph_modules": len(modules),
                      "mirrors": len(mirrors), "module_counts": counts, "observed_axioms": observed_axioms,
                      "installed": not args.check_only, "local_verification_sha256": sha(result)}, ensure_ascii=False))

if __name__ == "__main__":
    main()

