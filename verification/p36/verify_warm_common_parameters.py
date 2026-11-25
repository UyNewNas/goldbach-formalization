#!/usr/bin/env python3
"""Run the unchanged P3.6 verifier for ten warm/common owners and preserve its evidence.

This wrapper does not replace any Runner method or generate a different Lean audit.
It uses the existing project/build/package paths, including native cache mirrors.
An accepted receipt is written only after the full original verification, identity
checks, and archive read-back succeed. Prior foundation/payer owners get no new credit.
"""
from __future__ import annotations

import argparse
from collections import Counter
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import threading

sys.dont_write_bytecode = True
RUNNER_SHA256 = "be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709"
TARGETS = tuple("ImbalancedChen." + name for name in (
    "P3OriginalU5WarmCapCodeStability", "P3OriginalU5WarmAdmissionView",
    "P3OriginalU5WarmWordWalls", "P3OriginalU5RoundedCountInsertion",
    "P3OriginalU5RoundedModulusCap", "P3OriginalU5RoundedBetaReserve",
    "P3OriginalU5WarmMixedWallCover", "P3OriginalU5WarmRoundingPayment",
    "P3OriginalU5RoundedUniformModulusCap", "P3OriginalU5RoundedCommonParameters"))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PRIOR_SOURCES = {
    "ImbalancedChen.P2RoundedFibreCore": "bb4447d5f16da43543f8352fd933a06130f032eef9b6f45b48983a5524111310",
    "ImbalancedChen.P3OriginalU5WarmMixedReusedCore": "dc003864e849c1b69af1095e8d0af11973adb108626b2eee87bbf36c248ca40c",
    "ImbalancedChen.P1ActualMovingAffineWallMass": "640ae129694dc9c2a653f3ff56221694788e28b5e08b1f826facb15b79fff5ad",
    "ImbalancedChen.P1ActualMovingCoordinateSlab": "fd7a5150e70d8afa176815b41ebac228a7311ff6cc570521192006014cdbc851",
    "ImbalancedChen.P1ActualMovingAffineSlab": "3f111bed14f63a4c4de105532bca89d183cc228f2e1b4cce7dcd94070b11790d",
    "ImbalancedChen.P3OriginalU5FixedWidthSlabReserve": "800530282915b32e1e57bd6f1a0f9a4185163ba99ee23332a79eb94d22cbbb8f",
    "ImbalancedChen.P2CanonicalWallFullResidualPayment": "2a226cc5ba32f14c8ca8eb04be6dd171f8655295394900b40291c74bb5ebebde",
    "ImbalancedChen.P3OriginalU5MovingWallPayment": "28b1032a2231d391b96f2bdfe644d6c7efd486e9ac5e062e8c7a4979066ea9e2",
}
CONFIG_FILES = (
    "lean-toolchain", "lake-manifest.json", "lakefile.toml",
    "verification/p36/compile_p36_local.py", "verification/p36/project_cache_reuse.py",
    "verification/p36/verify_warm_common_parameters.py",
    "verification/p36/test_verify_warm_common_parameters.py",
    "verification/verify_part3_continuation.py", "verification/verify_part3_distribution.py",
    "verification/Part3DistributionAudit.lean", "verification/verify_variable_envelope_boxes.py")
MANIFEST = "docs/part3-distribution/continuation-20261125-p36/SOURCE_SELECTION.json"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def write_json(path, value):
    path = Path(path)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temporary.replace(path)


def git(project, *arguments):
    return subprocess.check_output(["git", "--no-optional-locks", *arguments],
                                   cwd=project, stderr=subprocess.PIPE, text=True).strip()


def check_source_identity(project, source_commit):
    require(re.fullmatch(r"[0-9a-f]{40}", source_commit) is not None,
            "--source-commit must be a full commit hash")
    require(git(project, "rev-parse", "HEAD") == source_commit, "Project HEAD changed or differs")
    require(not git(project, "status", "--porcelain", "--untracked-files=no"),
            "Project tracked files are not clean")


def make_runner_args(args):
    project = args.project.resolve()
    return argparse.Namespace(
        modules=list(TARGETS), project=project,
        packages_dir=(args.packages_dir or project / ".lake/p36-packages").resolve(),
        toolchain_dir=args.toolchain_dir.resolve(),
        build_dir=(args.build_dir or project / ".lake/p36-six-core-build").resolve(),
        source_manifest=(args.source_manifest or project / MANIFEST).resolve(),
        build=True, preflight=False, strict_owned=True, verify_owned=True,
        reuse_verified_bundle=[], timeout=1800)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def object_paths(path):
    return {str(p) for suffix in ("", ".private", ".server")
            if (p := Path(str(path) + suffix)).is_file()}


def log_body(stage, run_dir):
    path = Path(stage["log"])
    require(path.parent == run_dir and path.name == stage["name"] + ".log",
            "Command log is outside its exact run/stage")
    require(sha256(path) == stage["log_sha256"], "Command log hash differs: " + stage["name"])
    header, body = path.read_text(errors="replace").split("\n", 1)
    require(header == "command=" + json.dumps(stage["command"]),
            "Command log header differs: " + stage["name"])
    return body


def validate_completed_run(runner, exit_code, validator, expected_audit):
    """Gate evidence publication; the original Runner has already done all Lean work."""
    report = runner.report
    require(exit_code == 0 and report.get("status") == "VERIFIED_OWNED"
            and report.get("strict_owned") is True and report.get("targets") == list(TARGETS)
            and not report.get("blockers"), "The exact ten-owner verification did not finish")
    stages = report["commands"]
    require(stages and all(s["exit_code"] == 0 for s in stages), "A recorded command failed")
    require(len({s["name"] for s in stages}) == len(stages), "Duplicated command stage")
    bodies = {s["name"]: log_body(s, runner.run_dir) for s in stages}
    compiler, checker = runner.toolchain / "bin/lean", runner.toolchain / "bin/leanchecker"
    require(report["compiler"]["path"] == str(compiler), "Compiler path differs")
    require({s["name"] for s in stages if s["name"].startswith("replay-")}
            == {"replay-" + name for name in TARGETS}, "Replay owner set differs")
    for name in TARGETS:
        record = report["modules"][name]
        require(record.get("action") == "compiled" and record.get("strict") is True
                and record.get("exit_code") == 0, "Owned target was not freshly strict-compiled: " + name)
        source = runner.project / (name.replace(".", "/") + ".lean")
        obj = runner.local_object(name)
        expected = [str(compiler), "-t0", "-j1", "-R", str(runner.project),
                    "-DwarningAsError=true", "-o", str(obj), str(source)]
        for prefix, command in (("compile-", expected),
                                ("replay-", [str(checker), "--verbose", name])):
            matching = [s for s in stages if s["name"] == prefix + name]
            require(len(matching) == 1 and matching[0]["command"] == command,
                    "Missing or different exact command: " + prefix + name)
        require(record["command"] == expected and record["source"] == str(source)
                and sha256(source) == record["source_sha256"], "Owned source/command differs: " + name)
        require(object_paths(obj) == set(record["objects"])
                and all(sha256(p) == digest for p, digest in record["objects"].items()),
                "Owned object/sidecar set differs: " + name)
        require("replaying " + name in bodies["replay-" + name].splitlines(),
                "Missing exact replay line: " + name)
    audit = runner.run_dir / "P36OwnedAudit.lean"
    matching = [s for s in stages if s["name"] == "owned-inventory-audit"]
    require(len(matching) == 1 and stages[-1] == matching[0] and matching[0]["command"] ==
            [str(compiler), "-t0", "-j1", "-DwarningAsError=true", "-R", str(runner.run_dir), str(audit)],
            "The original complete audit stage is missing or different")
    require(audit.read_bytes() == expected_audit, "Generated audit differs from original render_audit")
    require(set(validator.ALLOWED) == ALLOWED, "Original validator axiom allowlist differs")
    declarations, counts = validator.validate_inventory(bodies["owned-inventory-audit"], modules=TARGETS)
    declaration_file = runner.run_dir / "declarations.json"
    require(report["declarations_file"] == str(declaration_file)
            and json.loads(declaration_file.read_text()) == declarations
            and report["declaration_count"] == len(declarations) and report["module_counts"] == counts,
            "Saved complete inventory differs from the actual audit output")
    return declarations, counts


class EvidenceArchive:
    """A fixed file manifest; tar payloads are regular files and are read back."""
    def __init__(self):
        self.files = {}

    def add(self, name, path, expected=None):
        member = PurePosixPath(name)
        require(not member.is_absolute() and ".." not in member.parts
                and member.as_posix() == name and name not in ("", "."), "Unsafe archive name")
        path = Path(path)
        require(path.is_file(), "Missing evidence file: " + str(path))
        digest = sha256(path)
        require(expected is None or digest == expected, "Evidence hash differs: " + str(path))
        item = {"path": str(path), "sha256": digest, "bytes": path.stat().st_size}
        require(name not in self.files or self.files[name] == item, "Conflicting archive member: " + name)
        self.files[name] = item

    def check_inputs(self):
        for item in self.files.values():
            require(Path(item["path"]).stat().st_size == item["bytes"]
                    and sha256(item["path"]) == item["sha256"], "Archive input changed: " + item["path"])

    def write(self, archive):
        self.check_inputs()
        with tarfile.open(archive, "w:xz", preset=6) as tar:
            for name, item in sorted(self.files.items()):
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = item["bytes"], 0o644, 0
                with Path(item["path"]).open("rb") as source:
                    tar.addfile(info, source)
        self.check_inputs()
        verify_archive(archive, self.files)


def verify_archive(archive, files):
    with tarfile.open(archive, "r:xz") as tar:
        members = tar.getmembers()
        require(len(members) == len(files) and {m.name for m in members} == set(files),
                "Archive membership differs")
        for member in members:
            require(member.isfile() and not member.issparse() and member.size == files[member.name]["bytes"],
                    "Archive member is not the expected regular payload")
            digest = hashlib.sha256()
            with tar.extractfile(member) as source:
                for block in iter(lambda: source.read(1024 * 1024), b""):
                    digest.update(block)
            require(digest.hexdigest() == files[member.name]["sha256"], "Archive payload hash differs")


def publish_evidence(out, evidence, metadata, final_check):
    archive = out / "evidence.tar.xz"
    evidence.write(archive)
    final_check()
    evidence.check_inputs()
    receipt = {**metadata, "archive": str(archive), "archive_bytes": archive.stat().st_size,
               "archive_sha256": sha256(archive), "files": evidence.files, "finished_utc": now()}
    write_json(out / "RECEIPT.json", receipt)
    return receipt


def collect_evidence(runner, out, initial):
    evidence = EvidenceArchive()
    for path in sorted(runner.run_dir.iterdir()):
        if path.is_file():
            evidence.add("run/" + path.name, path)
    evidence.add("wrapper/runner-stdout.log", out / "runner-stdout.log")
    for relative in CONFIG_FILES:
        evidence.add("config/" + relative, runner.project / relative, initial[str(runner.project / relative)])
    manifest = runner.report["source_manifest"]
    evidence.add("SOURCE_SELECTION.json", manifest["path"], manifest["sha256"])
    for name in TARGETS:
        record = runner.report["modules"][name]
        evidence.add("source/" + name.replace(".", "/") + ".lean",
                     record["source"], record["source_sha256"])
        for path, digest in record["objects"].items():
            evidence.add("objects/" + Path(path).relative_to(runner.objdir).as_posix(), path, digest)
    evidence.add("lineage/local-state.json", runner.state_path)
    state = json.loads(runner.state_path.read_text())["modules"]
    require(state == runner.state["modules"], "Build state changed after verification")
    for name, node in runner.report["modules"].items():
        if node.get("action") != "reused":
            continue
        previous = state[name]
        require(previous.get("exit_code") == 0 and previous["input_key"] == node["input_key"]
                and previous["objects"] == node["objects"]
                and previous["source_sha256"] == node["source_sha256"], "Reuse lineage differs: " + name)
        log = Path(node["previous_log"])
        require(log.is_relative_to(runner.build / "runs") and str(log) == previous["log"],
                "Reuse log is outside the recorded build: " + name)
        log_body(previous, log.parent)
        evidence.add("lineage/" + log.relative_to(runner.build).as_posix(), log, previous["log_sha256"])
    for index, donor in enumerate(runner.report.get("transferred_verified_objects", [])):
        root = Path(donor["receipt"]).parent
        evidence.add(f"lineage/transferred-{index}/RECEIPT.json", donor["receipt"], donor["receipt_sha256"])
        for path, digest in donor["evidence_sha256"].items():
            require(Path(path).is_relative_to(root), "Transferred evidence escaped its bundle")
            evidence.add(f"lineage/transferred-{index}/" + Path(path).relative_to(root).as_posix(), path, digest)
    for index, alias in enumerate(runner.report.get("native_research_aliases", [])):
        evidence.add(f"native-aliases/{index}/source.lean", alias["source"], alias["sha256"])
        for match in alias["tracked_matches"]:
            path = runner.packages / "goldbach" / match["path"]
            require(path.resolve().is_relative_to((runner.packages / "goldbach").resolve()),
                    "Tracked native alias escaped its package")
            evidence.add(f"native-aliases/{index}/tracked/" + match["path"], path, alias["sha256"])
    return evidence


def check_after_run(runner, source_commit, initial):
    check_source_identity(runner.project, source_commit)
    for path, expected in initial.items():
        require(sha256(path) == expected, "Initial project source/config changed: " + path)
    for package, pin in runner.report["dependency_pins"].items():
        root = runner.packages / package
        require(git(root, "rev-parse", "HEAD") == pin, "Dependency HEAD changed: " + package)
        require(not git(root, "status", "--porcelain", "--untracked-files=no"),
                "Dependency tracked files changed: " + package)
    mirrors = runner.report.get("external_cache_mirrors", {})
    require(set(mirrors) == set(runner.report.get("planned_external_cache_mirrors", [])),
            "Planned and actual native cache mirrors differ")
    runner.assert_snapshots()
    for name, node in runner.graph.nodes.items():
        obj = runner.local_object(name) if node.kind == "build" else node.cached_object
        require(object_paths(obj) == set(runner.report["modules"][name]["objects"]),
                "Dependency object/sidecar set changed: " + name)


def heartbeat(runner, stop, output):
    while not stop.wait(45):
        logs = list(runner.run_dir.glob("*.log"))
        latest = max(logs, key=lambda p: p.stat().st_mtime_ns) if logs else None
        print("P36_WARM_COMMON_HEARTBEAT " + json.dumps({"utc": now(),
              "stage": latest.stem if latest else "preparing",
              "log_bytes": latest.stat().st_size if latest else 0}), file=output, flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--project", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--packages-dir", type=Path)
    parser.add_argument("--toolchain-dir", type=Path, default=Path("/toolchains"))
    parser.add_argument("--build-dir", type=Path)
    parser.add_argument("--source-manifest", type=Path)
    args = parser.parse_args(argv)
    runner_args = make_runner_args(args)
    project = runner_args.project
    out = project / ".lake/p36-warm-common-verification" / datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out.mkdir(parents=True, exist_ok=False)
    wrapper_report = {"status": "PREPARING_NOT_ACCEPTED", "source_commit": args.source_commit,
                      "targets": list(TARGETS), "started_utc": now(), "p36_closed": False}
    runner = None
    try:
        check_source_identity(project, args.source_commit)
        require(Path(__file__).resolve() == project / "verification/p36/verify_warm_common_parameters.py",
                "Wrapper must be the committed project file")
        require(not set(TARGETS) & set(PRIOR_SOURCES), "Prior owners cannot get new acceptance credit")
        initial = {str(project / name): sha256(project / name) for name in CONFIG_FILES}
        require(initial[str(project / "verification/p36/compile_p36_local.py")] == RUNNER_SHA256,
                "The pinned original Runner differs")
        manifest = runner_args.source_manifest
        require(manifest.is_relative_to(project), "Source manifest must belong to the project")
        initial[str(manifest)] = sha256(manifest)
        entries = json.loads(manifest.read_text())["sources"]
        require(len({entry["module"] for entry in entries}) == len(entries), "Duplicate selected module")
        require(set(TARGETS) <= {entry["module"] for entry in entries}, "An owned source is not selected")
        for entry in entries:
            relative = entry["module"].replace(".", "/") + ".lean"
            require(relative == entry["selected_path"], "Invalid selected source path")
            initial[str(project / relative)] = entry["selected_sha256"]
        for name, digest in PRIOR_SOURCES.items():
            path = str(project / (name.replace(".", "/") + ".lean"))
            require(path not in initial or initial[path] == digest, "Prior owner selected hash changed")
            initial[path] = digest
        for path, digest in initial.items():
            require(sha256(path) == digest, "Initial source binding differs: " + path)
        git(project, "ls-files", "--error-unmatch", "--", *(str(Path(p).relative_to(project)) for p in initial))
        source_tree = git(project, "rev-parse", "HEAD^{tree}")
        sys.path.insert(0, str(project / "verification/p36"))
        sys.path.insert(0, str(project / "verification"))
        module = load_module("p36_warm_common_original_runner", project / "verification/p36/compile_p36_local.py")
        helper = load_module("p36_warm_common_original_helper", project / "verification/verify_part3_continuation.py")
        require(Path(helper.baseline.__file__).resolve() == project / "verification/verify_part3_distribution.py",
                "Validator resolved outside this project")
        runner = module.Runner(runner_args)
        wrapper_report.update(status="RUNNING_NOT_ACCEPTED", runner_report=str(runner.report_path))
        write_json(out / "wrapper-report.json", wrapper_report)
        print("P36_WARM_COMMON_START " + json.dumps({"path": str(out), "source_commit": args.source_commit,
              "owned_modules": len(TARGETS), "runner_report": str(runner.report_path)}), flush=True)
        stop = threading.Event()
        monitor = threading.Thread(target=heartbeat, args=(runner, stop, sys.stdout), daemon=True)
        with (out / "runner-stdout.log").open("w") as output, redirect_stdout(output), redirect_stderr(output):
            monitor.start()
            try:
                code = runner.execute()
            finally:
                stop.set()
                monitor.join(timeout=5)
        declarations, counts = validate_completed_run(runner, code, helper.baseline,
                                                       helper.render_audit(TARGETS).encode())
        require(json.loads(runner.report_path.read_text()) == runner.report, "Saved runner report differs")
        check_after_run(runner, args.source_commit, initial)
        evidence = collect_evidence(runner, out, initial)
        binding = {"source_commit": args.source_commit, "source_tree": source_tree,
                   "runner_sha256": RUNNER_SHA256, "snapshot_sha256": dict(runner.snapshots),
                   "initial_project_sha256": initial, "lean_path": runner.report["lean_path"],
                   "dependency_pins": runner.report["dependency_pins"],
                   "external_cache_mirrors": runner.report.get("external_cache_mirrors", {}),
                   "native_research_aliases": runner.report.get("native_research_aliases", []),
                   "prior_owner_sources_preserved_without_new_credit": PRIOR_SOURCES,
                   "checked_after_original_verification_utc": now()}
        write_json(out / "binding.json", binding)
        evidence.add("binding.json", out / "binding.json")
        receipt = {
            "status": "VERIFIED_OWNED", "scope": "Exactly ten warm/common owned modules; not whole P3.6",
            "source_commit": args.source_commit, "source_tree": source_tree, "targets": list(TARGETS),
            "p36_closed": False, "started_utc": wrapper_report["started_utc"],
            "runner_run": str(runner.run_dir), "runner_sha256": RUNNER_SHA256,
            "runner_report_sha256": sha256(runner.report_path), "binding_sha256": sha256(out / "binding.json"),
            "snapshot_count": len(runner.snapshots), "compiler": runner.report["compiler"],
            "checker_sha256": runner.snapshots[str(runner.toolchain / "bin/leanchecker")],
            "dependency_pins": runner.report["dependency_pins"], "lean_path": runner.report["lean_path"],
            "strict_compilation": True, "bundled_kernel_replay": True, "complete_transitive_axiom_audit": True,
            "fresh_target_compilation_this_task": True, "kernel_replay_this_task": True,
            "complete_owned_declaration_count": len(declarations), "module_counts": counts,
            "module_declaration_kinds": {name: dict(Counter(r["kind"] for r in declarations
                                                            if r["module"] == name)) for name in TARGETS},
            "allowed_transitive_axioms": sorted(ALLOWED),
            "source_sha256": {name: runner.report["modules"][name]["source_sha256"] for name in TARGETS},
            "objects_sha256": {name: runner.report["modules"][name]["objects"] for name in TARGETS},
            "source_manifest": runner.report["source_manifest"],
            "external_cache_mirror_count": len(binding["external_cache_mirrors"]),
            "dependency_bytes_in_archive": "Owned object bytes and recorded lineage are included; all other dependency bytes are hash-bound by the original runner snapshots.",
        }
        def final_check():
            check_after_run(runner, args.source_commit, initial)
            validate_completed_run(runner, code, helper.baseline, helper.render_audit(TARGETS).encode())
            require(json.loads(runner.report_path.read_text()) == runner.report,
                    "Saved runner report changed during packaging")

        final = publish_evidence(out, evidence, receipt, final_check)
        wrapper_report.update(status="VERIFIED_OWNED", finished_utc=final["finished_utc"],
                              receipt=str(out / "RECEIPT.json"), archive_sha256=final["archive_sha256"])
        write_json(out / "wrapper-report.json", wrapper_report)
        print("P36_WARM_COMMON_VERIFIED " + json.dumps({"path": str(out),
              "source_commit": args.source_commit, "owned_modules": len(TARGETS),
              "declarations": len(declarations), "archive_bytes": final["archive_bytes"],
              "archive_sha256": final["archive_sha256"], "receipt_sha256": sha256(out / "RECEIPT.json")}), flush=True)
        return 0
    except Exception as error:
        (out / "RECEIPT.json").unlink(missing_ok=True)
        (out / "RECEIPT.json.tmp").unlink(missing_ok=True)
        if runner is not None and runner.report_path.is_file():
            shutil.copyfile(runner.report_path, out / "runner-report.json")
        wrapper_report.update(status="FAILED_NOT_ACCEPTED", finished_utc=now(), error=str(error))
        write_json(out / "wrapper-report.json", wrapper_report)
        print("P36_WARM_COMMON_FAILED " + json.dumps({"path": str(out),
              "runner_report": str(runner.report_path) if runner is not None else None,
              "error": str(error)[-2000:]}), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
