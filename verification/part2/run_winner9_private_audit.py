#!/usr/bin/env python3
"""Replay compiled P2 modules and audit their complete owned declarations.

Run sequentially in the private verification worktree. Project source/object
closures are checked against schema-2 compilation records and frozen around
each process. Mathlib is the separately locked, pinned environment boundary.
The original audit template is reused verbatim apart from its target module.
Compilation, independent replay and declaration audit remain distinct receipts.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from run_winner9_private_checks import (
    CACHE_SCHEMA, LEAN, MATHLIB, PIN, closure_signature, digest, imports, json_digest,
)

LEANCHECKER = str(Path(LEAN).with_name("leanchecker"))
TEMPLATE = Path(__file__).with_name("winner9_private_audit_template.lean")
TEMPLATE_TARGET = "ImbalancedChen.P2Winner9FiniteMomentKernel"
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def write_json(path: Path, value: dict | list) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def project_nodes(root: Path, target: str) -> dict[str, dict]:
    nodes: dict[str, dict] = {}
    visiting: set[str] = set()

    def visit(name: str) -> None:
        require(name not in visiting, "Project import cycle: " + name)
        if name in nodes:
            return
        source = root / (name.replace(".", "/") + ".lean")
        require(source.is_file(), "Missing project source: " + str(source))
        visiting.add(name)
        deps = imports(source)
        for dep in deps:
            visit(dep)
        visiting.remove(name)
        nodes[name] = {"source": source, "deps": deps}

    visit(target)
    return nodes


def snapshot(root: Path, lib: Path, nodes: dict, toolchain: dict) -> dict:
    project = {}
    for name, node in nodes.items():
        source, obj = node["source"], lib / (name.replace(".", "/") + ".olean")
        project[name] = {
            "source": str(source.relative_to(root)), "source_sha256": digest(source) if source.is_file() else None,
            "object": str(obj), "object_sha256": digest(obj) if obj.is_file() else None,
        }
    return {"project": project, "toolchain": toolchain,
            "lean_binary_sha256": digest(Path(LEAN)), "leanchecker_sha256": digest(Path(LEANCHECKER)),
            "template_sha256": digest(TEMPLATE), "driver_sha256": digest(Path(__file__))}


def verify_compilation(records: dict, nodes: dict, frozen: dict) -> None:
    require(frozen["lean_binary_sha256"] == frozen["toolchain"]["lean_binary_sha256"],
            "Lean binary changed after environment verification")
    for name, node in nodes.items():
        record = records.get(name, {})
        actual = frozen["project"][name]
        require(record.get("cache_schema") == CACHE_SCHEMA and record.get("module") == name
                and record.get("exit_code") == 0 and record.get("toolchain") == frozen["toolchain"],
                "No valid schema-2 compilation record: " + name)
        require(record.get("source_sha256") == actual["source_sha256"]
                and actual["source_sha256"] is not None
                and record.get("object_sha256") == actual["object_sha256"]
                and actual["object_sha256"] is not None,
                "Source/object differs from compilation record: " + name)
        require(record.get("deps") == {dep: records[dep]["object_sha256"] for dep in node["deps"]}
                and record.get("dependency_signatures") == {
                    dep: records[dep]["closure_signature"] for dep in node["deps"]}
                and record.get("closure_signature") == closure_signature(record),
                "Compilation dependency binding mismatch: " + name)


def parse_audit(log: Path, target: str, project: set[str]) -> dict:
    inventories, import_lists, declarations = [], [], []
    for line in log.read_text().splitlines():
        for prefix, output in (("P0_QUEUE_IMPORTS ", import_lists),
                               ("P0_QUEUE_INVENTORY ", inventories),
                               ("P0_QUEUE_DECL ", declarations)):
            if line.startswith(prefix):
                output.append(json.loads(line[len(prefix):]))
                break
    require(len(import_lists) == 1 and isinstance(import_lists[0], list), "Missing/duplicate import inventory")
    actual_project = {name for name in import_lists[0] if name.startswith("ImbalancedChen.")}
    require(actual_project == project, "Loaded project modules differ from the frozen source closure")
    require(len(inventories) == 1 and inventories[0].get("module") == target,
            "Missing/duplicate/wrong target inventory")
    inventory = inventories[0]
    serialized, environment = inventory["serialized"], inventory["environment"]
    require(serialized and len(serialized) == len(set(serialized))
            and sorted(serialized) == sorted(environment), "Serialized/environment inventory mismatch")
    names = [record["name"] for record in declarations]
    require(len(names) == len(set(names)) and sorted(names) == sorted(serialized),
            "Declaration records do not exactly cover the owned inventory")
    for record in declarations:
        require(record.get("module") == target, "Declaration belongs to another module")
        require(all(record.get(flag) is False for flag in ("unsafe", "partial", "axiom")),
                "Unsafe/partial/axiom declaration: " + record["name"])
        require(isinstance(record.get("type"), str) and record["type"] and "⋯" not in record["type"],
                "Missing/truncated declaration type: " + record["name"])
        require(isinstance(record.get("axioms"), list) and set(record["axioms"]) <= AXIOMS,
                "Forbidden transitive axiom: " + record["name"])
    return {"inventory": inventory, "imports": import_lists[0], "declarations": declarations,
            "declaration_count": len(declarations),
            "axiom_counts": dict(sorted(Counter(ax for rec in declarations for ax in rec["axioms"]).items()))}


def run_process(command: list[str], log: Path, root: Path, env: dict) -> dict:
    started = datetime.now(timezone.utc).isoformat()
    start = time.monotonic()
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
    return {"command": command, "exit_code": result.returncode, "started_utc": started,
            "seconds": round(time.monotonic() - start, 3), "log": str(log.relative_to(root)),
            "log_sha256": digest(log)}


def artifacts_valid(root: Path, artifacts: dict) -> bool:
    return bool(artifacts) and all((root / path).is_file() and digest(root / path) == sha
                                   for path, sha in artifacts.items())


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--summary-name", default="summary.json",
                        help="JSON basename under the audit directory; use distinct names for disjoint workers")
    args = parser.parse_args()
    require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*\.json", args.summary_name) is not None,
            "Expected a safe JSON summary basename")
    targets = list(dict.fromkeys(args.modules))
    require(all(re.fullmatch(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9]*)+", name) for name in targets),
            "Expected explicit ImbalancedChen module names")
    root = Path.cwd()
    out = root / ".lake/p2-private"
    lib, audit_root = out / "lib", out / "audit"
    audit_root.mkdir(parents=True, exist_ok=True)
    pin = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip()
    require(pin == PIN, "Mathlib checkout differs from the locked pin")
    toolchain = {"lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
                 "lean_binary_sha256": digest(Path(LEAN)), "mathlib_commit": pin}
    template_bytes = TEMPLATE.read_bytes()
    template = template_bytes.decode()
    template_sha256 = hashlib.sha256(template_bytes).hexdigest()
    require(template.count(TEMPLATE_TARGET) == 2, "Unexpected target occurrences in the original audit template")
    env = dict(os.environ)
    env["LEAN_PATH"] = str(lib) + ":" + env.get("LEAN_PATH", "")
    results = {}
    for target in targets:
        directory = audit_root / target
        directory.mkdir(parents=True, exist_ok=True)
        latest = directory / "latest.json"
        previous = json.loads(latest.read_text()) if latest.exists() else {}
        receipt = {"schema": 1, "module": target, "accepted": False}
        attempt = directory / f"attempt-{len(list(directory.glob('attempt-*'))) + 1:03d}"
        try:
            records = json.loads((out / "records.json").read_text())
            nodes = project_nodes(root, target)
            before = snapshot(root, lib, nodes, toolchain)
            require(before["template_sha256"] == template_sha256, "Audit template changed after loading")
            verify_compilation(records, nodes, before)
            if (previous.get("accepted") is True and previous.get("input_snapshot") == before
                    and artifacts_valid(root, previous.get("artifacts", {}))):
                results[target] = {"accepted": True, "reused": True,
                                   "declarations": previous["audit"]["declaration_count"]}
                print("REUSE_AUDIT", target, previous["audit"]["declaration_count"], flush=True)
                continue
            attempt.mkdir()
            receipt.update({"input_snapshot": before, "input_sha256": json_digest(before),
                            "source_sha256": before["project"][target]["source_sha256"],
                            "object_sha256": before["project"][target]["object_sha256"],
                            "compile_closure_signature": records[target]["closure_signature"],
                            "compile_provenance": records[target].get("provenance", "private compilation")})
            replay_command = [LEANCHECKER, "--verbose", target]
            replay_binding = {key: before[key] for key in (
                "project", "toolchain", "lean_binary_sha256", "leanchecker_sha256")}
            old_replay = previous.get("replay", {})
            if (previous.get("replay_binding") == replay_binding and old_replay.get("exit_code") == 0
                    and old_replay.get("inputs_unchanged") is True and old_replay.get("command") == replay_command
                    and artifacts_valid(root, {old_replay["log"]: old_replay["log_sha256"]})):
                receipt["replay"] = dict(old_replay, reused=True)
            else:
                print("REPLAY", target, flush=True)
                receipt["replay"] = run_process(replay_command, attempt / "replay.log", root, env)
            receipt["replay_binding"] = replay_binding
            after_replay = snapshot(root, lib, nodes, toolchain)
            receipt["replay"]["inputs_unchanged"] = after_replay == before
            write_json(latest, receipt)
            require(receipt["replay"]["exit_code"] == 0, "Independent leanchecker replay failed")
            require(after_replay == before, "Source/object/toolchain changed during independent replay")
            source = attempt / "Audit.lean"
            source.write_text(template.replace(TEMPLATE_TARGET, target))
            audit_source_sha = digest(source)
            command = [LEAN, "-t0", "-j1", "-M6144", "-DwarningAsError=true",
                       "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", str(source.relative_to(root))]
            print("AUDIT", target, flush=True)
            receipt["audit"] = run_process(command, attempt / "audit.log", root, env)
            receipt["audit"].update({"source": str(source.relative_to(root)), "source_sha256": audit_source_sha})
            after_audit = snapshot(root, lib, nodes, toolchain)
            receipt["audit"]["inputs_unchanged"] = after_audit == before and digest(source) == audit_source_sha
            require(receipt["audit"]["exit_code"] == 0, "Owned-declaration audit failed")
            require(receipt["audit"]["inputs_unchanged"], "Source/object/audit template changed during audit")
            parsed = parse_audit(attempt / "audit.log", target, set(nodes))
            write_json(attempt / "declarations.json", parsed)
            (attempt / "types.txt").write_text("\n\n".join(
                record["name"] + "\n" + record["type"] for record in parsed["declarations"]) + "\n")
            receipt["audit"].update({key: parsed[key] for key in ("declaration_count", "axiom_counts")})
            paths = [root / receipt["replay"]["log"], attempt / "audit.log", source,
                     attempt / "declarations.json", attempt / "types.txt"]
            receipt["artifacts"] = {str(path.relative_to(root)): digest(path) for path in paths}
            receipt["accepted"] = True
            print("PASS_AUDIT", target, parsed["declaration_count"], flush=True)
        except (OSError, ValueError, KeyError, TypeError) as error:
            receipt["error"] = str(error)
            print("FAIL_AUDIT", target, str(error).splitlines()[0], flush=True)
        if attempt.exists():
            write_json(attempt / "receipt.json", receipt)
        write_json(latest, receipt)
        results[target] = {"accepted": receipt["accepted"], "reused": False,
                           "declarations": receipt.get("audit", {}).get("declaration_count", 0)}
    summary = {"modules": results, "accepted": sum(value["accepted"] for value in results.values()),
               "requested": len(targets), "all_accepted": all(value["accepted"] for value in results.values())}
    write_json(audit_root / args.summary_name, summary)
    print(json.dumps(summary, sort_keys=True), flush=True)
    return int(not summary["all_accepted"])


if __name__ == "__main__":
    raise SystemExit(main())
