#!/usr/bin/env python3
"""Cross-check recovered declaration inventories and compiler terminal captures."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile

ADMISSION = Path(__file__).resolve().parents[1]
CONTINUATION = ADMISSION.parent
REPOSITORY = Path(__file__).resolve().parents[5]
BASELINE = "b3f306cc3b430fc40c3b3ec4110d323443d2f609"
OWNERS = tuple("ImbalancedChen." + stem for stem in (
    "P5OriginalU5NativeRootCover", "P3OriginalU5FreshFifthSquareSupplier",
    "P3OriginalU5AllSourceSquares", "P3OriginalU5AllSignedSquares",
    "P3OriginalU5RootVInputs", "P3OriginalU5CoarseRootV",
    "P3OriginalU5RoughEndpoints", "P3OriginalU5FullWLayer",
))
OLD_GROUPS = {
    "foundations": (6, 140), "payer": (2, 26), "warm-common": (10, 137), "classical-six": (6, 85),
    "rounded-pair-density": (1, 5), "normalized-row": (1, 11), "pair-normalized": (1, 10),
}
KINDS = {"theorem", "definition", "opaque", "quotient", "inductive", "constructor", "recursor"}
AXIOMS = {"Classical.choice", "Quot.sound", "propext"}
TOOL_DIGESTS = {
    "lean": "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    "leanchecker": "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
    "verification/p36/compile_p36_local.py": "be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709",
    "verification/verify_part3_continuation.py": "9afe49d061639c5d98926185b4e6301e3ff7222e35550839fbfe1a4c785bdcc8",
    "verification/verify_part3_distribution.py": "bef3b8ba73736d7a787aaf31fe49cb8017de4f8d7c71ee4220c6c3dbc47607f4",
    "verification/Part3DistributionAudit.lean": "45b20653d5510b9639a653913ba39fdc21d402f45342d6dd7d2c51439f01ed93",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def hash_file(path):
    with path.open("rb") as handle:
        digestor = sha256()
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digestor.update(block)
    return digestor.hexdigest()


def relative(path):
    return str(path.relative_to(REPOSITORY)) if path.is_relative_to(REPOSITORY) else str(path)


def git_blob(commit, path):
    return subprocess.check_output(["git", "--no-optional-locks", "show", commit + ":" + path],
                                   cwd=REPOSITORY)


def digest_names(records):
    return digest(json.dumps(sorted(records), ensure_ascii=False, separators=(",", ":")).encode())


def events(lines, prefix):
    return [(index, json.loads(line[len(prefix):])) for index, line in enumerate(lines, 1)
            if line.startswith(prefix)]


def archive_members(archive, receipt, wanted):
    require(hash_file(archive) == receipt["archive_sha256"] and archive.stat().st_size == receipt["archive_bytes"],
            "Archive bytes or SHA-256 differ: " + str(archive))
    found = {}
    with tarfile.open(archive, "r|xz") as source:
        for member in source:
            if member.name in wanted:
                require(member.isfile() and member.name not in found, "Repeated or nonregular member: " + member.name)
                data = source.extractfile(member).read()
                metadata = receipt["files"][member.name]
                expected = metadata["sha256"] if isinstance(metadata, dict) else metadata
                require(digest(data) == expected and (not isinstance(metadata, dict) or len(data) == metadata["bytes"]),
                        "Archive member SHA-256 or size differs: " + member.name)
                found[member.name] = data
    require(wanted == set(found), "Missing archived evidence members: " + repr(wanted - set(found)))
    return found


def inventory(directory, label, prefix, extra=()):
    archive = directory / "evidence.tar.xz"
    receipt_path = directory / "RECEIPT.json"
    receipt_raw = receipt_path.read_bytes()
    receipt = json.loads(receipt_raw)
    declaration_member = prefix + "declarations.json"
    audit_member = prefix + "owned-inventory-audit.log"
    payload = archive_members(archive, receipt, {declaration_member, audit_member, *extra})
    records = json.loads(payload[declaration_member])
    lines = payload[audit_member].decode().splitlines()
    require(records == [record for _, record in events(lines, "PART3_AUDIT_DECL ")],
            "Audit declarations and complete JSON inventory differ: " + label)
    counts = [record for _, record in events(lines, "PART3_AUDIT_MODULE ")]
    require(counts == receipt["module_counts"] and
            [int(line.removeprefix("PART3_AUDIT_COUNT ")) for line in lines if line.startswith("PART3_AUDIT_COUNT ")]
            == [len(records)], "Archived audit counts differ: " + label)
    names = [record["name"] for record in records]
    modules = receipt["targets"]
    by_module = Counter(record["module"] for record in records)
    require(len(names) == len(set(names)) and len(modules) == len(set(modules)) == len(counts)
            and set(by_module) == set(modules) and by_module == {c["module"]: c["count"] for c in counts}
            and receipt.get("complete_owned_declaration_count", receipt.get("declaration_count")) == len(records),
            "Declaration or defining-module totals/uniqueness differ: " + label)
    kinds_by_module = {module: Counter() for module in modules}
    for record in records:
        require(isinstance(record["name"], str) and bool(record["name"]) and record["kind"] in KINDS
                and isinstance(record["type"], str) and bool(record["type"]) and "⋯" not in record["type"]
                and isinstance(record["level_parameters"], list)
                and all(isinstance(p, str) for p in record["level_parameters"])
                and isinstance(record["axioms"], list) and set(record["axioms"]) <= AXIOMS,
                "Invalid declaration, full type or transitive axioms: " + record["name"])
        kinds_by_module[record["module"]][record["kind"]] += 1
    return {
        "label": label, "archive": relative(archive), "archive_sha256": receipt["archive_sha256"],
        "receipt_sha256": digest(receipt_raw), "inventory_member": declaration_member,
        "inventory_sha256": digest(payload[declaration_member]), "audit_log_member": audit_member,
        "audit_log_sha256": digest(payload[audit_member]), "audit_declarations_match_exactly": True,
        "owners": modules, "module_kinds": kinds_by_module, "declaration_count": len(records),
        "kinds": Counter(record["kind"] for record in records),
        "sorted_full_names_sha256": digest_names(names),
    }, receipt, records, payload


def check_baseline():
    groups, indexed, modules, sources = [], defaultdict(list), set(), {}
    for label, expected in OLD_GROUPS.items():
        folder = CONTINUATION if label in {"foundations", "payer", "warm-common", "classical-six"} \
            else CONTINUATION / "normalized-density"
        prefix = "continuation/" if label in {"foundations", "payer"} else "run/"
        directory = folder / ("accepted-" + label)
        group, receipt, records, _ = inventory(directory, label, prefix)
        require(group["receipt_sha256"] == digest(git_blob(BASELINE, relative(directory / "RECEIPT.json"))),
                "Old evidence receipt changed from the frozen baseline: " + label)
        require((len(group["owners"]), len(records)) == expected and not modules.intersection(group["owners"]),
                "Old group owners or total differ: " + label)
        for module in group["owners"]:
            path = module.replace(".", "/") + ".lean"
            data = (REPOSITORY / path).read_bytes()
            require(data == git_blob(BASELINE, path) and digest(data) == receipt["source_sha256"][module],
                    "Old owned source changed from baseline or receipt: " + module)
            sources[module] = digest(data)
        for record in records:
            indexed[record["name"]].append({"group": label, **record})
        groups.append(group)
        modules.update(group["owners"])
    require(len(modules) == 27 and len(indexed) == 414 and all(len(rows) == 1 for rows in indexed.values())
            and Counter(rows[0]["kind"] for rows in indexed.values()) == {"theorem": 317, "definition": 97},
            "Old 27-owner inventory differs from its 414-record baseline")
    return groups, indexed, modules, sources


def strict_stages(report, run, payload, line_by_name):
    compiler = PurePosixPath(report["compiler"]["path"])
    project = PurePosixPath(report["project"])
    objects = PurePosixPath(report["build_dir"]) / "lib/lean"
    stages = {}
    for module in OWNERS:
        source = module.replace(".", "/") + ".lean"
        node = report["modules"][module]
        require(node["package"] == "project" and node["action"] == "compiled"
                and node["strict"] is True and type(node["exit_code"]) is int and node["exit_code"] == 0,
                "Owner was not freshly compiled strictly: " + module)
        stages["compile-" + module] = [str(compiler), "-t0", "-j1", "-R", str(project), "-DwarningAsError=true",
                                       "-o", str(objects / (module.replace(".", "/") + ".olean")), str(project / source)]
    for module in OWNERS:
        stages["replay-" + module] = [str(compiler.with_name("leanchecker")), "--verbose", module]
    stages["owned-inventory-audit"] = [str(compiler), "-t0", "-j1", "-DwarningAsError=true", "-R", str(run),
                                       str(run / "P36OwnedAudit.lean")]
    owned = [stage for stage in report["commands"]
             if stage["name"] in stages or stage["name"].startswith("replay-") or "-DwarningAsError=true" in stage["command"]]
    require([stage["name"] for stage in owned] == list(stages) and report["commands"][-1] == owned[-1],
            "Original strict, replay and audit membership/order differs")
    checked = []
    for stage in owned:
        name = stage["name"]
        member = "run/" + name + ".log"
        data = payload[member]
        header, body = data.decode().split("\n", 1)
        require(stage["command"] == stages[name] and header.startswith("command=")
                and json.loads(header.removeprefix("command=")) == stages[name]
                and stage["log"] == str(run / (name + ".log")) and digest(data) == stage["log_sha256"]
                and type(stage["exit_code"]) is int and stage["exit_code"] == 0,
                "Original formal stage command, exit code or log SHA-256 differs: " + name)
        if name.startswith("compile-"):
            node = report["modules"][name.removeprefix("compile-")]
            require(all(node[key] == stage[key] for key in ("command", "exit_code", "log", "log_sha256")),
                    "Compiled node and original strict stage differ: " + name)
        if name.startswith("replay-"):
            require("replaying " + name.removeprefix("replay-") in body.splitlines(),
                    "Exact module replay marker absent: " + name)
        checked.append({**stage, "archive_member": member, "terminal_stdout_line": line_by_name[name]})
    return checked


def check_terminal(attempt, group, receipt, payload, metadata, manifest, binding_raw):
    stdout_path = ADMISSION / "attempts" / (attempt + "-task-stdout.log")
    terminal_path = ADMISSION / "attempts" / (attempt + "-terminal.json")
    terminal_raw = terminal_path.read_bytes()
    terminal = json.loads(terminal_raw)
    stdout = stdout_path.read_bytes()
    require(terminal["status"] == "succeeded" and type(terminal["exit_code"]) is int and terminal["exit_code"] == 0
            and terminal["output_truncated"] is False and len(stdout) == terminal["output_bytes"],
            "Original MCP terminal is not complete and successful")
    lines = stdout.decode().splitlines()
    before_events = events(lines, "P36_GROUP_RUNTIME_BEFORE ")
    binding_events = events(lines, "P36_GROUP_RUNTIME_BINDING ")
    require(len(before_events) == len(binding_events) == 1, "Missing or repeated group runtime markers")
    before_line, before = before_events[0]
    binding_line, binding_event = binding_events[0]
    require(before_line < binding_line, "Original group runtime markers are out of order")
    report_raw = payload["run/report.json"]
    report = json.loads(report_raw)
    report_sha = digest(report_raw)
    report_path = PurePosixPath(receipt["report_path"])
    run = report_path.parent
    tools = dict(TOOL_DIGESTS)
    compiler = PurePosixPath(report["compiler"]["path"])
    original_project = PurePosixPath(report["project"])
    runtime = {str(compiler): tools.pop("lean"), str(compiler.with_name("leanchecker")): tools.pop("leanchecker"),
               **{str(original_project / path): sha for path, sha in tools.items()}}
    commit = metadata["source_commit"]
    require(compiler.name == "lean" and report["compiler"]["sha256"] == runtime[str(compiler)]
            and report["runner_sha256"] == runtime[str(original_project / "verification/p36/compile_p36_local.py")],
            "Original compiler or runner digest differs")
    require(report_path.is_absolute() and report_path.name == "report.json"
            and run.parent == PurePosixPath(report["build_dir"]) / "runs"
            and report["targets"] == list(OWNERS) and report["strict_owned"] is True
            and report["status"] == "VERIFIED_OWNED" and report["blockers"] == []
            and report["source_manifest"] == manifest and report["finished_utc"]
            and report_sha == group["original_report_sha256"] == receipt["report_sha256"] == receipt["terminal_report_sha256"],
            "Original group report identity, strict scope, or manifest differs")
    expected_before = {"owners": list(OWNERS), "source_commit": commit, "source_manifest": manifest,
                       "runtime_tool_sha256_before": runtime}
    expected_binding = {**expected_before, "status": "VERIFIED_OWNED", "exit_code": 0,
                        "report": str(report_path), "report_sha256": report_sha, "runtime_tool_sha256_after": runtime}
    binding = json.loads(binding_raw)
    require(before == expected_before and binding == expected_binding
            and binding_event["binding"] == binding and type(binding["exit_code"]) is int
            and PurePosixPath(binding_event["path"]).is_absolute()
            and binding_event["sha256"] == digest(binding_raw) == group["runtime_binding_sha256"],
            "Independent original runtime-before/binding event or file SHA-256 differs")
    endings = events(lines, "P36_COMMAND_END ")
    formal = [(index, stage) for index, stage in endings if before_line < index < binding_line]
    require([stage for _, stage in formal] == report["commands"]
            and len({stage["name"] for _, stage in formal}) == len(formal)
            and all(PurePosixPath(stage["log"]).parent == run and type(stage["exit_code"]) is int
                    and stage["exit_code"] == 0 for _, stage in formal)
            and all(index < binding_line for index, _ in endings),
            "Formal MCP P36_COMMAND_END records differ from the original report")
    summaries = [json.JSONDecoder().raw_decode("\n".join(lines[index:binding_line - 1]))[0]
                 for index in range(before_line, binding_line - 1) if lines[index] == "{"]
    require(len(summaries) == 1 and summaries[0]["status"] == "VERIFIED_OWNED"
            and summaries[0]["report"] == str(report_path) and summaries[0]["blocker_count"] == 0,
            "Original formal stdout report summary differs")
    return {
        "attempt": attempt, "task_id": terminal["task_id"], "outer_task_status": terminal["status"],
        "outer_task_exit_code": 0, "stdout_path": relative(stdout_path), "stdout_bytes": len(stdout),
        "stdout_sha256": digest(stdout), "output_truncated": False,
        "terminal_path": relative(terminal_path), "terminal_sha256": digest(terminal_raw),
        "original_report_path": str(report_path), "original_report_sha256": report_sha,
        "original_report_status": report["status"], "source_manifest": manifest,
        "runtime_before_line": before_line, "runtime_binding_line": binding_line,
        "runtime_binding_path": binding_event["path"], "runtime_binding_sha256": digest(binding_raw),
        "original_runtime_before_and_after_sha256": runtime,
        "formal_command_end_records_matched_exactly": len(formal),
        "diagnostic_prefix_command_end_records_excluded": sum(index < before_line for index, _ in endings),
        "strict_compile_replay_and_audit": strict_stages(report, run, payload, {stage["name"]: i for i, stage in formal}),
    }, report


def check_new_group(directory, attempt):
    metadata = json.loads((ADMISSION / "attempts" / (attempt + "-source.json")).read_bytes())
    manifest_raw = (directory / "OWNER_MANIFEST.json").read_bytes()
    manifest_entries = json.loads(manifest_raw)["sources"]
    commit = metadata["source_commit"]
    require(metadata["attempt"] == int(attempt) and manifest_entries == metadata["sources"]
            and [entry["module"] for entry in manifest_entries] == list(OWNERS)
            and digest(manifest_raw) == metadata["owner_manifest_sha256"],
            "Recovered owner manifest differs from original frozen attempt")
    group_receipt_path = directory / "GROUP_RECEIPT.json"
    group_raw = group_receipt_path.read_bytes()
    group = json.loads(group_raw)
    binding_raw = (directory / "GROUP_RUNTIME_BINDING.json").read_bytes()
    owners = {entry["module"]: entry["selected_sha256"] for entry in manifest_entries}
    source_members = {"source/" + entry["selected_path"] for entry in manifest_entries}
    stage_members = {"run/" + action + "-" + module + ".log" for action in ("compile", "replay") for module in OWNERS}
    notes, receipt, records, payload = inventory(
        directory, "admission-w-layer", "run/", source_members | stage_members | {"run/report.json", "SOURCE_SELECTION.json"})
    manifest = {"path": receipt["files"]["SOURCE_SELECTION.json"]["path"], "sha256": digest(manifest_raw)}
    require(payload["SOURCE_SELECTION.json"] == manifest_raw and group["source_manifest"] == manifest
            and group["status"] == "VERIFIED_OWNED_GROUP_EXPORT" and group["whole_p36_closed"] is False
            and group["currentVerified"] is False and receipt["whole_p36_closed"] is False
            and group["source_commit"] == receipt["source_commit"] == commit
            and group["owners"] == notes["owners"] == list(OWNERS) and group["source_sha256"] == receipt["source_sha256"] == owners
            and group["base_receipt_sha256"] == notes["receipt_sha256"]
            and group["archive_sha256"] == notes["archive_sha256"] and group["archive_bytes"] == receipt["archive_bytes"],
            "Group receipt, base receipt, archive and frozen source metadata disagree")
    terminal, original = check_terminal(attempt, group, receipt, payload, metadata, manifest, binding_raw)
    require(original["declaration_count"] == len(records) and original["module_counts"] == receipt["module_counts"]
            and original["declarations_file"] == str(PurePosixPath(receipt["report_path"]).with_name("declarations.json")),
            "Report does not bind the complete audited inventory")
    notes.update(group_receipt_sha256=digest(group_raw), terminal_crosscheck=terminal, source_commit=commit)
    by_module = {module: [record for record in records if record["module"] == module] for module in OWNERS}
    scope = {}
    for entry in manifest_entries:
        module, path = entry["module"], entry["selected_path"]
        source = payload["source/" + path]
        require(path == module.replace(".", "/") + ".lean" and digest(source) == owners[module]
                and original["modules"][module]["source_sha256"] == owners[module]
                and (REPOSITORY / path).read_bytes() == source == git_blob(commit, path),
                "Original owner source differs from frozen bytes: " + module)
        scope[module] = {"source_sha256": owners[module], "declaration_records": len(by_module[module]),
                         "kinds": notes["module_kinds"][module]}
        if module != OWNERS[-1]:
            baseline = digest(git_blob(BASELINE, path))
            scope[module].update(source_scope="Existing source brought through the group gate",
                                 baseline_source_sha256=baseline, source_bytes_changed=baseline != owners[module])
            continue
        explicit = {module + "." + name: "definition" if kind == "def" else "theorem"
                    for kind, name in re.findall(r"(?m)^(theorem|def) ([A-Za-z0-9_']+)\b", source.decode())}
        indexed = {record["name"]: record for record in by_module[module]}
        require(Counter(explicit.values()) == {"theorem": 7, "definition": 1}
                and all(name in indexed and indexed[name]["kind"] == kind for name, kind in explicit.items()),
                "Full W-layer explicit mathematics does not match its audited inventory")
        auxiliary = [record for name, record in indexed.items() if name not in explicit]
        scope[module].update(source_scope="New W-layer source",
                             explicit_source_declarations=explicit,
                             remaining_inventory_declarations=[{"name": r["name"], "kind": r["kind"]} for r in auxiliary],
                             remaining_inventory_kinds=Counter(r["kind"] for r in auxiliary))
    notes["per_owner_scope"] = scope
    return notes, records


def crosscheck(directory, attempt):
    groups, indexed, modules, baseline_sources = check_baseline()
    new_group, records = check_new_group(directory, attempt)
    require(not modules.intersection(new_group["owners"]), "New group repeats a prior owned module")
    for record in records:
        indexed[record["name"]].append({"group": new_group["label"], **record})
    duplicates = {name: found for name, found in sorted(indexed.items()) if len(found) > 1}
    conflicts = {name: found for name, found in duplicates.items()
                 if len({(r["kind"], r["type"], tuple(r["level_parameters"])) for r in found}) > 1}
    comparable = {name: found for name, found in indexed.items() if name not in conflicts}
    return {
        "status": "FAIL_CONFLICTING_AUDITED_NAMES" if conflicts else "PASS_INDEPENDENT_INVENTORY_AND_TERMINAL_CROSSCHECK",
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Recovered inventories, archive member hashes and original terminal capture. Zero Lean or kernel runs.",
        "whole_p36_closed": False, "currentVerified": False,
        "baseline_commit": BASELINE, "baseline_owned_sources_unchanged": baseline_sources,
        "aggregate": {
            "archive_groups": len(groups) + 1, "owned_modules": len(modules) + len(new_group["owners"]),
            "baseline_unique_full_names": 414, "new_group_raw_records": len(records),
            "new_group_incremental_unique_full_names": len(indexed) - 414,
            "raw_declaration_records": 414 + len(records), "unique_full_names": len(indexed),
            "unique_nonconflicting_kinds": Counter(found[0]["kind"] for found in comparable.values()),
            "observed_transitive_axioms": sorted({axiom for found in indexed.values() for r in found for axiom in r["axioms"]}),
            "sorted_full_names_sha256": digest_names(indexed),
            "duplicate_full_names": duplicates, "conflicting_full_names": sorted(conflicts),
        },
        "groups": [*groups, new_group],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence-dir", required=True, type=Path)
    parser.add_argument("--attempt", required=True, help="Three-digit attempt basename under admission-w-layer/attempts")
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        require(re.fullmatch(r"\d{3}", args.attempt), "Expected a three-digit attempt basename")
        report = crosscheck(args.evidence_dir.resolve(strict=True), args.attempt)
        with args.output.open("x", encoding="utf-8") as handle:
            json.dump(report, handle, indent=2, ensure_ascii=False)
            handle.write("\n")
        print(json.dumps({"status": report["status"], "sha256": hash_file(args.output), "output": str(args.output)}))
        return int(report["status"].startswith("FAIL_"))
    except (OSError, RuntimeError, ValueError, TypeError, KeyError, AttributeError,
            subprocess.CalledProcessError) as error:
        parser.exit(1, "Crosscheck failed: " + str(error) + "\n")


if __name__ == "__main__":
    sys.exit(main())
