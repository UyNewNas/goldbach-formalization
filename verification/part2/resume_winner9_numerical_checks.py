#!/usr/bin/env python3
"""Resume one Winner9 block using immutable public checkpoints and original C/A/E.

This is a transport/orchestration layer, not another proof verifier. Every new
compile is immediately recoverable. Accepted receipts are validated by the
original relocatable exporter; partial replay uses the original auditor's exact
snapshot reuse. Historical receipts, commands and closure signatures are never
rewritten. Only a live compilation record's object locator may move.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
import import_winner9_ci_artifacts as I
import run_winner9_private_checks as C
import run_winner9_private_audit as A
import export_winner9_private_evidence as E

REPO = "UyNewNas/goldbach-formalization"
ROOT = Path.cwd().resolve()
W = ROOT / ".lake/p210-resume"
BOOT = ROOT / ".lake/p210-ci"
PRIVATE = ROOT / ".lake/p2-private"
LIB = PRIVATE / "lib"
REGISTRY = PRIVATE / "records.json"
PLAN = ROOT / "verification/part2/p210_resume_plan.json"
need = A.require


def read(path):
    return json.loads(Path(path).read_bytes())


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_bytes(E.encoded(value))
    temporary.replace(path)


def relative(path):
    return str(Path(path).relative_to(ROOT))


def without_locator(record):
    return {key: value for key, value in record.items() if key != "object"}


def producer():
    return {"run_id": os.environ["GITHUB_RUN_ID"], "run_attempt": int(os.environ["GITHUB_RUN_ATTEMPT"]),
            "commit": os.environ["GITHUB_SHA"]}


def api(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint]))


def output(**values):
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
            for key, value in values.items():
                stream.write(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n")


def slot_target(block, slot):
    wanted = I.targets(block)
    if slot == "check":
        return wanted[-1]
    need(re.fullmatch(r"(?:0?[0-9]|1[0-5])", slot or "") is not None, "Expected slot 0..15 or check")
    page = 16 * block + int(slot)
    return I.PREFIX + f"NumericalPage{page:04}" if page < 690 else None


def slot_dir(module):
    return W / "slots" / module


def plan():
    value = read(W / "resume-plan.json")
    need((W / "resume-plan.json").read_bytes() == PLAN.read_bytes(), "Published resume plan changed")
    return value


def check_drivers(value=None):
    value = value or plan()
    need(value["schema"] == 1 and value["source_commit"] == I.FIXED_BOOTSTRAP["commit"]
         and value["bootstrap"] == I.FIXED_BOOTSTRAP, "Wrong public bootstrap/source plan")
    for path, expected in I.DRIVER_HASHES.items():
        need(sha(path) == expected, "Original C/A/E driver changed: " + path)
    need(sha(I.__file__) == value["importer_sha256"], "Reviewed transport/importer changed")
    ids = [item["artifact_id"] for item in value["recovery_inputs"]]
    need(len(ids) == len(set(ids)), "Duplicate public recovery input")
    original_blocks = [item["block"] for item in value["recovery_inputs"]
                       if item["format"] == "block-recovery-v1" and item["run_id"] == value["bootstrap"]["run_id"]]
    need(sorted(original_blocks) == [f"{block:02}" for block in range(8, 44)],
         "The final inventory must include all 36 original block checkpoints, including empty ones")
    for item in value["recovery_inputs"]:
        need(re.fullmatch(r"(?:0[8-9]|[1-3][0-9]|4[0-3])", item["block"]) is not None
             and len(item["modules"]) == len(set(item["modules"]))
             and set(item["modules"]) <= set(I.targets(int(item["block"]))), "Recovery input exceeds its block")


def check_metadata(metadata, item):
    need(metadata["id"] == item["artifact_id"] and metadata["name"] == item["artifact_name"]
         and metadata["expired"] is False and metadata["size_in_bytes"] == item["zip_bytes"]
         and metadata["digest"] == "sha256:" + item["zip_sha256"]
         and str(metadata["workflow_run"]["id"]) == item["run_id"]
         and metadata["workflow_run"]["head_sha"] == item["commit"], "Public checkpoint metadata changed")


def completed_inputs(value):
    runs = {(item["run_id"], item["commit"]) for item in [value["bootstrap"], *value["recovery_inputs"]]}
    for run, commit in sorted(runs):
        result = api(f"repos/{REPO}/actions/runs/{run}")
        need(result["status"] == "completed" and result["head_sha"] == commit,
             "A source run is still active or changed; freeze its final successes before resuming: " + run)


def refuse_unplanned(block, value):
    allowed = {item["artifact_id"] for item in value["recovery_inputs"]}
    current = producer()
    pattern = re.compile(r"p210-resume-(?:compiled|progress)-" + f"{block:02}" + r"-(?:[0-9]{2}|check)-([0-9]+)-([0-9]+)$")
    complete = re.compile(r"p210-block-" + f"{block:02}" + r"-([0-9]+)-([0-9]+)$")
    page = 1
    while True:
        items = api(f"repos/{REPO}/actions/artifacts?per_page=100&page={page}")["artifacts"]
        for item in items:
            match = pattern.fullmatch(item["name"]) or complete.fullmatch(item["name"])
            if not item["expired"] and match and item["id"] not in allowed:
                need(match.group(1) == current["run_id"] and int(match.group(2)) == current["run_attempt"],
                     "Unplanned preserved work exists for this block; update the plan instead of rebuilding: " + str(item["id"]))
        if len(items) < 100:
            break
        page += 1


def download(item, destination):
    check_metadata(api(f"repos/{REPO}/actions/artifacts/{item['artifact_id']}"), item)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("xb") as stream:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{item['artifact_id']}/zip"], stdout=stream, check=True)
    need(destination.stat().st_size == item["zip_bytes"] and sha(destination) == item["zip_sha256"], "Public checkpoint ZIP bytes changed")


def bootstrap(block, supplied_plan):
    need(os.environ["GITHUB_REPOSITORY"] == REPO, "Unexpected repository")
    need(subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == producer()["commit"], "Checkout differs from this run")
    need(Path(supplied_plan).resolve() == PLAN, "Use the checked-in resume plan")
    value = read(PLAN)
    check_drivers(value)
    completed_inputs(value)
    refuse_unplanned(block, value)
    W.mkdir(parents=True, exist_ok=False)
    (W / "resume-plan.json").write_bytes(PLAN.read_bytes())
    write(W / "state.json", dict(producer(), block=f"{block:02}", plan_sha256=sha(PLAN),
          bootstrap_origin=value["bootstrap"], origins={}, old_numerical_rows_replayed=0,
          bootstrap_modules_recompiled=0, status="bootstrap-transport"))
    item = value["bootstrap"]
    download(item, W / "bootstrap.zip")
    files = I.unpack_zip(W / "bootstrap.zip", W / "bootstrap-zip")
    need(files == {"bootstrap.tar.gz": item["tar_sha256"]}, "Unexpected bootstrap ZIP inventory")
    stage = W / "bootstrap-input"
    files = I.unpack_tar(W / "bootstrap-zip/bootstrap.tar.gz", stage)
    seal_path = ".lake/p210-ci/bootstrap.json"
    need(files.get(seal_path) == item["manifest_sha256"], "Public bootstrap seal changed")
    sealed = read(stage / seal_path)
    need(files == dict(sealed["files"], **{seal_path: item["manifest_sha256"]})
         and sealed["commit"] == item["commit"] and sealed["run_id"] == item["run_id"]
         and int(sealed["run_attempt"]) == item["run_attempt"] and sealed["proof_credit"] == 0, "Invalid bootstrap inventory/provenance")
    for name, digest in files.items():
        need(name.startswith((".lake/p210-ci/", ".lake/p2-private/")), "Unexpected bootstrap installation path")
        I.no_destination(ROOT, name)
        I.exclusive_link_or_copy(stage / name, ROOT / name, digest)
    shutil.rmtree(stage)
    need(sha(REGISTRY) == sha(BOOT / "public-reference.json") == item["records_sha256"], "Bootstrap original registry changed")
    print("PUBLIC_BOOTSTRAP_RESTORED: no dependency or numerical compilation", flush=True)


def bootstrap_graph():
    common = I.nodes(ROOT, [I.PREFIX + "MaterializedLogChecker", I.PREFIX + "SeedArchiveChecks"])
    seeds = [I.PREFIX + f"CompleteSeedBlock{block:02}" for block in range(8, 44)]
    graph = I.nodes(ROOT, [*common, *seeds])
    need(len(common) == 57 and len(graph) == 93 and set(graph) == set(common) | set(seeds), "Unexpected historical closure")
    return graph


def resources():
    available = int(re.search(r"^MemAvailable:\s+(\d+)", Path("/proc/meminfo").read_text(), re.M)[1]) * 1024
    cg = Path("/sys/fs/cgroup")
    if (cg / "memory.max").is_file() and (cg / "memory.max").read_text().strip() != "max":
        available = min(available, int((cg / "memory.max").read_text()) - int((cg / "memory.current").read_text()))
    need(available >= 13 * 2**30, "Less than 13 GiB actually available for one -M11264 process")
    need(shutil.disk_usage(ROOT).free >= 2 * 2**30, "Insufficient space to preserve proof checkpoints")
    return {"available_bytes": available, "disk_free_bytes": shutil.disk_usage(ROOT).free,
            "workers": 1, "lean_threads": 1, "lean_memory_mib": 11264, "lean_memory_flag_applied": True}


def strict_record(module, record):
    memory = [limit for limit in (6144, 11264) if record.get("command") == I.strict_command(module, record, limit)]
    need(len(memory) == 1 and record.get("new_strict_compile") is True and record.get("exit_code") == 0
         and record.get("source") == module.replace(".", "/") + ".lean"
         and record["attempts"][-1]["command"] == record["command"] and record["attempts"][-1]["exit_code"] == 0,
         "Missing original strict compilation: " + module)
    checks = record["dependency_file_check"]
    need(checks["before_matches_records"] is True and checks["after_matches_records"] is True
         and checks["expected_sha256"] == checks["before_sha256"] == checks["after_sha256"], "Dependency files were not frozen")
    logs = {record["log"], *(attempt["log"] for attempt in record["attempts"])}
    need(all(re.fullmatch(re.escape(".lake/p2-private/logs/" + module) + r"\.attempt[1-9][0-9]*\.log", name) for name in logs), "Foreign compile log")
    return memory[0], logs


def unpack_origin(item):
    origin = W / "origins" / str(item["artifact_id"])
    download(item, origin / "source.zip")
    zipped = I.unpack_zip(origin / "source.zip", origin / "zip")
    old = item["format"] == "block-recovery-v1"
    tar_name = "p210-ci/recovery/new-objects-records-and-receipts.tar.gz" if old else "proof-and-original-evidence.tar.gz"
    info_name = "p210-ci/recovery/provenance.json" if old else "provenance.json"
    need(zipped.get(tar_name) == item["tar_sha256"] and info_name in zipped, "Missing exact recovery tar/provenance")
    info = read(origin / "zip" / info_name)
    if old or item["format"] == "slot-v1":
        need(info["block"] == item["block"] and all(str(info[key]) == str(item[key]) for key in ("commit", "run_id", "run_attempt")), "Wrong recovery producer/block")
        need((info.get("bootstrap_sha256") if old else info["bootstrap_origin"]["tar_sha256"]) == plan()["bootstrap"]["tar_sha256"], "Wrong recovery bootstrap")
    else:
        need(item["format"] == "page-probe-v1" and info["producer_commit"] == item["commit"]
             and str(info["producer_run_id"]) == item["run_id"] and int(info["producer_attempt"]) == item["run_attempt"]
             and info["target"] in item["modules"] and info["bootstrap_tar_sha256"] == plan()["bootstrap"]["tar_sha256"]
             and info["bootstrap_zip_sha256"] == plan()["bootstrap"]["zip_sha256"], "Wrong page-probe producer")
    if not old:
        need(info["archive_sha256"] == item["tar_sha256"], "Recovery tar is not bound to its provenance")
    raw = origin / "raw"
    files = I.unpack_tar(origin / "zip" / tar_name, raw)
    expected = dict(info["files"])
    if old:
        expected[".lake/p210-ci/recovery/provenance.json"] = zipped[info_name]
    need(files == expected, "Recovery raw inventory differs from original provenance")
    registry_raw, _ = I.original_registry(origin / "source.zip", item)
    need((raw / ".lake/p2-private/records.json").read_bytes() == registry_raw, "Conflicting original registry bytes")
    (origin / "records.json").write_bytes(registry_raw)
    return {"item": item, "info": info, "raw": raw, "files": files, "records": json.loads(registry_raw)}


def install_origin_file(value, name):
    need(name in value["files"], "Checkpoint omits required file: " + name)
    I.no_destination(ROOT, name)
    I.exclusive_link_or_copy(value["raw"] / name, ROOT / name, value["files"][name])


def original_compile_origin(value, module, memory):
    item = value["item"]
    result = {key: item[key] for key in ("run_id", "run_attempt", "commit", "artifact_id")}
    result.update(records_path=relative(W / "origins" / str(item["artifact_id"]) / "records.json"),
                  records_sha256=sha(W / "origins" / str(item["artifact_id"]) / "records.json"), memory_mb=memory, reused=True)
    if item["format"] == "slot-v1" and value["info"]["compile_origin"]["artifact_id"] is not None:
        original = value["info"]["compile_origin"]
        need(any(entry["artifact_id"] == original["artifact_id"] and module in entry["modules"] for entry in plan()["recovery_inputs"]),
             "Resume plan omitted the first compilation producer")
        result = dict(original, reused=True)
    return result


def validate_receipt(module, receipt, records):
    evidence = E.Evidence()
    checked = E.validate_receipt(ROOT, module, receipt, records, evidence, {sha(A.__file__): Path(A.__file__)})
    evidence.verify_frozen()
    return checked


def replay_reusable(module, receipt, frozen):
    replay = receipt.get("replay", {})
    return (receipt.get("replay_binding") == A.replay_context(frozen)
            and replay.get("exit_code") == 0 and replay.get("inputs_unchanged") is True
            and replay.get("command") == [A.LEANCHECKER, "--verbose", module]
            and isinstance(replay.get("log"), str) and isinstance(replay.get("log_sha256"), str)
            and A.artifacts_valid(ROOT, {replay["log"]: replay["log_sha256"]}))


def restore(block):
    value = plan()
    check_drivers(value)
    completed_inputs(value)
    refuse_unplanned(block, value)
    need(read(W / "state.json")["block"] == f"{block:02}", "Wrong block bootstrap")
    need(sha(C.LEAN) == I.LEAN_SHA and sha(A.LEANCHECKER) == I.CHECKER_SHA, "Lean/checker binary changed")
    toolchain = {"lean_version": subprocess.check_output([C.LEAN, "--version"], text=True).strip(),
                 "lean_binary_sha256": sha(C.LEAN),
                 "mathlib_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=C.MATHLIB, text=True).strip()}
    old_plan, sealed, reference = read(BOOT / "plan.json"), read(BOOT / "bootstrap.json"), read(BOOT / "public-reference.json")
    need(sha(BOOT / "bootstrap.json") == value["bootstrap"]["manifest_sha256"]
         and sha(REGISTRY) == value["bootstrap"]["records_sha256"]
         and REGISTRY.read_bytes() == (BOOT / "public-reference.json").read_bytes(), "Initial 93 registry bytes changed")
    need(toolchain["mathlib_commit"] == C.PIN and old_plan["toolchain"] == toolchain
         and old_plan["commit"] == value["bootstrap"]["commit"] and old_plan["run_id"] == value["bootstrap"]["run_id"], "Bootstrap toolchain/producer changed")
    graph = bootstrap_graph()
    need(set(reference) == set(graph) == set(old_plan["modules"]) == set(sealed["modules"]), "Incomplete 93-module reuse")
    frozen = A.snapshot(ROOT, LIB, graph, toolchain)
    A.verify_compilation(reference, graph, frozen)
    I.unchanged({ROOT / name: digest for name, digest in sealed["files"].items()})
    wanted = I.targets(block)
    sources = {}
    for module in wanted:
        path = ROOT / (module.replace(".", "/") + ".lean")
        original = subprocess.check_output(["git", "show", value["source_commit"] + ":" + relative(path)])
        need(path.is_file() and not path.is_symlink() and path.read_bytes() == original,
             "Numerical source changed since the original run: " + module)
        sources[relative(path)] = sha(path)
        need(not (LIB / (module.replace(".", "/") + ".olean")).exists(), "Unexpected local numerical object; qualify before reuse")
    need(set(I.nodes(ROOT, wanted)) - set(graph) == set(wanted), "Block would require unplanned project compilation")
    baseline_lib = Path(os.environ["P210_BASELINE"]) / ".lake/build/lib/lean"
    need(not any(path.is_file() and not (LIB / path.relative_to(baseline_lib)).exists() for path in baseline_lib.rglob("*")),
         "Original C would copy unplanned baseline objects")
    write(W / "resources.json", resources())
    candidates, origins, entries = {}, {}, []
    for item in value["recovery_inputs"]:
        if item["block"] != f"{block:02}":
            continue
        entry = unpack_origin(item); entries.append(entry)
        for name, before in reference.items():
            need(name in entry["records"] and without_locator(entry["records"][name]) == without_locator(before), "Original recovery changed a historical dependency record")
        successful = {name for name in wanted if entry["records"].get(name, {}).get("exit_code") == 0
                      and entry["records"][name].get("new_strict_compile") is True}
        need(set(item["modules"]) <= successful, "Planned compilation never succeeded")
        if item["format"] == "block-recovery-v1":
            need(set(item["modules"]) == successful, "Plan omitted an original successful compilation")
        for module in item["modules"]:
            candidates.setdefault(module, []).append(entry)
        key = str(item["artifact_id"])
        origins[key] = dict(item, zip_path=relative(W / "origins" / key / "source.zip"), records_path=relative(W / "origins" / key / "records.json"))
    records, selected = dict(reference), {}
    for module, choices in candidates.items():
        need(all(without_locator(entry["records"][module]) == without_locator(choices[0]["records"][module]) for entry in choices), "Conflicting successful compilations; do not choose silently")
        def advanced(entry):
            directory = entry["raw"] / ".lake/p2-private/audit" / module
            receipts = [read(path) for path in [directory / "latest.json", *directory.glob("attempt-*/receipt.json")] if path.is_file()]
            return (any(r.get("accepted") is True for r in receipts), any(r.get("replay", {}).get("exit_code") == 0 for r in receipts))
        entry = max(choices, key=advanced)
        record = entry["records"][module]
        memory, logs = strict_record(module, record)
        stem = ".lake/p2-private/lib/" + module.replace(".", "/")
        need(entry["files"].get(stem + ".olean") == record["object_sha256"], "Successful object missing from checkpoint")
        for name in sorted({stem + suffix for suffix in I.FACETS if stem + suffix in entry["files"]} | logs):
            install_origin_file(entry, name)
        for name in sorted(entry["files"]):
            if name.startswith(".lake/p2-private/audit/" + module + "/"):
                install_origin_file(entry, name)
        records[module] = dict(record, object=str(LIB / (module.replace(".", "/") + ".olean")))
        selected[module] = entry
        directory = slot_dir(module); directory.mkdir(parents=True, exist_ok=False)
        write(directory / "state.json", {"module": module, "phases": [], "accepted": False,
              "gates": dict(I.GATES, stock_leanchecker=False, owned_declarations_and_axioms=False),
              "compile_origin": original_compile_origin(entry, module, memory), "audit_origin": None})
    write(REGISTRY, records)
    for module, entry in selected.items():
        nodes = A.project_nodes(ROOT, module)
        current = A.snapshot(ROOT, LIB, nodes, toolchain)
        A.verify_compilation(records, nodes, current)
        directory = PRIVATE / "audit" / module
        accepted = []
        for path in [directory / "latest.json", *directory.glob("attempt-*/receipt.json")]:
            if path.is_file() and read(path).get("accepted") is True:
                validate_receipt(module, read(path), records)
                accepted.append(path)
        state = read(slot_dir(module) / "state.json")
        if accepted:
            path = accepted[0]; receipt = read(path)
            selected_path = slot_dir(module) / "selected-receipt.json"
            selected_path.write_bytes(path.read_bytes())
            item = entry["item"]
            state["gates"] = dict(I.GATES)
            state["audit_origin"] = dict({key: item[key] for key in ("run_id", "run_attempt", "commit", "artifact_id")},
                receipt_path=relative(selected_path), receipt_sha256=sha(selected_path), reuse="exact" if receipt["input_snapshot"] == current else "relocated")
            if item["format"] == "slot-v1" and entry["info"].get("audit_origin", {}).get("artifact_id") is not None:
                original = entry["info"]["audit_origin"]
                need(any(inp["artifact_id"] == original["artifact_id"] and module in inp["modules"] for inp in value["recovery_inputs"]), "Plan omitted original accepted audit producer")
                state["audit_origin"] = dict(original, receipt_path=relative(selected_path), receipt_sha256=sha(selected_path),
                                             reuse=state["audit_origin"]["reuse"])
        elif (directory / "latest.json").is_file():
            previous = read(directory / "latest.json")
            if previous.get("replay", {}).get("exit_code") == 0 and previous["replay"].get("inputs_unchanged") is True:
                need(replay_reusable(module, previous, current), "A completed stock replay cannot be reused at these paths; stop instead of repeating it")
                state["gates"]["stock_leanchecker"] = True
                state["partial_replay_reuse"] = True
        write(slot_dir(module) / "state.json", state)
    protected = {name: records[name] for name in selected}
    files = {name: digest for name, digest in sealed["files"].items()
             if name != ".lake/p2-private/records.json" and not name.startswith(".lake/p2-private/lib/")}
    files.update(sources)
    for origin in origins.values():
        for key in ("zip_path", "records_path"):
            files[origin[key]] = sha(ROOT / origin[key])
    for module in selected:
        files.update(immutable_module_files(module))
    write(W / "anchors.json", {"bootstrap_snapshot": frozen, "toolchain": toolchain,
          "protected_records": protected, "files": files, "sources": sources})
    state = read(W / "state.json"); state.update(origins=origins, status="verified", modules=wanted)
    write(W / "state.json", state)
    for entry in entries:
        shutil.rmtree(entry["raw"]); shutil.rmtree(entry["raw"].parent / "zip")
    guard(block)
    print("VERIFIED_REUSE: 93 original dependencies; existing numerical C/A/replay preserved", sorted(selected), flush=True)


def immutable_module_files(module):
    result = {}
    stem = LIB / module.replace(".", "/")
    paths = [Path(str(stem) + suffix) for suffix in I.FACETS]
    paths += list((PRIVATE / "logs").glob(module + ".attempt*.log"))
    paths += [path for path in (PRIVATE / "audit" / module).rglob("*") if path.name != "latest.json"]
    for path in paths:
        if path.is_file():
            need(not path.is_symlink(), "Linked proof artifact")
            result[relative(path)] = sha(path)
    return result


def guard(block):
    check_drivers()
    anchors = read(W / "anchors.json")
    records, reference = read(REGISTRY), read(BOOT / "public-reference.json")
    need(set(records) <= set(reference) | set(I.targets(block)) and set(reference) <= set(records), "Unplanned compilation record")
    for module, before in dict(reference, **anchors["protected_records"]).items():
        after = records[module]
        need(without_locator(after) == without_locator(before), "Original record changed beyond object locator: " + module)
        need(after["object"] in (before["object"], str(LIB / (module.replace(".", "/") + ".olean"))), "Unexpected live object locator")
    graph = bootstrap_graph()
    current = A.snapshot(ROOT, LIB, graph, anchors["toolchain"])
    need(current == anchors["bootstrap_snapshot"], "Historical dependency source/object changed")
    A.verify_compilation(records, graph, current)
    I.unchanged({ROOT / name: digest for name, digest in anchors["files"].items()})
    for module in anchors["protected_records"]:
        nodes = A.project_nodes(ROOT, module)
        A.verify_compilation(records, nodes, A.snapshot(ROOT, LIB, nodes, anchors["toolchain"]))
    return records


def freeze_success(module):
    anchors = read(W / "anchors.json")
    record = read(REGISTRY)[module]
    if module in anchors["protected_records"]:
        need(without_locator(record) == without_locator(anchors["protected_records"][module]), "Protected successful compilation changed")
    anchors["protected_records"][module] = record
    for name, digest in immutable_module_files(module).items():
        need(name not in anchors["files"] or anchors["files"][name] == digest, "Previously frozen proof artifact changed")
        anchors["files"][name] = digest
    write(W / "anchors.json", anchors)


def timed(block, module, phase, command):
    directory = slot_dir(module) if module else W
    log, metrics = directory / (phase + ".log"), directory / (phase + ".time.txt")
    started, start = datetime.now(timezone.utc).isoformat(), time.monotonic()
    with log.open("xb") as stream:
        code = subprocess.run(["/usr/bin/time", "-v", "-o", str(metrics), *command], cwd=ROOT,
                              env=dict(os.environ, LC_ALL="C"), stdout=stream, stderr=subprocess.STDOUT).returncode
    details = {"phase": phase, "command": command, "exit_code": code, "started_utc": started,
               "elapsed_seconds": round(time.monotonic() - start, 3), "log": relative(log), "log_sha256": sha(log),
               "time_log": relative(metrics), "time_log_sha256": sha(metrics)}
    match = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", metrics.read_text())
    details["maximum_resident_set_kib"] = int(match[1]) if match else None
    state = read(directory / "state.json")
    state.setdefault("phases", []).append(details); write(directory / "state.json", state)
    text = log.read_text(); print(text[-16000:], flush=True)
    guard(block)
    return code, text


def verify_target(module, records):
    graph = A.project_nodes(ROOT, module)
    frozen = A.snapshot(ROOT, LIB, graph, read(W / "anchors.json")["toolchain"])
    A.verify_compilation(records, graph, frozen)
    return frozen


def compile_slot(block, slot):
    module = slot_target(block, slot)
    output(target=module or "absent", present=module is not None, c_ready=False, c_new=False, accepted=False)
    if module is None:
        return
    records = guard(block)
    directory = slot_dir(module)
    if (directory / "state.json").exists() and read(directory / "state.json")["gates"]["strict_compile"]:
        verify_target(module, records)
        output(c_ready=True, accepted=read(directory / "state.json")["accepted"])
        print("REUSE_COMPILE", module, flush=True)
        return
    need(records.get(module, {}).get("exit_code") != 0, "An unqualified successful compilation exists; do not repeat it")
    if slot == "check":
        for page in I.targets(block)[:-1]:
            verify_target(page, records)  # Prevent C from silently filling missing page predecessors.
    graph = A.project_nodes(ROOT, module)
    predecessors = {name: node for name, node in graph.items() if name != module}
    A.verify_compilation(records, predecessors, A.snapshot(ROOT, LIB, predecessors, read(W / "anchors.json")["toolchain"]))
    resources()
    directory.mkdir(parents=True, exist_ok=True)
    if not (directory / "state.json").exists():
        write(directory / "state.json", {"module": module, "phases": [], "accepted": False,
              "gates": {key: False for key in I.GATES}, "compile_origin": None, "audit_origin": None})
    code, text = timed(block, module, "compile", ["python3", "verification/part2/run_winner9_private_checks.py", module,
        "--baseline-root", os.environ["P210_BASELINE"], "--workers", "1", "--threads", "1", "--memory-mb", "11264",
        "--time-budget-seconds", "3600"])
    need([line.split()[1] for line in text.splitlines() if line.startswith("START ")] == [module], "C started an unplanned module")
    need(code == 0, "Strict compilation failed; preserve its original attempt")
    records = guard(block); verify_target(module, records)
    memory, _ = strict_record(module, records[module]); need(memory == 11264, "New C did not use the approved memory limit")
    snapshot = directory / "compile-records.json"; snapshot.write_bytes(REGISTRY.read_bytes())
    state = read(directory / "state.json"); state["gates"]["strict_compile"] = True
    state["compile_origin"] = dict(producer(), artifact_id=None, records_path=relative(snapshot),
          records_sha256=sha(snapshot), memory_mb=11264, reused=False)
    write(directory / "state.json", state)
    freeze_success(module); guard(block)
    capture(block, module, "compiled")
    output(c_ready=True, c_new=True)


def export_gate(manifest, modules):
    need(set(manifest["accepted_modules"]) == set(modules) and manifest["accepted_module_count"] == len(modules)
         and not manifest["unselected_modules"] and not manifest["rejected_candidates"]
         and not manifest["duplicate_owned_declarations"], "Incomplete or rejected export")
    pages = {module: I.binding(module) for module in modules if re.fullmatch(re.escape(I.PREFIX) + r"NumericalPage[0-9]{4}", module)}
    coverage = manifest["coverage"]["numerical_pages"]
    need(coverage["bindings"] == pages and coverage["accepted_bound_pages"] == len(pages)
         and coverage["covered_rows"] == sum(item["row_count"] for item in pages.values()), "Wrong numerical page interval")
    need(set(manifest["transitive_axiom_counts"]) <= A.AXIOMS, "Forbidden transitive axiom")


def audit_export(block, slot):
    module = slot_target(block, slot)
    output(target=module or "absent", present=module is not None, accepted=False)
    if module is None:
        return
    directory = slot_dir(module)
    failure = None
    try:
        records = guard(block); current = verify_target(module, records)
        state = read(directory / "state.json")
        need(state["gates"]["strict_compile"], "Compilation gate did not pass")
        if state["audit_origin"] is not None:
            validate_receipt(module, read(directory / "selected-receipt.json"), records)
            print("REUSE_ACCEPTED_RECEIPT", module, state["audit_origin"]["reuse"], flush=True)
        else:
            latest = PRIVATE / "audit" / module / "latest.json"
            previous = read(latest) if latest.is_file() else {}
            partial = replay_reusable(module, previous, current)
            if previous.get("replay", {}).get("exit_code") == 0 and previous["replay"].get("inputs_unchanged") is True:
                need(partial, "Would repeat an already completed stock replay; stop")
            registry_before = REGISTRY.read_bytes()
            code, text = timed(block, module, "audit", ["python3", "verification/part2/run_winner9_private_audit.py", module,
                "--summary-name", "p210-resume-" + module.rsplit(".", 1)[1] + ".json", "--memory-mb", "11264"])
            need(REGISTRY.read_bytes() == registry_before, "Auditor changed compilation registry")
            if partial:
                need(not any(line.startswith("REPLAY ") for line in text.splitlines()), "Original auditor repeated a preserved stock replay")
            receipt = read(latest)
            state = read(directory / "state.json")
            if replay_reusable(module, receipt, current):
                state["gates"]["stock_leanchecker"] = True
            write(directory / "state.json", state)
            freeze_success(module)
            need(code == 0 and receipt.get("accepted") is True, "Owned audit not complete; partial replay remains preserved")
            validate_receipt(module, receipt, records)
            selected = directory / "selected-receipt.json"; selected.write_bytes(latest.read_bytes())
            state["gates"] = dict(I.GATES)
            state["audit_origin"] = dict(producer(), artifact_id=None, receipt_path=relative(selected),
                receipt_sha256=sha(selected), reuse="replay" if partial else "fresh")
            write(directory / "state.json", state)
        registry_before = REGISTRY.read_bytes()
        code, _ = timed(block, module, "export", ["python3", "verification/part2/export_winner9_private_evidence.py", module,
                       "--output-dir", str(directory / "evidence"), "--split", "all"])
        need(code == 0 and REGISTRY.read_bytes() == registry_before, "Original exporter failed or changed records")
        manifest = read(directory / "evidence/manifest.json"); export_gate(manifest, [module])
        state = read(directory / "state.json")
        need(manifest["accepted_modules"][module]["receipt_sha256"] == state["audit_origin"]["receipt_sha256"], "Exporter selected a different receipt")
        state["accepted"] = True; write(directory / "state.json", state)
        output(accepted=True)
    except BaseException as error:
        failure = error
    finally:
        guard_failure = None
        try:
            guard(block)
        except BaseException as error:
            guard_failure = error
            if (directory / "state.json").is_file():
                state = read(directory / "state.json")
                state.update(accepted=False, guard_error=repr(error))
                write(directory / "state.json", state)
        if directory.is_dir() and (directory / "state.json").is_file():
            capture(block, module, "progress")
        if guard_failure is not None:
            if failure is not None:
                print("ORIGINAL_FAILURE:", repr(failure), file=sys.stderr, flush=True)
            raise guard_failure
    if failure is not None:
        raise failure


def add_regular(paths, path):
    if path.is_file():
        need(not path.is_symlink() and path.resolve().is_relative_to(ROOT), "Linked or foreign checkpoint input")
        paths.add(path)


def pack(path, paths):
    for source in paths:
        need(source.is_file() and not source.is_symlink() and source.resolve().is_relative_to(ROOT),
             "Linked, missing or foreign checkpoint input")
    files = {relative(source): sha(source) for source in sorted(paths)}
    with tarfile.open(path, "x:gz", compresslevel=3) as archive:
        for source in sorted(paths):
            archive.add(source, arcname=relative(source), recursive=False)
    I.unchanged({ROOT / name: digest for name, digest in files.items()})
    return files


def module_paths(module):
    paths = set()
    stem = LIB / module.replace(".", "/")
    for suffix in I.FACETS:
        add_regular(paths, Path(str(stem) + suffix))
    for path in (PRIVATE / "logs").glob(module + ".attempt*.log"):
        add_regular(paths, path)
    for path in (PRIVATE / "audit" / module).rglob("*"):
        add_regular(paths, path)
    return paths


def capture(block, module, kind):
    need(kind in ("compiled", "progress"), "Unknown slot checkpoint kind")
    directory = slot_dir(module)
    destination = directory / kind
    if destination.exists():
        info = read(destination / "provenance.json")
        need(info["module"] == module and info["block"] == f"{block:02}" and info["format"] == "slot-v1"
             and sha(destination / "proof-and-original-evidence.tar.gz") == info["archive_sha256"], "Existing checkpoint changed")
        return
    destination.mkdir(parents=True, exist_ok=False)
    state = read(directory / "state.json")
    paths = module_paths(module)
    for path in (REGISTRY, ROOT / (module.replace(".", "/") + ".lean"), W / "resume-plan.json",
                 BOOT / "bootstrap.json", BOOT / "public-reference.json", BOOT / "plan.json"):
        add_regular(paths, path)
    for path in directory.iterdir():
        if path.suffix in (".json", ".log", ".txt"):
            add_regular(paths, path)
    for path in (directory / "evidence").rglob("*"):
        add_regular(paths, path)
    archive = destination / "proof-and-original-evidence.tar.gz"
    files = pack(archive, paths)
    write(destination / "provenance.json", dict(producer(), schema=1, format="slot-v1", block=f"{block:02}", module=module,
          bootstrap_origin=plan()["bootstrap"], plan_sha256=sha(W / "resume-plan.json"), gates=state["gates"], accepted=state["accepted"],
          compile_origin=state["compile_origin"], audit_origin=state["audit_origin"], files=files, archive_sha256=sha(archive)))


def deliver(block):
    records = guard(block); wanted = I.targets(block)
    origins = {}
    for module in wanted:
        verify_target(module, records)
        state = read(slot_dir(module) / "state.json")
        need(state["accepted"] is True and state["gates"] == I.GATES, "Block has an incomplete slot: " + module)
        validate_receipt(module, read(slot_dir(module) / "selected-receipt.json"), records)
        origins[module] = {"compile": state["compile_origin"], "audit": state["audit_origin"]}
    destination = W / "delivery"; destination.mkdir(exist_ok=False)
    registry_before = REGISTRY.read_bytes()
    code, _ = timed(block, None, "block-export", ["python3", "verification/part2/export_winner9_private_evidence.py", *wanted,
                   "--output-dir", str(destination / "evidence"), "--split", "all"])
    need(code == 0 and REGISTRY.read_bytes() == registry_before, "Whole-block exporter failed or changed records")
    manifest = read(destination / "evidence/manifest.json"); export_gate(manifest, wanted)
    for module in wanted:
        need(manifest["accepted_modules"][module]["receipt_sha256"] == origins[module]["audit"]["receipt_sha256"], "Whole-block export changed selected receipt")
    write(destination / "new-records.json", {module: records[module] for module in wanted})
    paths = {W / "resume-plan.json", W / "state.json", W / "resources.json", destination / "new-records.json"}
    for module in wanted:
        paths.update(module_paths(module))
        for name in ("state.json", "compile-records.json", "selected-receipt.json", "compile.log", "compile.time.txt",
                     "audit.log", "audit.time.txt", "export.log", "export.time.txt"):
            add_regular(paths, slot_dir(module) / name)
    state = read(W / "state.json")
    for origin in state["origins"].values():
        for key in ("zip_path", "records_path"):
            paths.add(ROOT / origin[key])
    archive = destination / "new-objects-and-receipts.tar.gz"
    files = pack(archive, paths)
    info = dict(producer(), schema=2, block=f"{block:02}", modules=wanted, gates=dict(I.GATES),
                bootstrap_sha256=plan()["bootstrap"]["tar_sha256"], bootstrap_origin=plan()["bootstrap"],
                plan_sha256=sha(W / "resume-plan.json"), origins=state["origins"], module_origins=origins, files=files,
                evidence_manifest_sha256=sha(destination / "evidence/manifest.json"), object_archive_sha256=sha(archive))
    info["delivery_files"] = {str(path.relative_to(destination)): sha(path) for path in destination.rglob("*") if path.is_file()}
    write(destination / "provenance.json", info)
    guard(block)
    print("ACCEPTED_BLOCK", f"{block:02}", "original C/A/E and exact numerical intervals", flush=True)


def recover(block):
    W.mkdir(parents=True, exist_ok=True)
    failure = None
    if (W / "anchors.json").is_file():
        try:
            guard(block)
        except BaseException as error:
            failure = error
    destination = W / "recovery"; destination.mkdir(exist_ok=False)
    paths = set()
    for module in I.targets(block):
        paths.update(module_paths(module))
    for path in (REGISTRY, BOOT / "public-reference.json", BOOT / "plan.json", BOOT / "bootstrap.json"):
        add_regular(paths, path)
    for path in W.rglob("*"):
        if path.is_relative_to(destination) or path.is_relative_to(W / "bootstrap-input") or path.is_relative_to(W / "bootstrap-zip"):
            continue
        if path.name == "bootstrap.zip" or path.is_relative_to(W / "delivery"):
            continue
        add_regular(paths, path)
    archive = destination / "proof-and-original-evidence.tar.gz"
    files = pack(archive, paths)
    write(destination / "provenance.json", dict(producer(), schema=1, block=f"{block:02}",
          credit="NONE: diagnostics require the original gates before reuse", files=files, archive_sha256=sha(archive),
          guard_error=None if failure is None else repr(failure)))
    if failure is not None:
        raise failure


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("bootstrap", "restore", "compile", "audit-export", "capture", "deliver", "recover"))
    parser.add_argument("--block", type=int, required=True)
    parser.add_argument("--plan", default=str(PLAN))
    parser.add_argument("--slot")
    parser.add_argument("--kind", choices=("compiled", "progress"))
    args = parser.parse_args()
    need(8 <= args.block <= 43, "Never repeat blocks 00..07")
    if args.action == "bootstrap":
        bootstrap(args.block, args.plan)
    elif args.action == "restore":
        need(Path(args.plan).resolve() == PLAN, "Use the checked-in resume plan")
        restore(args.block)
    elif args.action == "compile":
        compile_slot(args.block, args.slot)
    elif args.action == "audit-export":
        audit_export(args.block, args.slot)
    elif args.action == "capture":
        module = slot_target(args.block, args.slot)
        if module is not None:
            capture(args.block, module, args.kind)
    elif args.action == "deliver":
        deliver(args.block)
    else:
        recover(args.block)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
