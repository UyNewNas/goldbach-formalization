#!/usr/bin/env python3
"""One controlled Page0224 retry; transport and guards, never a proof verifier.

The original C/A/E drivers perform compilation, stock replay and owned audit.
Only public CI inputs are restored. Existing 93-module objects are never built.
"""
from __future__ import annotations

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
SOURCE_COMMIT = "8bb6eac5aae11d217fb29324e1db7685954d30ac"
TARGET = "ImbalancedChen.P2Winner9NumericalPage0224"
SOURCE_SHA = "7752517c9265f9c88089ec22a243566d93f3db87888482170a30bb16fda7f69d"
BOOT_ID, BOOT_RUN = 15013442313, 45589950483
BOOT_NAME = "p210-bootstrap-45589950483-1"
ZIP_BYTES = 413971373
ZIP_SHA = "8a3e7275fafe9b5b0046a541d320fd4669dd413a5444384ff782c3873d16c76c"
TAR_SHA = "e17d879ab60ad21874b8b26ce20075a1b646af82ee18cf00749773ba5dc37370"
SEAL_SHA = "d0c466739000ffe4351612a751123ae22db6f088c27cd71d640d1649dd6a5771"
RECORDS_SHA = "ee3d1b8d4dd962ba4195b90299062ab972de82422cb24114822a1a5442e77689"
EXPECTED_BINDING = {"page": 224, "first_ordinal": 3584, "row_count": 16,
                    "last_ordinal": 3599, "block": 14, "local_page": 0}
ROOT = Path.cwd().resolve()
W = ROOT / ".lake/p210-memory-probe"
BOOT = ROOT / ".lake/p210-ci"
PRIVATE = ROOT / ".lake/p2-private"
LIB = PRIVATE / "lib"
REGISTRY = PRIVATE / "records.json"
SOURCE = ROOT / (TARGET.replace(".", "/") + ".lean")
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


def api(endpoint):
    return json.loads(subprocess.check_output(["gh", "api", endpoint]))


def check_metadata(value):
    need(value["id"] == BOOT_ID and value["name"] == BOOT_NAME and not value["expired"]
         and value["size_in_bytes"] == ZIP_BYTES and value["digest"] == "sha256:" + ZIP_SHA
         and value["workflow_run"]["id"] == BOOT_RUN
         and value["workflow_run"]["head_sha"] == SOURCE_COMMIT,
         "Bootstrap artifact is not the fixed successful public producer")


def check_drivers():
    for path, expected in I.DRIVER_HASHES.items():
        need(sha(path) == expected, "Original C/A/E driver changed: " + path)
    need(sha(I.__file__) == "8848ad7f94ca485004602925440858b6c41b1649be7ae721623b7dcb91452cf6",
         "Reviewed archive/transport helpers changed")
    need(SOURCE.is_file() and not SOURCE.is_symlink() and sha(SOURCE) == SOURCE_SHA,
         "Page0224 differs from its failed -M6144 source")


def refuse_existing_compilation():
    page = 1
    while True:
        values = api(f"repos/{REPO}/actions/artifacts?per_page=100&page={page}")["artifacts"]
        matches = [v for v in values if not v["expired"] and
                   v["name"].startswith("p210-page0224-compiled-")]
        need(not matches, "A successful Page0224 compilation is already preserved; reuse its artifact instead of rebuilding: "
             + ", ".join(str(v["id"]) for v in matches))
        if len(values) < 100:
            break
        page += 1


def restore():
    need(os.environ["GITHUB_REPOSITORY"] == REPO, "Unexpected repository")
    need(subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
         == os.environ["GITHUB_SHA"], "Checkout differs from diagnostic producer")
    check_drivers()
    refuse_existing_compilation()
    W.mkdir(parents=True, exist_ok=False)
    metadata = api(f"repos/{REPO}/actions/artifacts/{BOOT_ID}")
    check_metadata(metadata)
    write(W / "input-provenance.json", {"artifact": metadata, "archive_zip_sha256": ZIP_SHA,
          "bootstrap_tar_sha256": TAR_SHA, "seal_sha256": SEAL_SHA,
          "records_sha256": RECORDS_SHA, "source_commit": SOURCE_COMMIT,
          "source_sha256": SOURCE_SHA, "new_environment_compilations": 0})
    archive = W / "bootstrap.zip"
    with archive.open("xb") as stream:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{BOOT_ID}/zip"],
                       stdout=stream, check=True)
    need(archive.stat().st_size == ZIP_BYTES and sha(archive) == ZIP_SHA, "Bootstrap ZIP bytes changed")
    unpacked = I.unpack_zip(archive, W / "transport")
    need(unpacked == {"bootstrap.tar.gz": TAR_SHA}, "Unexpected bootstrap ZIP inventory or tar SHA")
    stage = W / "bootstrap-input"
    files = I.unpack_tar(W / "transport/bootstrap.tar.gz", stage)
    seal_path = ".lake/p210-ci/bootstrap.json"
    need(files.get(seal_path) == SEAL_SHA, "Bootstrap seal changed")
    sealed = read(stage / seal_path)
    need(files == dict(sealed["files"], **{seal_path: SEAL_SHA}), "Bootstrap tar inventory differs from its seal")
    need(sealed["commit"] == SOURCE_COMMIT and sealed["run_id"] == str(BOOT_RUN)
         and sealed["run_attempt"] == "1" and sealed["proof_credit"] == 0,
         "Foreign bootstrap provenance or unexpected proof credit")
    for relative, digest in files.items():
        need(relative.startswith((".lake/p210-ci/", ".lake/p2-private/")), "Unexpected bootstrap installation path")
        I.no_destination(ROOT, relative)
        I.exclusive_link_or_copy(stage / relative, ROOT / relative, digest)
    shutil.rmtree(stage)  # Only this command's temporary extraction; installed hardlinks remain.
    need(sha(REGISTRY) == sha(BOOT / "public-reference.json") == RECORDS_SHA,
         "Bootstrap did not preserve the original 93 record bytes")
    write(W / "state.json", {"run_id": os.environ["GITHUB_RUN_ID"],
          "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"], "commit": os.environ["GITHUB_SHA"],
          "target": TARGET, "source_sha256": SOURCE_SHA, "phases": [],
          "gates": {"strict_compile": False, "stock_leanchecker": False,
                    "owned_declarations_and_axioms": False, "evidence_export": False},
          "old_numerical_rows_replayed": 0, "bootstrap_modules_recompiled": 0})


def bootstrap_graph():
    common = I.nodes(ROOT, [I.PREFIX + "MaterializedLogChecker", I.PREFIX + "SeedArchiveChecks"])
    seeds = [I.PREFIX + f"CompleteSeedBlock{b:02}" for b in range(8, 44)]
    graph = I.nodes(ROOT, [*common, *seeds])
    need(len(common) == 57 and len(graph) == 93 and set(graph) == set(common) | set(seeds), "Unexpected bootstrap closure")
    return graph


def verify():
    check_drivers()
    need(sha(C.LEAN) == I.LEAN_SHA and sha(A.LEANCHECKER) == I.CHECKER_SHA, "Lean/checker binary changed")
    toolchain = {"lean_version": subprocess.check_output([C.LEAN, "--version"], text=True).strip(),
                 "lean_binary_sha256": sha(C.LEAN),
                 "mathlib_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=C.MATHLIB, text=True).strip()}
    need(toolchain["mathlib_commit"] == C.PIN, "Mathlib pin changed")
    plan, sealed, reference = read(BOOT / "plan.json"), read(BOOT / "bootstrap.json"), read(BOOT / "public-reference.json")
    need(sha(BOOT / "bootstrap.json") == SEAL_SHA and sha(REGISTRY) == RECORDS_SHA
         and REGISTRY.read_bytes() == (BOOT / "public-reference.json").read_bytes(), "Original record bytes changed")
    need(plan["commit"] == SOURCE_COMMIT and plan["run_id"] == str(BOOT_RUN)
         and plan["toolchain"] == toolchain, "Bootstrap toolchain/provenance mismatch")
    graph = bootstrap_graph()
    need(set(reference) == set(graph) == set(plan["modules"]) == set(sealed["modules"]), "Incomplete 93-module reuse")
    frozen = A.snapshot(ROOT, LIB, graph, toolchain)
    A.verify_compilation(reference, graph, frozen)
    I.unchanged({ROOT / p: digest for p, digest in sealed["files"].items()})
    target_graph = A.project_nodes(ROOT, TARGET)
    need(set(target_graph) - set(graph) == {TARGET} and len(target_graph) == 59,
         "Single-page retry would compile additional project modules")
    need(TARGET not in reference and not (LIB / (TARGET.replace(".", "/") + ".olean")).exists(),
         "Page0224 already has a local compilation; do not repeat it")
    baseline = Path(os.environ["P210_BASELINE"]) / ".lake/build/lib/lean"
    need(not any(p.is_file() and not (LIB / p.relative_to(baseline)).exists() for p in baseline.rglob("*")),
         "The original compile driver would copy unplanned baseline objects")
    available = int(re.search(r"^MemAvailable:\s+(\d+)", Path("/proc/meminfo").read_text(), re.M)[1]) * 1024
    cg = Path("/sys/fs/cgroup")
    if (cg / "memory.max").is_file() and (cg / "memory.max").read_text().strip() != "max":
        available = min(available, int((cg / "memory.max").read_text()) - int((cg / "memory.current").read_text()))
    need(available >= 13 * 2**30, "Less than 13 GiB actually available for the single -M11264 process")
    need(shutil.disk_usage(ROOT).free >= 2 * 2**30, "Insufficient space to preserve proof and evidence")
    write(W / "resources.json", {"available_bytes": available, "disk_free_bytes": shutil.disk_usage(ROOT).free,
          "workers": 1, "lean_threads": 1, "lean_memory_mib": 11264, "lean_memory_flag_applied": True})
    (W / "bootstrap-records.json").write_bytes(REGISTRY.read_bytes())
    write(W / "anchors.json", {"frozen": frozen, "modules": sorted(graph), "toolchain": toolchain,
          "sealed_files": sealed["files"], "source_sha256": SOURCE_SHA})
    print("VERIFIED_REUSE: exact 93 historical dependencies; only Page0224 may compile", flush=True)


def guard():
    check_drivers()
    anchors = read(W / "anchors.json")
    original, current = read(W / "bootstrap-records.json"), read(REGISTRY)
    need(set(current) in (set(original), set(original) | {TARGET}), "An unplanned module entered the compile registry")
    for name, before in original.items():
        after = current[name]
        need({k: v for k, v in before.items() if k != "object"} == {k: v for k, v in after.items() if k != "object"},
             "Historical record changed: " + name)
        need(after["object"] in (before["object"], str(LIB / (name.replace(".", "/") + ".olean"))), "Unexpected object locator")
    graph = bootstrap_graph()
    frozen = A.snapshot(ROOT, LIB, graph, anchors["toolchain"])
    need(frozen == anchors["frozen"], "Historical source/object/environment changed")
    A.verify_compilation(current, graph, frozen)
    I.unchanged({ROOT / p: digest for p, digest in anchors["sealed_files"].items()
                 if p != ".lake/p2-private/records.json" and not p.startswith(".lake/p2-private/lib/")})
    return current


def timed(command, phase):
    state = read(W / "state.json")
    log, metrics = W / (phase + ".log"), W / (phase + ".time.txt")
    started_utc, start = datetime.now(timezone.utc).isoformat(), time.monotonic()
    with log.open("xb") as stream:
        code = subprocess.run(["/usr/bin/time", "-v", "-o", str(metrics), *command],
                              cwd=ROOT, env=dict(os.environ, LC_ALL="C"), stdout=stream, stderr=subprocess.STDOUT).returncode
    elapsed = round(time.monotonic() - start, 3)
    match = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", metrics.read_text())
    state["phases"].append({"phase": phase, "command": command, "exit_code": code,
          "started_utc": started_utc, "elapsed_seconds": elapsed,
          "maximum_resident_set_kib": int(match[1]) if match else None,
          "log": str(log.relative_to(ROOT)), "log_sha256": sha(log),
          "time_log": str(metrics.relative_to(ROOT)), "time_log_sha256": sha(metrics)})
    write(W / "state.json", state)
    print(log.read_text()[-24000:], flush=True)
    guard()  # Also run on a nonzero compiler/auditor/exporter exit.
    need(code == 0, phase + " failed; original logs/records are preserved")
    return log.read_text()


def compile_page():
    guard()
    text = timed(["python3", "verification/part2/run_winner9_private_checks.py", TARGET,
                  "--baseline-root", os.environ["P210_BASELINE"], "--workers", "1", "--threads", "1",
                  "--memory-mb", "11264", "--time-budget-seconds", "3600"], "compile")
    need([s.split()[1] for s in text.splitlines() if s.startswith("START ")] == [TARGET],
         "A dependency was rebuilt or the sole new target was not compiled")
    records = guard()
    graph = A.project_nodes(ROOT, TARGET)
    A.verify_compilation(records, graph, A.snapshot(ROOT, LIB, graph, read(W / "anchors.json")["toolchain"]))
    record = records[TARGET]
    expected = [C.LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true", "-DmaxRecDepth=50000",
                "-DmaxHeartbeats=40000000", "-o", str(LIB / (TARGET.replace(".", "/") + ".olean")),
                TARGET.replace(".", "/") + ".lean"]
    need(record["new_strict_compile"] is True and record["command"] == expected
         and record["exit_code"] == 0 and record["attempts"][-1]["command"] == expected
         and record["attempts"][-1]["exit_code"] == 0, "Missing actual strict -M11264 compilation")
    (W / "compile-records.json").write_bytes(REGISTRY.read_bytes())
    state = read(W / "state.json"); state["gates"]["strict_compile"] = True; write(W / "state.json", state)
    capture("compiled")


def audit_page():
    need(read(W / "state.json")["gates"]["strict_compile"], "Compilation did not pass")
    timed(["python3", "verification/part2/run_winner9_private_audit.py", TARGET,
           "--summary-name", "p210-page0224-memory.json", "--memory-mb", "11264"], "audit")
    summary = read(PRIVATE / "audit/p210-page0224-memory.json")
    need(summary["all_accepted"] is True and set(summary["modules"]) == {TARGET}
         and summary["modules"][TARGET]["accepted"] is True, "One-page stock replay/owned audit incomplete")
    state = read(W / "state.json")
    state["gates"].update(stock_leanchecker=True, owned_declarations_and_axioms=True)
    write(W / "state.json", state)


def page_export_gate(manifest):
    need(set(manifest["accepted_modules"]) == {TARGET} and manifest["accepted_module_count"] == 1
         and not manifest["unselected_modules"] and not manifest["rejected_candidates"]
         and not manifest["duplicate_owned_declarations"], "Exporter did not accept exactly Page0224")
    coverage = manifest["coverage"]["numerical_pages"]
    need(coverage["bindings"] == {TARGET: EXPECTED_BINDING} and coverage["accepted_bound_pages"] == 1
         and coverage["covered_rows"] == 16, "Wrong Page0224/3584..3599 binding")
    need(set(manifest["transitive_axiom_counts"]) <= A.AXIOMS, "Forbidden transitive axiom")


def export_page():
    need(all(read(W / "state.json")["gates"][k] for k in
             ("strict_compile", "stock_leanchecker", "owned_declarations_and_axioms")), "Earlier gate did not pass")
    timed(["python3", "verification/part2/export_winner9_private_evidence.py", TARGET,
           "--output-dir", str(W / "evidence"), "--split", "all"], "export")
    page_export_gate(read(W / "evidence/manifest.json"))
    state = read(W / "state.json"); state["gates"]["evidence_export"] = True; write(W / "state.json", state)


def capture(kind="recovery"):
    W.mkdir(parents=True, exist_ok=True)
    paths = {p for pattern in ("*.json", "*.log", "*.time.txt") for p in W.glob(pattern) if p.is_file()}
    paths.update(p for p in (REGISTRY, SOURCE, BOOT / "bootstrap.json", BOOT / "public-reference.json", BOOT / "plan.json") if p.is_file())
    stem = LIB / TARGET.replace(".", "/")
    paths.update(Path(str(stem) + suffix) for suffix in I.FACETS if Path(str(stem) + suffix).is_file())
    paths.update(p for p in (PRIVATE / "logs").glob(TARGET + ".attempt*.log") if p.is_file())
    paths.update(p for p in (PRIVATE / "audit" / TARGET).rglob("*") if p.is_file())
    paths.update(p for p in (W / "evidence").rglob("*") if p.is_file())
    paths.update(p for p in (PRIVATE / "audit/p210-page0224-memory.json", Path(__file__), Path(C.__file__), Path(A.__file__), Path(E.__file__), A.TEMPLATE) if p.is_file())
    output = W / kind; output.mkdir(exist_ok=False)
    files = {}
    with tarfile.open(output / "proof-and-original-evidence.tar.gz", "w:gz", compresslevel=3) as archive:
        for path in sorted(paths):
            need(not path.is_symlink() and path.resolve().is_relative_to(ROOT), "Linked or foreign recovery input")
            relative = str(path.relative_to(ROOT)); files[relative] = sha(path)
            archive.add(path, arcname=relative, recursive=False)
    state = read(W / "state.json") if (W / "state.json").is_file() else {"gates": {}, "status": "setup-incomplete"}
    write(output / "provenance.json", {"kind": kind, "target": TARGET, "source_sha256": SOURCE_SHA,
          "source_commit": SOURCE_COMMIT, "producer_run_id": os.environ.get("GITHUB_RUN_ID"),
          "producer_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"), "producer_commit": os.environ.get("GITHUB_SHA"),
          "bootstrap_artifact_id": BOOT_ID, "bootstrap_zip_sha256": ZIP_SHA, "bootstrap_tar_sha256": TAR_SHA,
          "state": state, "files": files, "archive_sha256": sha(output / "proof-and-original-evidence.tar.gz"),
          "boundary": "Original driver records and actual object facets. Only all three gates plus exact export confer one-page acceptance; recovery material alone grants none."})


def finish():
    failure = None
    if (W / "anchors.json").is_file():
        try:
            guard()
            if (W / "compile-records.json").is_file():
                need(REGISTRY.read_bytes() == (W / "compile-records.json").read_bytes(), "Audit/export changed compilation records")
        except BaseException as error:
            failure = error
            write(W / "guard-failure.json", {"error": type(error).__name__ + ": " + str(error)})
    capture("recovery")
    state = read(W / "state.json") if (W / "state.json").is_file() else {}
    if failure is None and state.get("gates") and all(state["gates"].values()):
        page_export_gate(read(W / "evidence/manifest.json"))
        capture("accepted")
        print("PAGE0224_ACCEPTED: original C/A/E gates; 16 rows; no old numerical replay", flush=True)
    if failure is not None:
        raise failure


if __name__ == "__main__":
    actions = {"restore": restore, "verify": verify, "compile": compile_page,
               "audit": audit_page, "export": export_page, "finish": finish}
    need(len(sys.argv) == 2 and sys.argv[1] in actions, "Expected one fixed orchestration phase")
    actions[sys.argv[1]]()
