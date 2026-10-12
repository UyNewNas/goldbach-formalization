#!/usr/bin/env python3
"""Read-only comparison of supplied actual core evidence; never executes Lean/CI."""
from __future__ import annotations
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import zipfile

OUT = Path(__file__).resolve().parent
ROUND = OUT.parents[1]
CORE = ROUND / "d0366ce-ci/core"
OLD = ROUND / "p2-intake"
REPO = ROUND.parent / "goldbach-formalization"
SHA = "d0366ce64272e81faf6166a8a90050f56b328d38"
TREE = "e2ab22b96f76c8969386296558c626c62a581700"
ZIP_SHA = "4d7499fd526651d70f73fb7cbbf98769ffc51d8a406e1bc80f96ad5dc0d20df8"
P2_COUNTS = {"ImbalancedChen.Certificates.PairedV2Batch4To64Data": 72,
             "ImbalancedChen.Certificates.PairedV2Batch4To64": 207,
             "ImbalancedChen.Certificates.PairedV2Prefix64": 121}
ALL_COUNTS = {"ImbalancedChen.StoredHistoricalBoxPermit": 14, **P2_COUNTS}
SHORTS = ["integral_semantics", "integral_bounds", "integral_eq_parts", "source_ordinal_coverage", "rowIndices_injective"]
KEYS = ["ImbalancedChen.Certificates.PairedV2.Prefix64." + name for name in SHORTS]
STEPS = ["Build the full project", "Check the four explicit round 4 production targets",
         "Recheck ImbalancedChen with bundled Lean 4.33.0-rc1 leanchecker",
         "Audit ImbalancedChen root declarations and transitive axioms",
         "Export complete round 3 types and the existing conditional main bridge",
         "Export complete round 4 types and the existing conditional main bridge"]
checks = []

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def write_json(name: str, value: object) -> None:
    p = OUT / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def require(condition: bool, label: str) -> None:
    checks.append({"check": label, "passed": bool(condition)})
    if not condition:
        raise RuntimeError(label)

def file_identity(path: Path) -> dict:
    raw = path.read_bytes()
    return {"path": str(path), "bytes": len(raw), "sha256": sha(raw)}

def markers(raw: bytes, marker: bytes, timestamped: bool = False) -> tuple[dict, dict]:
    records, locations = {}, {}
    offset = 0
    for number, line in enumerate(raw.splitlines(keepends=True), 1):
        at = line.find(marker)
        if at >= 0 and (at == 0 or (timestamped and re.fullmatch(rb"(?:\xef\xbb\xbf)?[0-9T:.Z-]+ ", line[:at]))):
            record = json.loads(line[at + len(marker):])
            name = record["name"]
            require(name not in records, "Unique original marker: " + name)
            records[name] = record
            locations[name] = {"line": number, "byte_offset": offset, "line_bytes": len(line),
                               "line_sha256": sha(line), "marker_offset_in_line": at,
                               "external_log_prefix_hex": line[:at].hex(), "marker_bytes": line[at:]}
        offset += len(line)
    return records, locations

def main() -> None:
    report = {"scope": "ACTUAL_D036_CORE_P2_400_INDEPENDENT_EVIDENCE_COMPARISON",
              "status": "REVIEW_IN_PROGRESS", "source_commit": SHA, "source_tree": TREE,
              "run": 38289734671, "job": 114946653833, "artifact": 11767708658,
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "lean_ci_network_or_consumer_execution": False, "type_simplification_or_whitespace_normalization": False}
    try:
        run = json.loads((CORE / "run.json").read_bytes())
        jobs = json.loads((CORE / "jobs.json").read_bytes())["jobs"]
        artifacts = json.loads((CORE / "artifacts.json").read_bytes())["artifacts"]
        require(run["id"] == 38289734671 and run["head_sha"] == SHA and run["run_attempt"] == 1,
                "Exact actual run, source SHA and attempt")
        require(run["status"] == "completed" and run["conclusion"] == "success", "Actual run completed successfully")
        chosen = [j for j in jobs if j["id"] == 114946653833]
        require(len(chosen) == 1, "Unique actual job")
        job = chosen[0]
        require(job["run_id"] == run["id"] and job["head_sha"] == SHA, "Job identity binds actual source")
        require(job["status"] == "completed" and job["conclusion"] == "success", "Actual job completed successfully")
        steps = []
        for name in STEPS:
            values = [s for s in job["steps"] if s["name"] == name]
            require(len(values) == 1 and values[0]["status"] == "completed" and values[0]["conclusion"] == "success",
                    "Actual required step succeeded: " + name)
            steps.append(values[0])
        selected = [a for a in artifacts if a["id"] == 11767708658]
        require(len(selected) == 1, "Unique actual artifact")
        artifact = selected[0]
        require(artifact["workflow_run"]["id"] == run["id"] and artifact["workflow_run"]["head_sha"] == SHA,
                "Artifact belongs to exact actual source/run")
        archive_raw = (CORE / "core-artifact.zip").read_bytes()
        require(len(archive_raw) == 543994 == artifact["size_in_bytes"], "Original archive length")
        require(sha(archive_raw) == ZIP_SHA and artifact["digest"] == "sha256:" + ZIP_SHA, "Original archive API SHA-256")
        with zipfile.ZipFile(CORE / "core-artifact.zip") as archive:
            names = [i.filename for i in archive.infolist() if not i.is_dir()]
            require(len(names) == len(set(names)) and archive.testzip() is None, "Archive member uniqueness and CRC")
            members = [n for n in names if "/.lake/part0-round4-types/" in n and n.endswith("/receipt.json")]
            require(len(members) == 1, "Unique actual Round4 type receipt")
            parent = members[0].rsplit("/", 1)[0]
            receipt_raw = archive.read(members[0])
            receipt = json.loads(receipt_raw)
            require(receipt["source_commit"] == receipt["source_commit_after"] == SHA, "Round4 receipt binds before/after source")
            require(receipt["status"] == "PASS" and receipt["lean_invocation_started"] is True
                    and receipt["lean_exit_code"] == receipt["pin_check_exit_code"] == 0 and receipt["failures"] == [],
                    "Actual strict Round4 type invocation succeeded")
            require(receipt["expected_defining_module_counts"] == ALL_COUNTS
                    and receipt["declaration_count"] == receipt["expected_owned_declarations"] == 414,
                    "Actual complete census 14+72+207+121=414")
            require(receipt["full_types_untruncated"] is True and receipt["unsafe_and_new_axiom_checks"] == "PASS_IN_LEAN",
                    "Actual complete type and Lean safety audit flags")
            require(receipt["inputs_before"] == receipt["inputs_after"], "All actual source/object snapshots unchanged during Round4 export")
            decl_raw = archive.read(parent + "/declarations.json")
            stdout = archive.read(parent + "/stdout.log")
            stderr = archive.read(parent + "/stderr.log")
            require(sha(decl_raw) == receipt["compiler_output_files_sha256"]["declarations.json"], "Actual declaration JSON digest")
            require(sha(stdout) == receipt["stdout_sha256"] and sha(stderr) == receipt["stderr_sha256"], "Actual compiler raw stream digests")
            require(stderr == b"", "Actual compiler stderr is empty")
            declarations = json.loads(decl_raw)
            current = {r["name"]: r for r in declarations}
            require(len(current) == len(declarations) == 414 and dict(Counter(r["module"] for r in declarations)) == ALL_COUNTS,
                    "Actual JSON inventory exactly covers four defining modules")
            actual_stdout, stdout_locations = markers(stdout, b"P0_ROUND4_DECL ")
            require(actual_stdout == current, "All 414 raw stdout marker records exactly equal actual JSON records")
            require(stdout.count(b"P0_ROUND4_COUNT 414\n") == 1, "Actual raw compiler count footer is 414")
            stage_name = next(n for n in names if n.endswith("/lean-verification-logs/round4-types.log"))
            stage_raw = archive.read(stage_name)
            require(stdout in stage_raw, "Entire actual compiler stdout appears unchanged in Round4 stage log")
            stage_records, _ = markers(stage_raw, b"P0_ROUND4_DECL ")
            require(stage_records == current, "All actual stage marker records match JSON")
            job_raw = (CORE / "job.log").read_bytes()
            job_records, job_locations = markers(job_raw, b"P0_ROUND4_DECL ", True)
            require(job_records == current, "All 414 records exactly appear in the supplied complete actual job log")
            require(all(stdout_locations[n]["marker_bytes"] == job_locations[n]["marker_bytes"] for n in current),
                    "Every job marker byte string equals stdout after removing only its external optional BOM and timestamp")
            module_markers = [json.loads(line[len(b"P0_ROUND4_MODULE "):]) for line in stdout.splitlines() if line.startswith(b"P0_ROUND4_MODULE ")]
            require(len(module_markers) == 4 and {x["module"]: x["count"] for x in module_markers} == ALL_COUNTS,
                    "Four actual module-count marker records")
            audit_key, audit_hash = next(iter(receipt["audit_object_after"].items()))
            audit_raw = archive.read(parent + "/Round4Audit.olean")
            require(sha(audit_raw) == audit_hash and receipt["audit_object_before"] == {}, "Actual fresh audit output object bytes bind receipt")
            producer_path = OLD / "fixed-source/verification/part2/round3/batch4-to64/compiler-types.json"
            producer_all = json.loads(producer_path.read_bytes())
            producer = {r["name"]: r for r in producer_all if r["module"] in P2_COUNTS}
            p2 = {n: r for n, r in current.items() if r["module"] in P2_COUNTS}
            require(len(producer) == len(p2) == 400 and set(producer) == set(p2), "Same exact 400 producer/current declaration names")
            fields = ["name", "module", "kind", "type", "readable_type", "axioms"]
            comparisons = []
            differences = []
            for name, record in p2.items():
                old = producer[name]
                equalities = {field: old[field] == record[field] for field in fields}
                for field, equal in equalities.items():
                    if not equal:
                        differences.append({"name": name, "field": field, "producer": old[field], "actual_core": record[field]})
                comparisons.append({"name": name, "module": record["module"], "exact_fields": equalities,
                                    "actual_type_utf8_sha256": sha(record["type"].encode()),
                                    "producer_type_utf8_sha256": sha(old["type"].encode()),
                                    "actual_raw_stdout_location": {k: v for k, v in stdout_locations[name].items() if k != "marker_bytes"},
                                    "actual_job_log_location": {k: v for k, v in job_locations[name].items() if k != "marker_bytes"}})
            write_json("TYPE_DIFFERENCES.json", differences)
            require(not differences, "All 400 name/module/kind/type/readable_type/axioms fields are exactly unchanged")
            producer_receipt_path = OLD / "fixed-source/verification/part2/round3/batch4-to64/receipt.json"
            producer_receipt = json.loads(producer_receipt_path.read_bytes())
            tree = subprocess.run(["git", "rev-parse", SHA + "^{tree}"], cwd=REPO, check=True, stdout=subprocess.PIPE).stdout.decode().strip()
            require(tree == TREE, "Local fixed integration Git object has published tree")
            source_rows = []
            old_objects = {m["module"]: m["object_sha256"] for m in json.loads((OLD / "P2_INTAKE_RECEIPT.json").read_bytes())["original_gates"] if m["action"] == "compile"}
            for module in producer_receipt["all_production_modules"]:
                if isinstance(module, dict):
                    module = module["module"]
                relative = module.replace(".", "/") + ".lean"
                current_bytes = subprocess.run(["git", "show", SHA + ":" + relative], cwd=REPO, check=True, stdout=subprocess.PIPE).stdout
                producer_bytes = (OLD / "fixed-source" / relative).read_bytes()
                require(current_bytes == producer_bytes, "Current fixed source bytes equal producer: " + module)
                require(sha(current_bytes) == producer_receipt["source_inputs"][relative]["sha256"], "Producer source identity: " + module)
                captured_source = receipt["inputs_before"]["source_sha256"].get(relative)
                parts = receipt["inputs_before"]["production_olean_parts"].get(module)
                if module in P2_COUNTS:
                    require(captured_source is not None and parts is not None, "All new P2 source/object snapshots are actually present: " + module)
                if captured_source is not None:
                    require(sha(current_bytes) == captured_source, "Actual export source snapshot matches fixed source: " + module)
                main_olean = parts[".lake/build/lib/lean/" + module.replace(".", "/") + ".olean"] if parts is not None else None
                source_rows.append({"module": module, "repository_path": relative, "source_sha256": sha(current_bytes),
                                    "source_bytes_exactly_equal": True, "actual_current_object_parts": parts,
                                    "source_captured_in_actual_export": captured_source is not None,
                                    "binding_scope": "ACTUAL_EXPORT_SOURCE_AND_OBJECT_HASHES" if captured_source is not None and parts is not None else "FIXED_GIT_SOURCE_IDENTITY_ONLY_NOT_IN_THIS_EXPORT_SNAPSHOT",
                                    "producer_main_olean_sha256": old_objects.get(module),
                                    "producer_and_core_main_olean_hash_equal": None if module not in old_objects or main_olean is None else old_objects[module] == main_olean})
            checker_name = next(n for n in names if n.endswith("/lean-verification-logs/leanchecker.log"))
            checker_raw = archive.read(checker_name)
            for module in P2_COUNTS:
                require(("replaying " + module).encode() in checker_raw, "Actual bundled root replay log includes module: " + module)
            write_json("COMPARISON_400.json", comparisons)
            write_json("SOURCE_OBJECT_BINDINGS.json", {"source_commit": SHA, "producer_source_commit": "f0c00f9ccce98e04af439321a92eb9fd0dd26203",
                       "sources": source_rows, "complete_inputs_before_after_equal": True,
                       "production_object_bytes_in_artifact": False, "production_objects_compared_as_recorded_hashes_only": True,
                       "replay_log_contains_module_markers_but_not_same_time_object_hashes": True,
                       "difference_explanation_inferred": False})
            write_json("ACTUAL_CORE_P2_400_RECORDS.json", list(p2.values()))
            write_json("ACTUAL_CORE_FIVE_RECORDS.json", [current[n] for n in KEYS])
            (OUT / "ACTUAL_ROUND4_RECEIPT.json").write_bytes(receipt_raw)
            (OUT / "actual-round4-stdout.log").write_bytes(stdout)
            pp_dir = OUT / "actual-five-ppall"
            pp_dir.mkdir(exist_ok=True)
            text = ["# d0366ce 实际 core 输出的五个完整 P2 类型", "", "Source: " + SHA,
                    "", "Run 38289734671; job 114946653833; artifact 11767708658.", "",
                    "以下 type 是本次实际完整 pp.all 字段，不是源码提取。和旧 producer 的五个字段逐字相同。", ""]
            for short, name in zip(SHORTS, KEYS):
                (pp_dir / (short + ".txt")).write_bytes(current[name]["type"].encode())
                text += ["## " + name, "", "```lean", current[name]["type"], "```", "",
                         "实际公理：`" + "`, `".join(current[name]["axioms"]) + "`。", ""]
            (OUT / "ACTUAL_CORE_FIVE_PP_ALL.md").write_text("\n".join(text) + "\n", encoding="utf-8")
            report.update(status="PASS_ACTUAL_CORE_P2_400_EXACT_RECORD_COMPARISON", actual_steps=steps,
                          actual_round4_declarations=414, actual_p2_declarations=400, module_counts=P2_COUNTS,
                          exact_comparison_counts={field: sum(row["exact_fields"][field] for row in comparisons) for field in fields},
                          actual_source_modules_compared=len(source_rows), actual_export_source_object_modules=sum(row["source_captured_in_actual_export"] and row["actual_current_object_parts"] is not None for row in source_rows),
                          fixed_source_only_modules=[row["module"] for row in source_rows if not row["source_captured_in_actual_export"]],
                          actual_types_are_compiler_confirmed=True,
                          three_new_module_object_hashes_equal=all(row["producer_and_core_main_olean_hash_equal"] for row in source_rows if row["module"] in P2_COUNTS),
                          object_hash_difference_count=sum(row["producer_and_core_main_olean_hash_equal"] is False for row in source_rows),
                          no_type_record_difference=True, actual_export_elapsed_seconds=receipt["elapsed_seconds"],
                          actual_export_started_utc=receipt["started_utc"], actual_export_finished_utc=receipt["finished_utc"],
                          archive_sha256=ZIP_SHA, round4_receipt_member=members[0], actual_stdout_member=parent + "/stdout.log",
                          actual_declarations_member=parent + "/declarations.json", actual_declarations_sha256=sha(decl_raw),
                          actual_stdout_sha256=sha(stdout), actual_audit_object_sha256=audit_hash,
                          actual_five_names=KEYS,
                          job_external_bom_prefix_records=[{"name": name, "line": loc["line"], "external_log_prefix_hex": loc["external_log_prefix_hex"]}
                                                           for name, loc in job_locations.items() if loc["external_log_prefix_hex"].startswith("efbbbf")],
                          first_local_parser_failure_preserved="attempts/001-before-external-bom-prefix-support/LOCAL_REVIEW_FAILURE.json",
                          extra_supplier_scope_assumption_failure_preserved="attempts/002-before-explicit-snapshot-scope/LOCAL_REVIEW_FAILURE.json",
                          main_theorem_still_conditional=True, full_17572_mask_closed=False,
                          K_c_hLower_hUpper_closed=False,
                          original_evidence_files=[file_identity(CORE / n) for n in ["core-artifact.zip", "run.json", "jobs.json", "artifacts.json", "job.log"]]
                            + [file_identity(producer_path), file_identity(producer_receipt_path)])
    except Exception as error:
        report.update(status="FAILED_ACTUAL_P2_REVIEW", first_failure=f"{type(error).__name__}: {error}")
        raise
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        report["checks_passed"] = sum(c["passed"] for c in checks)
        report["checks_failed"] = sum(not c["passed"] for c in checks)
        write_json("CHECKS.json", checks)
        write_json("REVIEW_RECEIPT.json", report)
    print(json.dumps({k: report[k] for k in ["status", "source_commit", "actual_p2_declarations", "exact_comparison_counts", "actual_source_modules_compared", "checks_passed"]}, ensure_ascii=False))

if __name__ == "__main__":
    main()
