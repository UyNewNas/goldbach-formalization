#!/usr/bin/env python3
"""Read-only Part 0 reception of fixed P2 rows [4,64).
No Lean, Lake, kernel replay, cache preparation, network or Git mutation occurs.
Run from any directory; git objects and the already extracted immutable source/
CI evidence are read. Outputs go only to the selected existing evidence folder.
The owned archived Python validator is executed in its full fixed P2 snapshot,
because its 424-parent-file scope intentionally does not apply to a P0 merge.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import zipfile

HEAD = "101bb2291cd51f9717544ce477122fdd44eda44d"
PROOF = "f0c00f9ccce98e04af439321a92eb9fd0dd26203"
CI_HEAD = "e6d6d57323cc358cef060fb243ec386c13cb662d"
INTEGRATION = "28fd630ef7cc38eba86beb6c0ba123336b5d05f2"
OLD = "076473720210ee602e6e9735902e16bb6c5f1398"
PREFIX = "ImbalancedChen.Certificates."
NEW_COUNTS = {
    PREFIX + "PairedV2Batch4To64Data": 72,
    PREFIX + "PairedV2Batch4To64": 207,
    PREFIX + "PairedV2Prefix64": 121,
}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ZIP_SHA = "4f0b9cc1232226392515eda5ccf880a40241cc5afc8d6defcbac45206089d663"
RECEIPT_REL = "verification/part2/round3/batch4-to64/receipt.json"
KEYS = {
    "Batch4To64": ["rowOrdinal_range", "certificates_checked", "geometry_checked",
                  "certificate_inputs", "rowIntegral_eq_certificate", "rowIntegral_bounds",
                  "integral_semantics", "integral_bounds"],
    "Prefix64": ["source_ranges_disjoint", "source_ordinal_coverage", "rowIndices_injective",
                 "prefix_batch_indices_disjoint", "geometry_checked", "fibre_argument",
                 "integral_eq_parts", "integral_semantics", "lowerBound_eq_sum",
                 "upperBound_eq_sum", "integral_bounds"],
}

def require(cond, msg):
    if not cond:
        raise ValueError(msg)

def pairs(items):
    out = {}
    for k, v in items:
        require(k not in out, "duplicate JSON key " + k)
        out[k] = v
    return out

def read(path):
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def identity(raw):
    return {"bytes": len(raw), "sha256": sha(raw),
            "git_blob_sha1": hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()}

def git(repo, *args):
    return subprocess.check_output(["git", *args], cwd=repo)

def source_path(module):
    return module.replace(".", "/") + ".lean"

def tree(repo, rev):
    result = {}
    for row in git(repo, "ls-tree", "-rz", rev).split(b"\0"):
        if not row:
            continue
        metadata, name = row.split(b"\t", 1)
        mode, kind, blob = metadata.decode().split()
        require(kind == "blob" and mode in {"100644", "100755"}, "unexpected tree entry")
        result[name.decode()] = {"mode": mode, "blob": blob}
    return result

def output(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--git-repo", type=Path, required=True)
    parser.add_argument("--evidence-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    base = args.evidence_dir.resolve()
    source = base / "fixed-source"
    ci = base / "ci-artifact"
    repo = args.git_repo.resolve()
    started = datetime.now(timezone.utc).isoformat()
    before = tree(repo, HEAD)
    require(len(before) == 487, "wrong fixed source tree size")
    for path, item in before.items():
        require(identity((source / path).read_bytes())["git_blob_sha1"] == item["blob"],
                "fixed extracted blob differs: " + path)
    require(git(repo, "rev-parse", HEAD + "^").decode().strip() == CI_HEAD,
            "handoff parent is not exact successful CI commit")
    require(git(repo, "rev-parse", CI_HEAD + "^").decode().strip() == PROOF,
            "CI parent is not fixed proof commit")
    require(git(repo, "diff", "--name-only", CI_HEAD, HEAD).decode().splitlines()
            == ["docs/part2/ROUND3_HANDOFF.md"], "handoff changes more than its document")
    producer = read(source / RECEIPT_REL)
    require(producer["fixed_proof_source_commit"] == PROOF,
            "producer proof identity mismatch")
    require(producer["fixed_proof_source_tree"] ==
            git(repo, "rev-parse", PROOF + "^{tree}").decode().strip(), "proof tree mismatch")
    for path, expected in producer["source_inputs"].items():
        require(identity((source / path).read_bytes()) == expected, "producer source mismatch " + path)
        require(identity(git(repo, "show", PROOF + ":" + path)) == expected,
                "receipt input differs from fixed proof blob " + path)

    # This previously inspected and now Git-bound Python validator executes no
    # theorem prover or network command. Preserve first execution elsewhere;
    # this named output is the latest independent repeat of pure evidence checks.
    cmd = [sys.executable, "-B", "verification/part2/round3/batch4-to64/verify_acceptance.py"]
    tick = time.monotonic()
    proc = subprocess.run(cmd, cwd=source, capture_output=True)
    (base / "acceptance-recheck.stdout.log").write_bytes(proc.stdout)
    (base / "acceptance-recheck.stderr.log").write_bytes(proc.stderr)
    require(proc.returncode == 0, "fixed-source archived validator failed: " + proc.stderr.decode())
    received = json.loads(proc.stdout, object_pairs_hook=pairs)
    require(received["status"] == "PASS_ARCHIVED_BATCH4_TO64_ACCEPTANCE" and
            received["new_modules"] == 3 and received["new_owned_declarations"] == 400 and
            received["all_owned_declarations"] == 709 and
            received["unchanged_historical_compiler_records"] == 309 and
            received["new_lean_compile_or_replay_in_this_receiving_check"] is False,
            "unexpected archived validator result")
    replay_execution = {"command": cmd, "elapsed_seconds": round(time.monotonic() - tick, 3),
                        "exit_code": proc.returncode, "stdout_sha256": sha(proc.stdout),
                        "stderr_sha256": sha(proc.stderr), "new_lean_compile_or_replay": False}

    zip_raw = (base / "ci-artifact.zip").read_bytes()
    require(len(zip_raw) == 260451 and sha(zip_raw) == ZIP_SHA, "CI artifact bytes differ")
    with zipfile.ZipFile(base / "ci-artifact.zip") as archive:
        members = archive.namelist()
        require(len(members) == 41, "unexpected CI artifact inventory")
        for path in members:
            require(not Path(path).is_absolute() and ".." not in Path(path).parts,
                    "invalid artifact member")
            require((ci / path).read_bytes() == archive.read(path), "extracted artifact differs " + path)
    run = read(base / "ci-run.json")
    jobs = read(base / "ci-jobs.json")
    artifacts = read(base / "ci-artifacts.json")
    require(run["id"] == 38252572597 and run["head_sha"] == CI_HEAD and
            run["status"] == "completed" and run["conclusion"] == "success", "CI run is not successful")
    job, = jobs["jobs"]
    require(job["id"] == 114822365913 and job["head_sha"] == CI_HEAD and
            job["status"] == "completed" and job["conclusion"] == "success", "CI job mismatch")
    stages = {}
    stage_names = [
        "Explicit Part 2 build and strict individual elaboration",
        "Replay every new module with the bundled kernel checker",
        "Inventory all Part 2 declarations and their transitive axioms",
    ]
    for label in stage_names:
        step, = [x for x in job["steps"] if x["name"] == label]
        require(step["conclusion"] == "success" and step["status"] == "completed",
                "required CI gate not executed: " + label)
        start = datetime.fromisoformat(step["started_at"].replace("Z", "+00:00"))
        end = datetime.fromisoformat(step["completed_at"].replace("Z", "+00:00"))
        stages[label] = {"started_at": step["started_at"], "completed_at": step["completed_at"],
                         "elapsed_seconds": (end - start).total_seconds(), "conclusion": "success"}
    artifact, = artifacts["artifacts"]
    require(artifact["id"] == 11749278994 and artifact["digest"] == "sha256:" + ZIP_SHA and
            artifact["workflow_run"]["head_sha"] == CI_HEAD, "API artifact binding mismatch")
    prov = read(ci / "provenance.json")
    report = read(ci / "report.json")
    require(prov["head_commit"] == prov["event_commit"] == CI_HEAD and
            report["status"] == "PASSED" and report["declaration_count"] == 709, "CI report mismatch")
    require(len(prov["source_sha256"]) == 180 and len(prov["modules"]) == 12,
            "CI source/module census mismatch")
    for key, value in prov.items():
        require(report[key] == value, "CI report provenance differs")
    for path, expected in prov["source_sha256"].items():
        require(sha((source / path).read_bytes()) == expected, "CI/head input differs " + path)
        require(sha(git(repo, "show", CI_HEAD + ":" + path)) == expected,
                "CI fixed Git input differs " + path)
    manifest = json.loads(git(repo, "show", INTEGRATION + ":lake-manifest.json"))
    frozen_pins = {p["name"]: p["rev"] for p in manifest["packages"]}
    require(prov["dependency_pins"] == frozen_pins and len(frozen_pins) == 11, "dependency pin changed")
    for path in ["lean-toolchain", "lake-manifest.json", "lakefile.toml",
                 "docs/CURRENT_MANUSCRIPT_MAP.md", "docs/EXTERNAL_REUSE.md",
                 "ImbalancedChen/CurrentMainTheorem.lean", "ImbalancedChen/CurrentNumericalTransfer.lean"]:
        require((source / path).read_bytes() == git(repo, "show", INTEGRATION + ":" + path),
                "protected shared source differs " + path)
    require("commit 62eed1db4d67327ec8120be05f1a1b0847d74561" in (ci / "lean-version.log").read_text(),
            "wrong actually executed Lean")

    records = read(ci / "declarations.json")
    archive_records = read(source / "verification/part2/round3/batch4-to64/compiler-types.json")
    audit_lines = (ci / "axioms.log").read_text().splitlines()
    raw_records = [json.loads(line[len("P2_AUDIT_DECL "):], object_pairs_hook=pairs)
                   for line in audit_lines if line.startswith("P2_AUDIT_DECL ")]
    job_log = (base / "ci-job.log").read_text()
    require(len(job_log) == 2804436, "downloaded job log bytes/text changed")
    job_records = [json.loads(m[1], object_pairs_hook=pairs)
                   for line in job_log.splitlines()
                   if (m := re.search(r"P2_AUDIT_DECL (\{.*\})$", line))]
    require(records == archive_records == raw_records == job_records and len(records) == 709,
            "raw CI/producer compiler records differ")
    require(len({r["name"] for r in records}) == 709, "duplicate declarations")
    require([line for line in audit_lines if line.startswith("P2_AUDIT_COUNT ")]
            == ["P2_AUDIT_COUNT 709"], "raw audit count differs")
    counts = Counter(r["module"] for r in records)
    require(set(counts) == set(prov["modules"]) == set(producer["all_production_modules"]),
            "module inventories differ")
    require({m: counts[m] for m in NEW_COUNTS} == NEW_COUNTS, "new module counts differ")
    require(set().union(*(set(r["axioms"]) for r in records)) == AXIOMS,
            "transitive axiom union differs")
    for record in records:
        require(record["kind"] != "axiom" and set(record["axioms"]) <= AXIOMS,
                "new/transitive axiom")
        require(all(isinstance(record[f], str) and record[f] and
                    "⋯" not in record[f] and "..." not in record[f]
                    for f in ["type", "readable_type"]), "incomplete compiler output")
    audit_source = (source / "verification/part2/CertificateAudit.lean").read_text()
    for token in ["set_option pp.all true", "set_option pp.proofs true",
                  "set_option pp.deepTerms true", "info.isUnsafe", "info.isAxiom",
                  "collectAxioms name", "env.getModuleIdxFor?"]:
        require(token in audit_source, "audit no longer performs required check " + token)
    build_log = (ci / "build.log").read_text()
    strict_census = []
    for module in prov["modules"]:
        short = module.rsplit(".", 1)[1]
        require(re.search(r"Built " + re.escape(module) + r" \(", build_log),
                "missing actual explicit build " + module)
        require("replaying " + module in (ci / (short + "-replay.log")).read_text().splitlines(),
                "missing exact stock replay " + module)
        require((ci / (short + "-strict.log")).is_file(), "missing strict log")
        strict_census.append({"module": module,
                              "strict_log_bytes": (ci / (short + "-strict.log")).stat().st_size})
    require((ci / "outcomes.log").read_text().splitlines() ==
            ["build=success", "replay=success", "audit=success", "head_commit=" + CI_HEAD],
            "actual stage outcomes differ")

    # Independently reconstruct the project's dependency edges and same-object
    # compile/replay/audit lineage in the original archived production gates.
    entries = {x["module"]: x for x in producer["new_modules"] + producer["reused_modules"]}
    graph = {}
    for module in entries:
        imports = re.findall(r"(?m)^import\s+([^\n]+)$",
                             (source / source_path(module)).read_text())
        graph[module] = [x for line in imports for x in line.split() if x.startswith(PREFIX)]
    def closure(module):
        found = set()
        pending = list(graph[module])
        while pending:
            dep = pending.pop()
            require(dep in entries and dep != module, "unrecognized production dependency")
            if dep not in found:
                found.add(dep)
                pending.extend(graph[dep])
        return found
    gate_base = source / "verification/part2/round3/batch4-to64"
    checked_bindings = 0
    gate_summaries = []
    for entry in producer["new_modules"] + [producer["audit"]]:
        module = entry["module"]
        needed = closure(module) if module in entries else set(entries)
        for action in (["compile", "replay"] if module in entries else ["compile"]):
            gate = read(gate_base / entry[action]["receipt"])
            require(gate["returncode"] == 0 and gate["verification_passed"] is True and
                    gate["failures"] == [] and gate["metadata_adapter"] is False, "gate not accepted")
            require(gate["object_sha256_after"] == entry["object_sha256"], "wrong target object")
            for label in ["source_sha256", "shared_sha256", "local_producer_sha256"]:
                require(gate[label + "_before"] == gate[label + "_after"], "gate input changed")
            for imported in needed:
                suffix = "/" + imported.replace(".", "/") + ".olean"
                values = [v for p, v in gate["local_producer_sha256_before"].items() if p.endswith(suffix)]
                require(values == [entries[imported]["object_sha256"]], "wrong imported object " + imported)
                checked_bindings += 1
            if action == "compile":
                require(gate["trustLevel"] == 0 and gate["warningAsError"] is True,
                        "strict frontend gate relaxed")
                require(gate["source_sha256_before"] == entry["source_identity"]["sha256"],
                        "wrong compiled source")
            else:
                require(gate["object_sha256_before"] == gate["object_sha256_after"],
                        "replayed object changed")
                require(gate["command"][-2:] == ["--verbose", module] and
                        Path(gate["command"][0]).name == "leanchecker", "not stock replay")
            gate_summaries.append({"module": module, "action": action,
                                   "elapsed_seconds": gate["elapsed_seconds"],
                                   "source_sha256": entry["source_identity"]["sha256"],
                                   "object_sha256": entry["object_sha256"],
                                   "required_import_objects": len(needed), "exit_code": 0})
    for entry in producer["reused_modules"]:
        require(identity(git(repo, "show", INTEGRATION + ":" + entry["source"])) == entry["source_identity"],
                "previously integrated production dependency changed")

    new_records = [r for r in records if r["module"] in NEW_COUNTS]
    output(base / "NEW_400_COMPLETE_TYPES.json", new_records)
    by_name = {r["name"]: r for r in records}
    keys = [by_name["ImbalancedChen.Certificates.PairedV2." + ns + "." + name]
            for ns, names in KEYS.items() for name in names]
    output(base / "KEY_INTERFACES_COMPILER.json", keys)
    md = ["# P2 本批关键完整接口", "", "以下为实际编译器输出，与固定生产者原始 log 和 CI 原始 log 逐条相等。"
          "完整 pp.all 字段保留在同名 JSON；readable_type 保留全部量词和前提。", ""]
    for record in keys:
        md += ["## " + record["name"], "", "```lean", record["name"] + " :",
               record["readable_type"], "```", "",
               "公理依赖：" + ", ".join(record["axioms"]), ""]
    (base / "KEY_INTERFACES_COMPILER.md").write_text("\n".join(md))

    # Only files needed by the new production declarations are mandatory writes.
    # The owner tools and original evidence remain independently source-bound.
    install = []
    for entry in producer["new_modules"]:
        install.append({"path": entry["source"], "source_commit": PROOF,
                        "role": "required production addition", "identity": entry["source_identity"],
                        "owned_declarations": NEW_COUNTS[entry["module"]]})
    for path in ["verification/part2/generate_paired_prefix.py",
                 "verification/part2/CertificateAudit.lean"]:
        install.append({"path": path, "source_commit": PROOF,
                        "role": "optional owner tooling update; P0 chooses explicit invocation",
                        "identity": identity((source / path).read_bytes())})
    output(base / "MINIMAL_RECEIVE_FILES.json", {
        "source_head": HEAD, "proof_commit": PROOF, "validated_ci_commit": CI_HEAD,
        "integration_start": INTEGRATION, "files": install,
        "unchanged_production_dependencies": producer["reused_modules"],
        "archive_only": ["verification/part2/check.sh", ".github/workflows/part2-certificates.yml",
                         "docs/part2/ROUND2_HANDOFF.md", "verification/part2/round2/prefix4/receipt.json"],
        "new_evidence_directory": "verification/part2/round3",
        "new_handoff": "docs/part2/ROUND3_HANDOFF.md",
        "archived_receiver_note": "The original receiver requires the full fixed P2 source extraction. "
            "Do not replace its frozen 424-parent-file checks with a modified P0 root.",
        "root_import_owner": "Part0 only",
    })
    for path, item in before.items():
        require(identity((source / path).read_bytes())["git_blob_sha1"] == item["blob"],
                "fixed source changed during intake " + path)
    result = {
        "status": "PASS_FIXED_P2_SOURCE_ORIGINAL_OBJECT_LINEAGE_AND_REAL_CI",
        "observed_utc": started, "source_head": HEAD, "fixed_proof_commit": PROOF,
        "fixed_proof_tree": producer["fixed_proof_source_tree"], "source_tree": git(repo, "rev-parse", HEAD+"^{tree}").decode().strip(),
        "integration_start": INTEGRATION, "fixed_source_blob_count": len(before),
        "ci_source_input_count": 180, "ci_source_comparisons": 360,
        "new_modules": [{"module": e["module"], "source": e["source"],
                         "source_identity": e["source_identity"], "object_sha256": e["object_sha256"],
                         "declarations": NEW_COUNTS[e["module"]]} for e in producer["new_modules"]],
        "new_owned_declarations": 400, "all_p2_owned_declarations": 709,
        "unchanged_prior_declarations": 309, "all_types_actual_pp_all": True,
        "raw_producer_ci_artifact_and_ci_job_type_records_equal": True,
        "transitive_axiom_union": sorted(AXIOMS), "production_dependency_graph": graph,
        "independently_checked_import_object_bindings": checked_bindings,
        "original_gates": gate_summaries, "archived_python_receiving_check": replay_execution,
        "ci": {"head_sha": CI_HEAD, "run_id": 38252572597, "job_id": 114822365913,
               "run_attempt": 1, "status": "completed", "conclusion": "success",
               "artifact_id": artifact["id"], "artifact_sha256": ZIP_SHA,
               "artifact_bytes": len(zip_raw), "artifact_members": len(members),
               "stage_execution": stages, "explicit_build_module_count": 12,
               "strict_module_count": 12, "stock_replay_module_count": 12,
               "strict_logs": strict_census, "job_log_sha256": sha((base/"ci-job.log").read_bytes())},
        "scope": producer["scope"], "new_lean_or_ci_execution": False,
        "production_objects_archived_as_bytes": False,
        "object_claim_scope": "Original producer compile/replay/audit hashes and actual input lineage; "
              "CI independently compiled/replayed/audited the same fixed sources. "
              "The CI artifact does not carry all object bytes.",
        "unclosed_inputs": ["E0 original rows [64,6091)", "E1 rows [6091,17572)",
                           "saved-floor real semantic estimator", "full geometric union/no-overlap identity",
                           "historical parent permission and actual count-to-integral identity",
                           "full K and c analytical proofs", "hLower", "hUpper"],
        "receivers": ["Part1", "Part2", "Part5", "Part0"],
        "part4_upper_certificate_scope_extended": False,
        "p0_production_repairs": [],
    }
    output(base / "P2_INTAKE_RECEIPT.json", result)
    print(json.dumps({k: result[k] for k in ["status", "source_head", "fixed_proof_commit",
                     "new_owned_declarations", "all_p2_owned_declarations",
                     "independently_checked_import_object_bindings", "new_lean_or_ci_execution"]},
                     ensure_ascii=False, indent=2))

if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        raise SystemExit("FAIL_P2_FIXED_INTAKE: " + str(exc)) from exc

