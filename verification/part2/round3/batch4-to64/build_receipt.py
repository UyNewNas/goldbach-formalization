#!/usr/bin/env python3
"""Assemble source-bound receipts from completed stock-tool executions.

This archives evidence; it neither runs Lean nor proves an integral.
The independent verify_acceptance.py rejects incomplete or inconsistent gates.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import shutil

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[3]
NEW = ["ImbalancedChen.Certificates." + name for name in
       ["PairedV2Batch4To64Data", "PairedV2Batch4To64", "PairedV2Prefix64"]]
PREVIOUS = "verification/part2/round2/prefix4/receipt.json"
PARENT = "076473720210ee602e6e9735902e16bb6c5f1398"
CHANGED = ["verification/part2/generate_paired_prefix.py",
           "verification/part2/CertificateAudit.lean", "verification/part2/check.sh",
           ".github/workflows/part2-certificates.yml"]


def read(path):
    return json.loads(path.read_text())


def identity(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
            "git_blob_sha1": hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--proof-commit")
    parser.add_argument("--proof-tree")
    args = parser.parse_args()
    executions = {}
    excluded = set(read(BASE / "scheduling-rejections.json")["excluded_receipt_stems"])
    for receipt in sorted(args.runtime.glob("20*.json")):
        item = read(receipt)
        if item.get("module") not in NEW + ["verification.part2.CertificateAudit"]:
            continue
        accepted = item["verification_passed"] and receipt.stem not in excluded
        target = BASE / ("gates" if accepted else "attempts")
        target.mkdir(exist_ok=True)
        for path in [receipt, receipt.with_suffix(".log")]:
            shutil.copyfile(path, target / path.name)
        if accepted:
            executions[item["module"], item["action"]] = (item, target / receipt.name)

    def entry(module, actions):
        source = module.replace(".", "/") + ".lean"
        result = {"module": module, "source": source,
                  "source_identity": identity(ROOT / source)}
        for action in actions:
            item, path = executions[module, action]
            assert item["returncode"] == 0 and not item["failures"]
            if action == "compile":
                assert item["source_sha256_after"] == result["source_identity"]["sha256"]
            if "object_sha256" in result:
                assert result["object_sha256"] == item["object_sha256_after"]
            result["object_sha256"] = item["object_sha256_after"]
            result[action] = {"receipt": str(path.relative_to(BASE)),
                              "log": str(path.with_suffix(".log").relative_to(BASE)),
                              "exit_code": item["returncode"],
                              "elapsed_seconds": item["elapsed_seconds"],
                              "child_maxrss_kib": item["child_maxrss_kib"]}
        return result

    previous = read(ROOT / PREVIOUS)
    upstream = read(ROOT / previous["upstream_acceptance"])
    reused = [{"module": item["module"], "source": item["module"].replace(".", "/") + ".lean",
               "source_identity": identity(ROOT / (item["module"].replace(".", "/") + ".lean")),
               "object_sha256": item["olean_sha256"]} for item in upstream["modules"]]
    reused += [{key: item[key] for key in ["module", "source", "source_identity", "object_sha256"]}
               for item in previous["new_modules"]]
    new = [entry(module, ["compile", "replay"]) for module in NEW]
    audit = entry("verification.part2.CertificateAudit", ["compile"])
    lines = (BASE / audit["compile"]["log"]).read_text().splitlines()
    records = [json.loads(line.removeprefix("P2_AUDIT_DECL ")) for line in lines
               if line.startswith("P2_AUDIT_DECL ")]
    counts = [json.loads(line.removeprefix("P2_AUDIT_MODULE ")) for line in lines
              if line.startswith("P2_AUDIT_MODULE ")]
    totals = [int(line.removeprefix("P2_AUDIT_COUNT ")) for line in lines
              if line.startswith("P2_AUDIT_COUNT ")]
    assert totals == [len(records)] and len({r["name"] for r in records}) == len(records)
    counter = Counter(r["module"] for r in records)
    modules = previous["all_production_modules"] + NEW
    assert {item["module"] for item in counts} == set(modules)
    assert all(counter[item["module"]] == item["count"] > 0 for item in counts)
    current = {r["name"]: r for r in records}
    old_types = read(ROOT / "verification/part2/round2/prefix4/compiler-types.json")
    assert all(current[r["name"]] == r for r in old_types)
    assert len(old_types) == 309
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert all(set(r["axioms"]) <= allowed and r["kind"] != "axiom" for r in records)
    assert all(r[key] and "⋯" not in r[key] for r in records for key in ["type", "readable_type"])
    audit.update(module_counts=counts, declaration_count=len(records),
                 declaring_module_inventory=True, includes_private_and_generated=True,
                 unsafe_or_new_axiom_declarations=0,
                 transitive_axiom_union=sorted({ax for r in records for ax in r["axioms"]}),
                 previous_309_records_identical=True)
    (BASE / "compiler-types.json").write_text(json.dumps(records, indent=2) + "\n")
    (BASE / "compiler-readable-types.txt").write_text("\n\n".join(
        f"[{r['module']}]\n{r['name']} :\n{r['readable_type']}\n"
        f"transitive_axioms={','.join(r['axioms'])}" for r in records) + "\n")
    selected = {"ImbalancedChen.Certificates.PairedIntegralCertificate.sum_check_sound"}
    selected |= {"ImbalancedChen.Certificates.PairedV2.Batch4To64." + name for name in
                 ["rowOrdinal_range", "certificates_checked", "geometry_checked", "certificate_inputs",
                  "rowIntegral_eq_certificate", "rowIntegral_bounds", "integral_semantics", "integral_bounds"]}
    selected |= {"ImbalancedChen.Certificates.PairedV2.Prefix64." + name for name in
                 ["source_ranges_disjoint", "source_ordinal_coverage", "rowOrdinal_eq_val",
                  "rowIndices_injective", "prefix_batch_indices_disjoint", "integral_eq_parts",
                  "integral_semantics", "integral_bounds"]}
    assert selected <= set(current)
    (BASE / "key-theorem-types.txt").write_text("\n\n".join(
        f"{r['name']} :\n{r['readable_type']}\ntransitive_axioms={','.join(r['axioms'])}"
        for r in records if r["name"] in selected) + "\n")
    (BASE / "axiom-counts.json").write_text(json.dumps(audit, indent=2) + "\n")

    generated = read(BASE / "generated-report.json")
    ledger = read(BASE / "append-ledger.json")
    source_paths = [module.replace(".", "/") + ".lean" for module in modules] + CHANGED
    source_paths += list(previous["source_inputs"]) + ["verification/verify_variable_envelope_boxes.py"]
    source_paths += ["lean-toolchain", "lake-manifest.json", "lakefile.toml", PREVIOUS,
                     "verification/part2/import_paired_v2.py",
                     "verification/part2/data/corpus-renewal-paired-certificate-v2-20261010.json",
                     "verification/part2/round2/upstream/UPSTREAM_ACCEPTANCE.json",
                     "verification/part2/round2/upstream/verify_upstream_acceptance.py",
                     "verification/part2/round3/batch4-to64/verify_acceptance.py",
                     "verification/part2/round3/batch4-to64/build_receipt.py"]
    source_paths += [str(p.relative_to(ROOT)) for p in sorted((ROOT / "verification/part2/round3/runtime").rglob("*"))
                     if p.is_file() and "__pycache__" not in p.parts]
    report = dict(schema="part2-e0-append-acceptance-v1",
                  status="PASS_STRICT_TRUST0_STOCK_REPLAY_OWNED_AUDIT",
                  parent_branch_commit=PARENT,
                  proof_common_baseline="1a80c1bcce67886f699d097fc37fd245cd3620bf",
                  manuscript_commit="ba6ec11d800eccc54406490631895e174de85766",
                  new_modules=new, reused_modules=reused, audit=audit,
                  all_production_modules=modules, previous_acceptance=PREVIOUS,
                  previous_acceptance_identity=identity(ROOT / PREVIOUS),
                  previous_fixed_proof_commit="6acf61cc28f227a9154363f2347c386ec01dffb0",
                  historical_scope=dict(parent_commit=PARENT, parent_sources="parent-source-identities.json",
                                        pre_mutation_receipt="prefix4-before-mutation.json",
                                        pre_mutation_log="prefix4-before-mutation.log",
                                        allowed_changed_parent_paths=CHANGED),
                  new_strict_compile_count=3, new_stock_kernel_replay_count=3,
                  reused_module_count=9, new_owned_declaration_count=len(records)-309,
                  audit_all_owned_declaration_count=len(records),
                  execution_entry="UNCHANGED_OFFICIAL_LAKE_Lean.Elab.runFrontend_TRUST_ZERO",
                  metadata_adapter=False, kernel_replay="STOCK_LEANCHECKER_EACH_NEW_MODULE_NOT_FRESH_IMPORT_CLOSURE",
                  full_lake_build=False, full_historical_mask_certified=False,
                  hLower_supplier=False, hUpper_supplier=False,
                  scope=dict(group="E0", previous_zero_based_ordinals=list(range(4)),
                             original_zero_based_ordinals=list(range(4,64)),
                             cumulative_zero_based_ordinals=list(range(64)), start=4, count=60, end=64,
                             lower=generated["candidate_lower"], upper=generated["candidate_upper"],
                             cumulative_lower=ledger["prefix64"]["lower"],
                             cumulative_upper=ledger["prefix64"]["upper"],
                             global_union_integral_identity=False, arithmetic_parent_license=False,
                             original_Q160_enclosures_used_as_proof_premises=False,
                             first_cell_added_again=False),
                  source_inputs={name: identity(ROOT / name) for name in sorted(set(source_paths))},
                  archive_files={str(p.relative_to(BASE)): identity(p) for p in sorted(BASE.rglob("*"))
                                 if p.is_file() and p.name != "receipt.json"
                                 and "__pycache__" not in p.parts and p.suffix != ".py"})
    if args.proof_commit:
        report["fixed_proof_source_commit"] = args.proof_commit
        report["fixed_proof_source_tree"] = args.proof_tree
    (BASE / "receipt.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "new_modules": 3, "reused_modules": 9,
                      "all_owned_declarations": len(records), "new_owned_declarations": len(records)-309,
                      "module_counts": counts}, indent=2))


if __name__ == "__main__":
    main()
