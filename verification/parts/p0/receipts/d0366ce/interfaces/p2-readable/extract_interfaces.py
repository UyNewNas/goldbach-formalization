#!/usr/bin/env python3
"""Extract existing P2 types and source values; no Lean, CI, network or proof run."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re


OUT = Path(__file__).resolve().parent
INTAKE = OUT.parents[1] / "p2-intake"
PREFIX = "ImbalancedChen.Certificates.PairedV2.Prefix64."
SHORT_NAMES = ["integral_semantics", "integral_bounds", "integral_eq_parts",
               "source_ordinal_coverage", "rowIndices_injective"]
NAMES = [PREFIX + name for name in SHORT_NAMES]
PROOF_SHA = "f0c00f9ccce98e04af439321a92eb9fd0dd26203"
HANDOFF_SHA = "101bb2291cd51f9717544ce477122fdd44eda44d"
CI_SHA = "e6d6d57323cc358cef060fb243ec386c13cb662d"
CORE_SHA = "d0366ce64272e81faf6166a8a90050f56b328d38"
PRODUCER_DIR = INTAKE / "fixed-source/verification/part2/round3/batch4-to64"
PRODUCER_LOG = PRODUCER_DIR / "gates/20261012T124344374925Z-compile-verification.part2.CertificateAudit.log"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def save_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def identity(path: Path) -> dict:
    data = path.read_bytes()
    return {"absolute_path": str(path), "bytes": len(data), "sha256": digest(data)}


def selected_records(path: Path) -> dict[str, dict]:
    records = json.loads(path.read_bytes())
    result = {record["name"]: record for record in records if record["name"] in NAMES}
    assert len(result) == len(NAMES)
    return result


def selected_log_records(path: Path, label: str) -> tuple[dict, list[dict]]:
    result, locations, retained = {}, [], []
    offset = 0
    for number, line in enumerate(path.read_bytes().splitlines(keepends=True), 1):
        if line.startswith(b"P2_AUDIT_DECL "):
            record = json.loads(line[len(b"P2_AUDIT_DECL "):])
            if record["name"] in NAMES:
                assert record["name"] not in result
                result[record["name"]] = record
                locations.append({"name": record["name"], "original_line": number,
                                  "original_byte_offset": offset, "original_line_bytes": len(line),
                                  "original_line_sha256": digest(line)})
                retained.append(line)
        offset += len(line)
    target = OUT / "original-log-lines" / (label + ".log")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(b"".join(retained))
    assert set(result) == set(NAMES)
    return result, locations


def source_head(source: str, short: str) -> dict:
    match = re.search(r"(?m)^theorem " + re.escape(short) + r"\b", source)
    assert match
    finish = source.index(":=", match.end())
    return {"name": PREFIX + short, "source_line": source.count("\n", 0, match.start()) + 1,
            "source_statement": source[match.start():finish].rstrip(),
            "kind": "EXACT_SOURCE_HEADER_NOT_COMPILER_OUTPUT"}


def source_rows(source: str, size: int, ordinal_start: int) -> list[dict]:
    indices_body = source.split("def rowIndices", 1)[1].split("def rowZ", 1)[0]
    z_body = source.split("def rowZ", 1)[1].split("def rowOrdinal", 1)[0]
    indices = re.findall(r"\| (\d+|_) => \((\d+), (\d+)\)", indices_body)
    zs = re.findall(r"\| (\d+|_) => (\d+) / (\d+)", z_body)
    assert len(indices) == len(zs) == size
    rows = []
    for local, (pair, z) in enumerate(zip(indices, zs)):
        key, t, u = pair
        zkey, numerator, denominator = z
        assert key == zkey and key in (str(local), "_")
        assert key != "_" or local == size - 1
        rows.append({"source_ordinal": ordinal_start + local, "local_index": local,
                     "supplier": "Prefix4" if ordinal_start == 0 else "Batch4To64",
                     "t_index": int(t), "u_index": int(u),
                     "rowZ_source_numerator": int(numerator), "rowZ_source_denominator": int(denominator),
                     "kind": "EXACT_SOURCE_TABLE_VALUE_NOT_NEW_NUMERICAL_CERTIFICATE"})
    return rows


def main() -> None:
    producer_types = PRODUCER_DIR / "compiler-types.json"
    ci_types = INTAKE / "ci-artifact/declarations.json"
    selected = selected_records(producer_types)
    for path in [ci_types, INTAKE / "NEW_400_COMPLETE_TYPES.json", INTAKE / "KEY_INTERFACES_COMPILER.json"]:
        assert selected_records(path) == selected
    producer_log, producer_locations = selected_log_records(PRODUCER_LOG, "producer-audit-selected-original-lines")
    ci_log, ci_locations = selected_log_records(INTAKE / "ci-artifact/axioms.log", "ci-audit-selected-original-lines")
    assert producer_log == ci_log == selected
    assert all(record["kind"] == "theorem" for record in selected.values())
    pp_all = OUT / "actual-producer-ppall"
    pp_all.mkdir(parents=True, exist_ok=True)
    record_hashes = []
    for short, name in zip(SHORT_NAMES, NAMES):
        record = selected[name]
        assert not any(token in record["type"] for token in ["⋯", "…", "<proof>"])
        raw_type = record["type"].encode("utf-8")
        (pp_all / (short + ".txt")).write_bytes(raw_type)
        record_hashes.append({"name": name, "pp_all_bytes": len(raw_type), "pp_all_sha256": digest(raw_type),
                              "axioms": record["axioms"], "pp_all_file": "actual-producer-ppall/" + short + ".txt"})
    save_json(OUT / "ACTUAL_PRODUCER_COMPLETE_RECORDS.json", [selected[name] for name in NAMES])
    lines = ["# 已接受 P2 producer 的完整 pp.all 原文", "",
             "来源为 f0c00f9ccce98e04af439321a92eb9fd0dd26203 的生产源码及已接受生产记录，",
             "并与 e6d6d57323cc358cef060fb243ec386c13cb662d 的实际 P2 CI 原始 audit 记录相同。",
             "本文件不是 d0366ce 新 core 类型导出。五份 .txt 保留各 type 字段的 UTF-8 原字节，不另添换行。", ""]
    for name in NAMES:
        lines += ["## " + name, "", "```lean", selected[name]["type"], "```", "",
                  "原始传递公理：`" + "`, `".join(selected[name]["axioms"]) + "`。", ""]
    (OUT / "COMPLETE_PRODUCER_PP_ALL.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    producer_receipt = json.loads((PRODUCER_DIR / "receipt.json").read_bytes())
    source_paths = ["PairedV2Prefix64.lean", "PairedV2Data.lean", "PairedV2Prefix4Data.lean",
                    "PairedV2Prefix4.lean", "PairedV2Batch4To64Data.lean", "PairedV2Batch4To64.lean",
                    "PairedFibreIntegral.lean"]
    source_identities = []
    for short_path in source_paths:
        relative = "ImbalancedChen/Certificates/" + short_path
        origin = INTAKE / "fixed-source" / relative
        data = origin.read_bytes()
        assert digest(data) == producer_receipt["source_inputs"][relative]["sha256"]
        target = OUT / "fixed-source" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        source_identities.append({"path": "fixed-source/" + relative, "repository_path": relative,
                                  "proof_source_commit": PROOF_SHA, **identity(origin)})
    prefix64 = (INTAKE / "fixed-source/ImbalancedChen/Certificates/PairedV2Prefix64.lean").read_text()
    save_json(OUT / "EXACT_SOURCE_STATEMENTS.json", [source_head(prefix64, short) for short in SHORT_NAMES])
    prefix4 = (INTAKE / "fixed-source/ImbalancedChen/Certificates/PairedV2Prefix4Data.lean").read_text()
    batch60 = (INTAKE / "fixed-source/ImbalancedChen/Certificates/PairedV2Batch4To64Data.lean").read_text()
    save_json(OUT / "ROWS_0_63_SOURCE_VALUES.json", {
        "kind": "SOURCE_TABLE_EXTRACTION_ONLY", "compiler_type_export": False,
        "source_mask_version": "same-mask-v2", "source_manuscript_commit": "ba6ec11d800eccc54406490631895e174de85766",
        "rows": source_rows(prefix4, 4, 0) + source_rows(batch60, 60, 4),
    })
    original_paths = [producer_types, PRODUCER_LOG, ci_types, INTAKE / "ci-artifact/axioms.log",
                      INTAKE / "ci-artifact.zip", INTAKE / "P2_INTAKE_RECEIPT.json",
                      INTAKE / "KEY_INTERFACES_COMPILER.json", INTAKE / "NEW_400_COMPLETE_TYPES.json",
                      INTAKE / "KEY_TYPES_SELECTION.md"]
    save_json(OUT / "PROVENANCE.json", {
        "scope": "EXTRACTION_OF_ACCEPTED_P2_PRODUCER_TYPES_NO_NEW_PROOF_EXECUTION",
        "producer_proof_source_commit": PROOF_SHA, "retrieved_fixed_handoff_commit": HANDOFF_SHA,
        "accepted_ci_source_commit": CI_SHA, "accepted_ci_run": 38252572597, "accepted_ci_job": 114822365913,
        "accepted_ci_artifact_id": 11749278994,
        "pending_core_source_commit": CORE_SHA, "pending_core_run": 38289734671,
        "new_core_full_type_export_observed_by_this_extraction": False,
        "new_core_type_confirmation_claimed": False, "lean_ci_network_proof_execution": False,
        "source_statement_kind": "EXACT_SOURCE_HEADER_NOT_COMPILER_OUTPUT",
        "pp_all_kind": "UNCHANGED_ACTUAL_PRODUCER_COMPILER_TYPE_UTF8",
        "five_records_equal_in_all_original_sources": True,
        "type_fields": record_hashes, "producer_log_locations": producer_locations,
        "ci_log_locations": ci_locations, "original_evidence_files": [identity(path) for path in original_paths],
        "fixed_source_files": source_identities,
        "formal_scope": {"adopted_rows": 64, "complete_adopted_mask_rows": 17572,
                         "old_rows": "[0,4)", "new_rows": "[4,64)",
                         "remaining_E0": "[64,6091)", "remaining_E1": "[6091,17572)",
                         "full_geometric_union_or_history_closed": False,
                         "full_actual_count_to_integral_or_error_suppliers_closed": False,
                         "K_c_analytic_or_hLower_hUpper_closed": False},
    })
    print(json.dumps({"scope": "PURE_EXISTING_RECORD_EXTRACTION", "selected_records": len(selected),
                      "raw_log_sources_compared": 2, "fixed_source_files": len(source_identities),
                      "new_core_type_confirmation_claimed": False, "output": str(OUT)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
