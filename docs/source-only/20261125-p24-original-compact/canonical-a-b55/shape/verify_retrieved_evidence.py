"""Local verification of complete, bounded read-only evidence transfers.

This verifies saved transport and diagnostic records. It does not run Lean,
replay proof objects, or award compilation/owned-audit/P2 acceptance credit.
"""
from pathlib import Path
import base64
import gzip
import hashlib
import json


ROOT = Path(__file__).resolve().parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def info(path):
    raw = path.read_bytes()
    return {"path": str(path), "bytes": len(raw), "sha256": sha(raw)}


def output_from_pages(path, expected_bytes):
    pages = json.loads(path.read_bytes())
    offset = 0
    parts = []
    for index, page in enumerate(pages):
        assert page["offset"] == offset
        assert not page["log_truncated"] and page["discarded_bytes"] == 0
        raw = base64.b64decode(page["output_base64"], validate=True)
        assert len(raw) <= 65536 and len(raw) == page["next_offset"] - offset
        offset = page["next_offset"]
        assert page["eof"] == (index == len(pages) - 1)
        parts.append(raw)
    raw = b"".join(parts)
    assert len(raw) == expected_bytes == offset
    return raw


def main():
    descriptor = json.loads((ROOT / "remote-files-descriptor.json").read_bytes())
    assert descriptor["all_original_bytes_unchanged"] and not descriptor["remote_writes"]
    assert descriptor["source_pin_of_evidence"] == "b55fa93d39e6a4ddf2abd37b9b8481078e329f70"
    metadata_task = json.loads((ROOT / "metadata-task-status.json").read_bytes())
    assert metadata_task["status"] == "succeeded" and metadata_task["exit_code"] == 0
    assert not metadata_task["log_truncated"] and metadata_task["log_discarded_bytes"] == 0
    assert output_from_pages(ROOT / "metadata-output-pages.json", metadata_task["log_bytes"]) == (ROOT / "metadata-task.log").read_bytes()

    blocks = []
    retrievals = []
    offset = 0
    for index in range(8):
        prefix = ROOT / "chunks" / f"chunk-{index:02d}"
        status = json.loads(prefix.with_name(prefix.name + "-task-status.json").read_bytes())
        submission = json.loads(prefix.with_name(prefix.name + "-submission.json").read_bytes())
        assert status["task_id"] == submission["job_id"]
        assert status["status"] == "succeeded" and status["exit_code"] == 0
        assert not status["log_truncated"] and status["log_discarded_bytes"] == 0
        output = output_from_pages(prefix.with_name(prefix.name + "-output-pages.json"), status["log_bytes"])
        assert output == prefix.with_name(prefix.name + "-task.log").read_bytes()
        assert output.startswith(b"P24_A_SHAPE_CHUNK ") and output.endswith(b"\n")
        record = json.loads(output[len(b"P24_A_SHAPE_CHUNK "):])
        raw = base64.b64decode(record.pop("data"), validate=True)
        assert record == json.loads(prefix.with_name(prefix.name + "-metadata.json").read_bytes())
        assert raw == prefix.with_suffix(".bin").read_bytes()
        assert record["chunk_index"] == index and record["chunk_count"] == 8
        assert record["offset"] == offset and record["end"] == offset + len(raw)
        assert 0 < len(raw) <= 1000000 and record["raw_bytes"] == len(raw)
        assert sha(raw) == record["chunk_sha256"]
        assert record["file_bytes"] == 7577341
        assert record["file_sha256"] == "709c2f0d26d4481f2845edd7d2726e677842eda447f455297178dab7259a25d0"
        assert record["all_original_bytes_unchanged"] and not record["remote_writes"]
        assert not record["proof_or_audit_executed"] and not record["canonical_credit"]
        offset += len(raw)
        blocks.append(raw)
        retrievals.append({"chunk": index, "task": status, "data": record})
    archive = b"".join(blocks)
    assert archive == (ROOT / "blocks.stdout.log.gz").read_bytes()
    assert len(archive) == 7577341
    assert sha(archive) == "709c2f0d26d4481f2845edd7d2726e677842eda447f455297178dab7259a25d0"

    for name, expected in descriptor["files"].items():
        raw = (ROOT / name).read_bytes()
        assert len(raw) == expected["bytes"] and sha(raw) == expected["sha256"]

    diagnostic = json.loads((ROOT / "shape-diagnostic.json").read_bytes())
    assert diagnostic["source_pin"] == descriptor["source_pin_of_evidence"]
    assert diagnostic["wrapper_exit_code"] == 0 and diagnostic["canonical_A_shape_checks_passed"]
    assert all(value is True for value in diagnostic["postchecks"].values())
    assert not diagnostic["canonical_audit_credit"] and not diagnostic["full324_credit"]
    assert not diagnostic["independent_replay_performed"] and not diagnostic["proof_generator_run"]
    capture = diagnostic["shape_capture"]
    stdout = gzip.decompress(archive)
    assert len(stdout) == capture["stdout_bytes"] == 32377535
    assert sha(stdout) == capture["stdout_sha256"] == "17da353c642b87270d40ccaf19803c462a1afc3ed88702cbb21ae8e8b9c2a033"
    assert capture["read_to_eof"] and capture["complete_successful_template_stdout"] and capture["lean_exit_code"] == 0

    lines = stdout.splitlines()
    assert len(lines) == 2049
    emitted = []
    for line in lines[:-1]:
        assert line.startswith(b"P24_Q80_BLOCK ")
        row = json.loads(line[len(b"P24_Q80_BLOCK "):])
        assert row["shape_checks_passed"] and row["sixty_four_fact_balanced_and"]
        assert row["theorem"] and row["private"] and not row["unsafe"] and not row["partial"] and not row["axiom"]
        assert row["balanced_and_depth"] == 6 and row["fact_count"] == len(row["facts"]) == 64
        indices = row["indices"]
        assert len(indices) == 64 and indices == list(range(indices[0], indices[0] + 64))
        assert indices[0] in range(32769, 163778, 64)
        assert [fact["index"] for fact in row["facts"]] == indices
        for fact in row["facts"]:
            assert fact["grid"] == 16384 and fact["completed"] == fact["index"]
            assert fact["exact_source_node_equality"] and len(fact["four_int_normal_form_decimal"]) == 4
            assert all(str(int(value)) == value for value in fact["four_int_normal_form_decimal"])
        emitted.append(row)
    assert lines[-1].startswith(b"P24_Q80_BLOCK_SUMMARY ")
    summary = json.loads(lines[-1][len(b"P24_Q80_BLOCK_SUMMARY "):])
    assert summary == json.loads(gzip.decompress((ROOT / "complete-block-summary.json.gz").read_bytes()))
    assert summary["indices"] == [index for row in emitted for index in row["indices"]]
    assert len(set(summary["indices"])) == 131072
    assert sorted(summary["indices"]) == list(range(32769, 163841))
    assert summary["total_fact_count"] == 131072 and summary["owned_block_count"] == 2048
    assert summary["shape_checks_passed"] and summary["public_entry_checks_passed"]
    assert summary["diagnostic_only"] and not summary["P2_acceptance_credit"]
    linked = json.loads(gzip.decompress((ROOT / "complete-block-owned-link.json.gz").read_bytes()))
    assert len(linked) == 2048 and len({row["name"] for row in linked}) == 2048
    assert {row["name"] for row in linked} == {row["name"] for row in emitted}
    assert sum(row["printed_type_utf8_bytes"] for row in linked) == diagnostic["total_block_printed_type_utf8_bytes"] == 158423464
    assert all(set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for row in linked)
    for name, field in [("complete-block-summary.json.gz", "complete_block_summary"),
                        ("complete-block-owned-link.json.gz", "complete_block_owned_link")]:
        assert descriptor["files"][name] == diagnostic[field]
    assert descriptor["files"]["InspectBlocks.lean"] == diagnostic["inspector_source"]

    original_status = json.loads((ROOT / "original-shape-task-status.json").read_bytes())
    assert original_status["task_id"] == descriptor["original_shape_task_id"] == "af141e9e53ef4fd591f2e320debedb5e"
    assert original_status["status"] == "succeeded" and original_status["exit_code"] == 0
    assert not original_status["log_truncated"] and original_status["log_discarded_bytes"] == 0
    assert output_from_pages(ROOT / "original-shape-task-output-pages.json", original_status["log_bytes"]) == (ROOT / "original-shape-task.log").read_bytes()

    result = {
        "schema": 1, "status": "passed", "scope": "complete local transport and diagnostic-evidence verification",
        "source_pin_of_evidence": descriptor["source_pin_of_evidence"],
        "original_shape_task": original_status,
        "original_shape_record_passed": True,
        "all_five_artifacts_exact_bytes_and_sha256_verified": True,
        "all_pages_contiguous_with_terminal_eof_and_zero_discarded_bytes": True,
        "gzip_complete_decompression_verified": True,
        "raw_stdout_bytes": len(stdout), "raw_stdout_sha256": sha(stdout),
        "original_order_of_all_emitted_block_records_preserved": True,
        "unique_block_count": len(emitted), "fact_count": len(summary["indices"]),
        "first_index": min(summary["indices"]), "last_index": max(summary["indices"]),
        "each_block_consecutive_64_and_balanced_depth_6": True,
        "sorted_global_indices_exact": True,
        "full_owned_link_exact_name_set_and_type_size_total": True,
        "full_owned_link_remains_diagnostic_only": True,
        "git_blob_sha1_expected": hashlib.sha1(b"blob " + str(len(archive)).encode() + b"\0" + archive).hexdigest(),
        "files": {name: info(ROOT / name) for name in descriptor["files"]},
        "retrieval_tasks": retrievals,
        "originals_deleted_or_modified": False,
        "proof_or_audit_rerun": False,
        "git_tree_or_ref_modified": False,
        "new_compile_or_owned_audit_or_full_P2_credit": False,
        "local_failed_assumption_history_retained": str(ROOT / "local-validation-attempt-001.json"),
        "read_api_parameter_failure_history_retained": str(ROOT / "read-api-invalid-argument-history.json"),
    }
    path = ROOT / "retrieval-verification.json"
    path.write_text(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "receipt": info(path), "archive": result["files"]["blocks.stdout.log.gz"],
                      "expected_git_blob": result["git_blob_sha1_expected"], "blocks": len(emitted), "facts": len(summary["indices"]),
                      "new_compile_or_owned_audit_or_full_P2_credit": False}, sort_keys=True))


if __name__ == "__main__":
    main()
