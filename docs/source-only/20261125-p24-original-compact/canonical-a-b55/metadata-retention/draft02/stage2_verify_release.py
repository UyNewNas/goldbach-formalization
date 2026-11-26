"""Draft02 second job: reconstruct thirteen original files, then explicit release."""
import argparse
import json
import os
from pathlib import Path
import re
import sys
import tempfile

import retention_common as c


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage1-receipt-sha256", required=True)
    parser.add_argument("--stage1-task-id", required=True)
    parser.add_argument("--stage1-task-status", type=Path, required=True)
    parser.add_argument("--stage1-task-status-sha256", required=True)
    parser.add_argument("--release-reviewed-thirteen", action="store_true")
    args = parser.parse_args()
    c.require(args.release_reviewed_thirteen, "Explicit owner release selection is required")
    for value in [args.stage1_receipt_sha256, args.stage1_task_status_sha256]:
        c.require(re.fullmatch(r"[0-9a-f]{64}", value), "Fill actual first-job hashes; placeholders are not executable")
    c.require(re.fullmatch(r"[0-9a-f]{32}", args.stage1_task_id), "Fill actual successful first-job task id")
    c.require(c.digest(args.stage1_task_status) == args.stage1_task_status_sha256, "Actual task status differs")
    task = json.loads(args.stage1_task_status.read_bytes())
    c.require(task.get("task_id",task.get("job_id")) == args.stage1_task_id and task.get("status") == "succeeded"
              and task.get("exit_code") == 0 and task.get("ended_at"), "Separate first task did not succeed")
    manifest = c.load_manifest(); output = Path(manifest["output_dir"])
    first_path = output/"stage1-receipt.json"
    c.require(c.digest(first_path) == args.stage1_receipt_sha256, "First-job receipt differs")
    first = json.loads(first_path.read_bytes())
    c.require(first["status"] == "passed" and first["exit_code"] == 0 and first["canonical_postcheck_passed"], "Preservation failed")
    c.require(first["manifest_sha256"] == c.MANIFEST_SHA256 and first["script_bindings"] == c.script_bindings(manifest),
              "Manifest/scripts differ from preservation")
    c.require(first["process"] != c.process_identity(), "Reconstruction must use a fresh process")
    originals = {r["path"]:r for r in first["targets_before"]}
    c.require(set(originals) == {r["path"] for r in manifest["targets"]}, "Preserved target coverage differs")
    spec = first["bundle_spec"]; runtime = first["gzip_runtime"]
    descriptor = output/"bundle-descriptor.json"
    c.require(c.receipt_info(descriptor) == first["bundle_descriptor"] and json.loads(descriptor.read_bytes()) == spec,
              "Persistent bundle descriptor differs")
    with c.original_lock(manifest):
        before = c.capture_canonical(manifest)
        free_before = c.reserve(manifest, manifest["max_control_files_bytes"])
        c.require_independent_tmp(manifest)
        stage = output/"stage2"; stage.mkdir(exist_ok=False); c.fsync_dir(output)
        receipt = {"schema": 2, "stage": "independent_solid_reconstruction_then_thirteen_release", "status": "failed",
                   "started_utc": c.now(), "process": c.process_identity(),
                   "stage1_task_id": args.stage1_task_id, "stage1_task_status_sha256": args.stage1_task_status_sha256,
                   "stage1_receipt_sha256": args.stage1_receipt_sha256, "manifest_sha256": c.MANIFEST_SHA256,
                   "canonical_before": before, "free_bytes_before": free_before,
                   "registry_changed_between_jobs": before["registry_sha256"] != first["canonical_after"]["registry_sha256"],
                   "released": [], "canonical_credit": False,
                   "source_object_native_registry_audit_log_modified": False}
        code = 1
        try:
            with tempfile.TemporaryDirectory(prefix="p24-solid-independent-", dir="/tmp") as folder:
                restored, verified = c.reconstruct_all(manifest, spec, Path(folder), runtime)
                for record in manifest["targets"]:
                    c.require(c.bytes_equal_files(restored[record["path"]], record["path"]), "Restored bytes differ from original")
                    c.require(c.matching_identity(c.check_target(record), originals[record["path"]]), "Original replaced between jobs")
                    c.ensure_marker_absent(record)
                receipt["independent_reconstruction"] = verified
                receipt["all_thirteen_reconstructed_before_any_unlink"] = True
                c.require(c.capture_canonical(manifest) == before, "Canonical state changed before release")
                c.require(c.script_bindings(manifest) == first["script_bindings"], "Retention recipe changed before release")
                # Every durable marker exists before any original is unlinked.
                for record in manifest["targets"]:
                    marker = {"schema": 2, "kind": "exact_diagnostic_reconstruction_reference",
                              "original_path": record["path"], "original_bytes": record["bytes"], "original_sha256": record["sha256"],
                              "solid_xz_path": spec["path"], "solid_xz_bytes": spec["xz_bytes"], "solid_xz_sha256": spec["xz_sha256"],
                              "complete_outer_tar_bytes": spec["tar_bytes"], "complete_outer_tar_sha256": spec["tar_sha256"],
                              "outer_FILES_member": spec["FILES_member"], "restore_kind": record["restore_kind"],
                              "solid_member": record["solid_member"], "inner_member": record["member"],
                              "stage1_receipt": str(first_path), "stage1_receipt_sha256": args.stage1_receipt_sha256,
                              "stage1_task_id": args.stage1_task_id, "release_receipt": str(stage/"receipt.json"),
                              "restore_script": str(Path(manifest["scripts_dir"])/"restore_metadata.py"),
                              "canonical_credit": False,
                              "note": "Reference only. Original loose bytes are recoverable from the complete solid XZ; consult release receipt for actual unlink status."}
                    c.reserve(manifest, len(c.encoded(marker))); c.write_new(c.marker_path(record), c.encoded(marker))
                # Exactly eleven JSONs, then the two derived gzips. No glob, no discovery.
                for record in manifest["targets"]:
                    current = c.check_target(record)
                    c.require(c.matching_identity(current, originals[record["path"]]), "Original changed just before unlink")
                    event = {"path": record["path"], "bytes": current["bytes"], "sha256": current["sha256"],
                             "allocated_bytes_before_unlink": current["allocated_bytes"], "marker": str(c.marker_path(record)),
                             "unlink_succeeded": False, "parent_fsync_succeeded": False}
                    path = Path(record["path"]); path.unlink()
                    event["unlink_succeeded"] = True; receipt["released"].append(event)
                    c.fsync_dir(path.parent); event["parent_fsync_succeeded"] = True
                    event["free_bytes_after_unlink"] = c.free_bytes(manifest["worktree"])
                    c.write_new(stage/f"released-{len(receipt['released']):02d}.json", c.encoded(event))
                c.require(Path(spec["path"]).stat().st_size == spec["xz_bytes"] and c.digest(spec["path"]) == spec["xz_sha256"],
                          "Sole durable solid bundle changed after release")
                c.require(c.receipt_info(descriptor) == first["bundle_descriptor"], "Durable descriptor changed")
                for original in manifest["archives"]:
                    c.require(c.digest(original["descriptor_path"]) == original["descriptor_sha256"], "Original gzip descriptor changed")
                c.require(c.gzip_runtime_profile() == runtime, "Exact gzip reconstruction runtime changed")
            code = 0
        except Exception as error:
            receipt["error"] = type(error).__name__ + ": " + str(error)
        finally:
            observed = c.observe_targets(manifest["targets"]); receipt["observed_targets_at_end"] = observed
            receipt["logical_bytes_observed_missing_at_end"] = sum(r["expected_bytes"] for r in observed["missing"])
            if code == 0 and (len(observed["missing"]) != 13 or observed["remaining"] or observed["uninspectable"]):
                code = 1; receipt["error"] = "Observed final whitelist does not match thirteen completed releases"
            try:
                after = c.capture_canonical(manifest); receipt["canonical_after"] = after
                c.require(after == before, "Canonical state changed during release")
                c.require(c.script_bindings(manifest) == first["script_bindings"], "Recipe changed during release")
                receipt["canonical_postcheck_passed"] = True
            except Exception as error:
                receipt["canonical_postcheck_passed"] = False
                receipt["postcheck_error"] = type(error).__name__ + ": " + str(error); code = code or 125
            receipt["status"] = "passed" if code == 0 else "failed"; receipt["exit_code"] = code; receipt["completed_utc"] = c.now()
            receipt["logical_bytes_released"] = sum(r["bytes"] for r in receipt["released"])
            receipt["allocated_bytes_unlinked"] = sum(r["allocated_bytes_before_unlink"] for r in receipt["released"])
            c.write_new(stage/"receipt.json", c.encoded(receipt)); final_free = c.reserve(manifest)
            print(json.dumps({"stage": 2, "variant": "draft02-solid-xz", "status": receipt["status"], "exit_code": code,
                              "receipt": c.receipt_info(stage/"receipt.json"), "logical_bytes_released": receipt["logical_bytes_released"],
                              "allocated_bytes_unlinked": receipt["allocated_bytes_unlinked"],
                              "free_bytes_after_all_persistent_writes": final_free,
                              "observed_free_delta_after_all_persistent_writes": final_free-free_before,
                              "canonical_credit": False}), flush=True)
        return code


if __name__ == "__main__":
    sys.exit(main())
