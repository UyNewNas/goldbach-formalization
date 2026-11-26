"""Independent exact reconstruction and comparison; no release operation.

This script imports only the frozen reconstruction/common helpers.  It never
imports or invokes the release stage and never creates reconstruction markers.
Persistent writes are confined to its fresh verification evidence directory.
TemporaryDirectory removes only the new reconstruction directory under /tmp.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile


SCRIPTS = Path("/workspace/p24-diagnostic-metadata-retention-20261126/scripts-002")
COMMON_SHA256 = "796d76d331f0a01bf7791cd75f33d0e6b51740e4053425b86e248a9f96f332a4"
OUTPUT = Path("/workspace/p24-diagnostic-metadata-retention-20261126/attempt-002/verification-only-001")
TASK_ID = "f4ea526437424a519930753257d6e725"
TASK_STATUS_SHA256 = "4a77c3a33cce1a78696232ff26e1bc56f3cd9390f6629dece43967fc2a923771"
FIRST_RECEIPT_BYTES = 26938
FIRST_RECEIPT_SHA256 = "b0873059d79e979f6dd6b41a9df2bf9c438e420134ebd616b5e0ba1c5be99b1f"
DESCRIPTOR_BYTES = 3833
DESCRIPTOR_SHA256 = "8a30765985104fd6f9caed5a78ef7403175c1f09e8e6f57978fd5c79b68ca58d"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    require(Path(__file__).resolve() == OUTPUT / "verify_only.py", "Unexpected verification script location")
    common = SCRIPTS / "retention_common.py"
    require(sha(common.read_bytes()) == COMMON_SHA256, "Frozen common helper differs")
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(SCRIPTS))
    import retention_common as c

    manifest = c.load_manifest()
    require(OUTPUT.parent == Path(manifest["output_dir"]), "Unexpected evidence parent")
    require(set(p.name for p in OUTPUT.iterdir()) == {"verify_only.py", "stage1-task-status.json"},
            "Verification evidence directory is not the freshly installed two-file input")
    input_bindings = {name: c.file_info(OUTPUT / name, single_link=True)
                      for name in ["verify_only.py", "stage1-task-status.json"]}
    task_raw = (OUTPUT / "stage1-task-status.json").read_bytes()
    require(sha(task_raw) == TASK_STATUS_SHA256, "Actual first-task status bytes differ")
    task = json.loads(task_raw)
    require(task.get("task_id", task.get("job_id")) == TASK_ID and task.get("status") == "succeeded"
            and task.get("exit_code") == 0 and task.get("ended_at"), "First preservation task did not succeed")

    first_path = OUTPUT.parent / "stage1-receipt.json"
    descriptor_path = OUTPUT.parent / "bundle-descriptor.json"
    require(first_path.stat().st_size == FIRST_RECEIPT_BYTES and c.digest(first_path) == FIRST_RECEIPT_SHA256,
            "Actual preservation receipt differs")
    require(descriptor_path.stat().st_size == DESCRIPTOR_BYTES and c.digest(descriptor_path) == DESCRIPTOR_SHA256,
            "Actual preserved-bundle descriptor differs")
    first = json.loads(first_path.read_bytes())
    require(first["status"] == "passed" and first["exit_code"] == 0 and first["canonical_postcheck_passed"],
            "First preservation receipt is not a successful verified preservation")
    require(first["manifest_sha256"] == c.MANIFEST_SHA256
            and first["script_bindings"] == c.script_bindings(manifest), "Frozen recipe changed after preservation")
    require(first["process"] != c.process_identity(), "Verification must run in a fresh process")
    original_identities = {r["path"]: r for r in first["targets_before"]}
    require(set(original_identities) == {r["path"] for r in manifest["targets"]}, "First receipt coverage differs")
    spec = first["bundle_spec"]
    runtime = first["gzip_runtime"]
    require(c.receipt_info(descriptor_path) == first["bundle_descriptor"]
            and json.loads(descriptor_path.read_bytes()) == spec, "Persistent descriptor does not bind this bundle")

    retained_paths = [first_path, descriptor_path, Path(spec["path"])]
    retained_paths += [Path(a["descriptor_path"]) for a in manifest["archives"]]
    retained_before = {str(p): c.file_info(p) for p in retained_paths}

    with c.original_lock(manifest):
        before = c.capture_canonical(manifest)
        free_before = c.reserve(manifest, manifest["max_control_files_bytes"])
        receipt = {
            "schema": 1,
            "stage": "independent_reconstruction_and_comparison_only",
            "started_utc": c.now(),
            "process": c.process_identity(),
            "stage1_task_id": TASK_ID,
            "stage1_task_status_sha256": TASK_STATUS_SHA256,
            "stage1_receipt_sha256": FIRST_RECEIPT_SHA256,
            "manifest_sha256": c.MANIFEST_SHA256,
            "input_bindings": input_bindings,
            "canonical_before": before,
            "registry_changed_since_preservation": before["registry_sha256"] != first["canonical_after"]["registry_sha256"],
            "free_bytes_before_verification": free_before,
            "original_files_deleted": 0,
            "original_files_written": 0,
            "reconstruction_markers_created": 0,
            "release_stage_imported_or_invoked": False,
            "canonical_credit": False,
            "new_compiler_or_audit_credit": False,
        }
        code = 1
        try:
            c.require_independent_tmp(manifest)
            before_targets = {}
            for record in manifest["targets"]:
                actual = c.check_target(record)
                require(c.matching_identity(actual, original_identities[record["path"]]),
                        "An original was replaced since preservation: " + record["path"])
                c.ensure_marker_absent(record)
                before_targets[record["path"]] = actual
            receipt["original_targets_before"] = before_targets
            with tempfile.TemporaryDirectory(prefix="p24-solid-verification-only-", dir="/tmp") as folder:
                restored, verified = c.reconstruct_all(manifest, spec, Path(folder), runtime)
                comparisons = []
                for record in manifest["targets"]:
                    path = record["path"]
                    require(c.bytes_equal_files(restored[path], path), "Exact reconstructed/original bytes differ: " + path)
                    require(c.matching_identity(c.check_target(record), before_targets[path]),
                            "Original changed during comparison: " + path)
                    c.ensure_marker_absent(record)
                    comparisons.append({"path": path, "bytes": record["bytes"], "sha256": record["sha256"],
                                        "reconstructed_from_solid_bundle_only": True,
                                        "byte_for_byte_equal_to_present_original": True})
                receipt["independent_reconstruction"] = verified
                receipt["original_byte_comparisons"] = comparisons
                receipt["all_thirteen_independently_reconstructed_and_compared"] = True
                require(c.gzip_runtime_profile() == runtime, "Reconstruction runtime changed")
            code = 0
        except Exception as error:
            receipt["error"] = type(error).__name__ + ": " + str(error)
        finally:
            postchecks = {}
            try:
                after_targets = {}
                for record in manifest["targets"]:
                    actual = c.check_target(record)
                    require(c.matching_identity(actual, original_identities[record["path"]]),
                            "An original no longer has its preserved bytes/identity: " + record["path"])
                    c.ensure_marker_absent(record)
                    after_targets[record["path"]] = actual
                receipt["original_targets_after"] = after_targets
                postchecks["all_thirteen_original_bytes_and_identities_unchanged"] = True
                postchecks["all_thirteen_reconstruction_markers_still_absent"] = True
            except Exception as error:
                postchecks["originals_and_markers_unchanged"] = False
                receipt["original_postcheck_error"] = type(error).__name__ + ": " + str(error)
                code = code or 125
            try:
                after = c.capture_canonical(manifest)
                receipt["canonical_after"] = after
                require(after == before, "Canonical state changed during read-only verification")
                require(c.script_bindings(manifest) == first["script_bindings"], "Frozen reconstruction recipe changed")
                for path, expected in retained_before.items():
                    require(c.matching_identity(c.file_info(path), expected), "Preserved archive/descriptor/receipt changed: " + path)
                for name, expected in input_bindings.items():
                    require(c.matching_identity(c.file_info(OUTPUT / name, single_link=True), expected),
                            "Verification input changed: " + name)
                postchecks["complete_canonical_state_and_recipe_unchanged"] = True
                postchecks["preserved_bundle_receipts_and_descriptors_unchanged"] = True
                postchecks["verification_inputs_unchanged"] = True
            except Exception as error:
                postchecks["canonical_or_retained_inputs_unchanged"] = False
                receipt["canonical_postcheck_error"] = type(error).__name__ + ": " + str(error)
                code = code or 125
            receipt["postchecks"] = postchecks
            receipt["observed_targets_at_end"] = c.observe_targets(manifest["targets"])
            observed = receipt["observed_targets_at_end"]
            if observed["missing"] or observed["uninspectable"] or len(observed["remaining"]) != 13:
                receipt["target_presence_postcheck_passed"] = False
                code = code or 125
            else:
                receipt["target_presence_postcheck_passed"] = True
            receipt["status"] = "passed" if code == 0 else "failed"
            receipt["exit_code"] = code
            receipt["completed_utc"] = c.now()
            raw = c.encoded(receipt)
            c.reserve(manifest, len(raw))
            c.write_new(OUTPUT / "receipt.json", raw)
            final_free = c.free_bytes(manifest["worktree"])
            reserve_ok = final_free >= manifest["reserve_bytes"]
            if not reserve_ok:
                code = code or 125
            print(json.dumps({
                "stage": "verification_only", "status": "passed" if code == 0 else "failed", "exit_code": code,
                "receipt": c.receipt_info(OUTPUT / "receipt.json"),
                "original_count": 13, "original_files_deleted": 0, "original_files_written": 0,
                "reconstruction_markers_created": 0,
                "all_thirteen_independently_reconstructed_and_compared": receipt.get("all_thirteen_independently_reconstructed_and_compared", False),
                "postchecks": postchecks, "persistent_reserve_passed_after_receipt": reserve_ok,
                "free_bytes_after_all_persistent_writes": final_free,
                "observed_free_delta_after_all_persistent_writes": final_free - free_before,
                "canonical_credit": False, "new_compiler_or_audit_credit": False,
            }), flush=True)
        return code


if __name__ == "__main__":
    sys.exit(main())
