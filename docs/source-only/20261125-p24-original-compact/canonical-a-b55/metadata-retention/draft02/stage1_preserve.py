"""Draft02 first job: durably retain all inputs in solid XZ; delete nothing."""
import json
import os
from pathlib import Path
import sys
import tempfile

import retention_common as c


def main():
    manifest = c.load_manifest(); output = Path(manifest["output_dir"])
    with c.original_lock(manifest):
        c.require(not output.exists(), "Use a fresh stage1 output; never overwrite a previous attempt")
        before = c.capture_canonical(manifest)
        free_before = c.reserve(manifest, manifest["max_control_files_bytes"])
        c.require_independent_tmp(manifest)
        scripts = c.script_bindings(manifest); runtime = c.gzip_runtime_profile()
        for name, expected in manifest["retained_recipe_inputs"].items():
            p = Path(manifest["scripts_dir"])/name
            c.require(p.stat().st_size == expected["bytes"] and c.digest(p) == expected["sha256"], "Original recipe input changed")
        output.mkdir(parents=True, exist_ok=False); c.fsync_dir(output.parent)
        receipt = {"schema": 2, "stage": "solid_xz_preserve_only", "status": "failed",
                   "started_utc": c.now(), "process": c.process_identity(),
                   "manifest_sha256": c.MANIFEST_SHA256, "script_bindings": scripts,
                   "gzip_runtime": runtime, "canonical_before": before, "free_bytes_before": free_before,
                   "originals_deleted": [], "canonical_credit": False,
                   "source_object_native_registry_audit_log_modified": False}
        code = 1
        try:
            original_infos = []
            for record in manifest["targets"]:
                c.ensure_marker_absent(record); original_infos.append(c.check_target(record))
            receipt["targets_before"] = original_infos
            with tempfile.TemporaryDirectory(prefix="p24-solid-preserve-", dir="/tmp") as folder:
                temp = Path(folder)
                spec, verification = c.build_solid_bundle(manifest, temp, before, original_infos, runtime)
                check = temp/"full-roundtrip"; check.mkdir()
                rebuilt, roundtrip = c.reconstruct_all(manifest, spec, check, runtime)
                for record in manifest["targets"]:
                    c.require(c.bytes_equal_files(rebuilt[record["path"]], record["path"]),
                              "Roundtrip does not byte-match an original")
                # Persistent space is checked against the ACTUAL fully verified XZ
                # size.  No speculative size estimate triggers a release.
                c.reserve(manifest, spec["xz_bytes"] + manifest["max_control_files_bytes"])
                partial = output/"preserved-complete-inputs.tar.xz.incomplete"
                c.copy_exact(spec["path"], partial, {"bytes": spec["xz_bytes"], "sha256": spec["xz_sha256"]})
                with partial.open("rb") as stream: os.fsync(stream.fileno())
                persistent = dict(spec, path=str(partial))
                persistent_verification = c.verify_solid_bundle(persistent)
                final = output/"preserved-complete-inputs.tar.xz"
                c.require(not final.exists(), "Do not replace a persistent bundle")
                partial.rename(final); c.fsync_dir(output); persistent["path"] = str(final)
                c.write_new(output/"bundle-descriptor.json", c.encoded(persistent))
                receipt["bundle_spec"] = persistent
                receipt["bundle_descriptor"] = c.receipt_info(output/"bundle-descriptor.json")
                receipt["preparation_verification"] = verification
                receipt["all_thirteen_roundtrip_before_persistence"] = roundtrip
                receipt["persistent_bundle_verification"] = persistent_verification
            current = [c.check_target(r) for r in manifest["targets"]]
            c.require(all(c.matching_identity(a,b) for a,b in zip(current, original_infos)), "An original changed during stage1")
            c.require(c.gzip_runtime_profile() == runtime, "Gzip runtime changed during stage1")
            code = 0
        except Exception as error:
            receipt["error"] = type(error).__name__ + ": " + str(error)
        finally:
            try:
                after = c.capture_canonical(manifest); receipt["canonical_after"] = after
                c.require(after == before, "Canonical state changed during preservation")
                c.require(c.script_bindings(manifest) == scripts, "Retention scripts changed")
                receipt["canonical_postcheck_passed"] = True
            except Exception as error:
                receipt["canonical_postcheck_passed"] = False
                receipt["postcheck_error"] = type(error).__name__ + ": " + str(error)
                code = code or 125
            receipt["status"] = "passed" if code == 0 else "failed"
            receipt["exit_code"] = code; receipt["completed_utc"] = c.now()
            c.write_new(output/"stage1-receipt.json", c.encoded(receipt))
            final_free = c.reserve(manifest)
            print(json.dumps({"stage": 1, "variant": "draft02-solid-xz", "status": receipt["status"], "exit_code": code,
                              "receipt": c.receipt_info(output/"stage1-receipt.json"),
                              "bundle": receipt.get("bundle_descriptor"),
                              "actual_xz_bytes": receipt.get("bundle_spec",{}).get("xz_bytes"),
                              "free_bytes_after_all_persistent_writes": final_free,
                              "observed_free_delta_after_all_persistent_writes": final_free-free_before,
                              "original_files_deleted": 0, "canonical_credit": False}), flush=True)
        return code


if __name__ == "__main__":
    sys.exit(main())
