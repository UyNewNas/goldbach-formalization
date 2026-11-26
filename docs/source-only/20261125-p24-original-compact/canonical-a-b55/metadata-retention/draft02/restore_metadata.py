"""Manually restore one of thirteen exact loose files from the solid XZ only."""
import argparse
import json
import os
from pathlib import Path
import sys
import tempfile

import retention_common as c


def main():
    parser = argparse.ArgumentParser(); parser.add_argument("--path", required=True); args = parser.parse_args()
    manifest = c.load_manifest(); matches = [r for r in manifest["targets"] if r["path"] == args.path]
    c.require(len(matches) == 1, "Only an exact thirteen-file whitelist path can be restored")
    record = matches[0]; target = Path(record["path"])
    marker = json.loads(c.marker_path(record).read_bytes()); first_path = Path(marker["stage1_receipt"])
    c.require(c.digest(first_path) == marker["stage1_receipt_sha256"], "Preservation receipt changed")
    first = json.loads(first_path.read_bytes()); spec = first["bundle_spec"]
    c.require(first["status"] == "passed" and first["script_bindings"] == c.script_bindings(manifest), "Preservation/recipe differs")
    c.require(marker["original_path"] == record["path"] and marker["original_sha256"] == record["sha256"] and
              marker["solid_xz_sha256"] == spec["xz_sha256"], "Reconstruction reference changed")
    with c.original_lock(manifest):
        c.require(not os.path.lexists(target), "Never overwrite a file or symlink")
        before = c.capture_canonical(manifest); c.require_independent_tmp(manifest)
        c.reserve(manifest, record["bytes"] + manifest["max_control_files_bytes"])
        with tempfile.TemporaryDirectory(prefix="p24-solid-restore-", dir="/tmp") as folder:
            restored, _ = c.reconstruct_all(manifest, spec, Path(folder), first["gzip_runtime"])
            temporary = Path(str(target)+".P24_RESTORING")
            c.require(not os.path.lexists(temporary), "Inspect a previous incomplete restore first")
            c.copy_exact(restored[record["path"]], temporary, record)
            with temporary.open("rb") as stream: os.fsync(stream.fileno())
            os.link(temporary, target, follow_symlinks=False)
            temporary.unlink()  # Only this new verified recovery temporary.
            c.fsync_dir(target.parent)
        c.require(c.capture_canonical(manifest) == before, "Canonical state changed during restoration")
        print(json.dumps({"restored": c.receipt_info(target), "canonical_credit": False}), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
