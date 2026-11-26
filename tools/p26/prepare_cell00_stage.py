#!/usr/bin/env python3
"""Freeze the already accepted analytic suppliers in the isolated P1 stage.

This script copies exact pre-existing source/object bytes; it does not generate
or compile Lean source. The complete 224-module pin file is an explicit input.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def copy_exact(src, dst, expected):
    assert src.is_file(), ("Missing accepted supplier", str(src))
    assert sha(src) == expected, ("Accepted supplier changed", str(src))
    dst.parent.mkdir(parents=True, exist_ok=True)
    if dst.exists():
        assert sha(dst) == expected, ("Existing isolated supplier changed", str(dst))
    else:
        shutil.copyfile(src, dst)
    assert sha(dst) == expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--pins", type=Path, required=True)
    args = parser.parse_args()
    stage, pins_path = args.stage.resolve(), args.pins.resolve()
    pins = json.loads(pins_path.read_text())
    manifest = json.loads((stage / "MANIFEST.json").read_text())
    for item in manifest["files"]:
        path = stage / item["archive_path"]
        assert path.stat().st_size == item["bytes"]
        assert sha(path) == item["sha256"], ("Transferred supplier mismatch", str(path))
    original_root = Path(pins["original_project_root"])
    frozen = []
    assert len(pins["rows"]) == pins["module_count"] == 224
    for row in pins["rows"]:
        module_path = Path(row["module"].replace(".", "/"))
        source = original_root / module_path.with_suffix(".lean")
        obj = Path(row["originalpath"])
        source_dst = stage / "analytic/sources" / module_path.with_suffix(".lean")
        object_dst = stage / "analytic/objects" / module_path.with_suffix(".olean")
        copy_exact(source, source_dst, row["source_sha256"])
        copy_exact(obj, object_dst, row["object_sha256"])
        assert object_dst.stat().st_size == row["bytes"]
        collision = stage / "objects" / module_path.with_suffix(".olean")
        if collision.exists():
            assert sha(collision) == row["object_sha256"], ("Object-root collision", row["module"])
        frozen.append({**row, "frozen_source": str(source_dst), "frozen_object": str(object_dst)})
    result = {
        "status": "exact_accepted_suppliers_frozen",
        "pins_sha256": sha(pins_path),
        "cell00_manifest_sha256": sha(stage / "MANIFEST.json"),
        "analytic_modules": len(frozen),
        "analytic_rows": frozen,
        "proof_sources_generated": False,
        "accepted_modules_recompiled": False,
    }
    out = stage / "ANALYTIC_FREEZE.json"
    if out.exists():
        assert json.loads(out.read_text()) == result
    else:
        out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "modules": len(frozen), "manifest_sha256": sha(out)}), flush=True)


if __name__ == "__main__":
    main()
