#!/usr/bin/env bash
# Package the first accepted export; this command does not compile or replay Lean.
# The caller must obtain argument 1 from the original exporter's recorded output.
set -euo pipefail
p27_manifest_sha="${1:?expected original export manifest SHA-256 required}"
p27_delivery="${2:-.lake/p27-delivery/attempt-001}"
p27_export=.lake/p2-private/exports/p27-complete-20261125
[[ "$p27_manifest_sha" =~ ^[0-9a-f]{64}$ ]]
test ! -e "$p27_delivery"
mkdir -p "$p27_delivery"
python3 -B verification/part2/repack_winner9_private_evidence.py catalog \
  --repo . --output "$p27_delivery/SOURCE_CATALOG.all.json"
python3 -B - "$p27_delivery/SOURCE_CATALOG.all.json" \
  "$p27_export/manifest.json" "$p27_delivery/SOURCE_CATALOG_P27.json" \
  "$p27_manifest_sha" <<'PY'
from pathlib import Path
import hashlib
import json
import sys

catalog_path, manifest_path, output_path = map(Path, sys.argv[1:4])
catalog_raw = catalog_path.read_bytes()
manifest_raw = manifest_path.read_bytes()
manifest_sha = hashlib.sha256(manifest_raw).hexdigest()
assert manifest_sha == sys.argv[4], "Original export manifest SHA differs"
catalog = json.loads(catalog_raw)
manifest = json.loads(manifest_raw)
assert catalog["catalog_schema"] == 1
project = manifest["object_manifest"]
assert len(project) == 81
assert "ImbalancedChen.P2PairedCertificateCompletion" in project
wanted = {row["source_sha256"] for row in project.values()}
retained = {key: row for key, row in catalog["blobs"].items() if key in wanted}
result = dict(catalog)
result["blobs"] = retained
result["derivation"] = {
    "kind": "P2.7 project-source catalog subset",
    "source_catalog_sha256": hashlib.sha256(catalog_raw).hexdigest(),
    "original_export_manifest_sha256": manifest_sha,
    "project_module_count": 81,
    "required_unique_source_hashes": len(wanted),
    "retained_source_blobs": len(retained),
    "missing_source_hashes_remain_embedded": sorted(wanted - retained.keys()),
    "complete_repository_inventory_claimed": False,
}
raw = (json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()
with output_path.open("xb") as output:
    output.write(raw)
print(json.dumps({"source_catalog": str(output_path), "bytes": len(raw),
                  "sha256": hashlib.sha256(raw).hexdigest(),
                  "retained_source_blobs": len(retained), "proof_credit": False}, sort_keys=True))
PY
python3 -B verification/part2/p27_delta_evidence.py pack "$p27_export" \
  --source-catalog "$p27_delivery/SOURCE_CATALOG_P27.json" \
  --prior-catalog docs/p2/20261125/p27/prior-evidence-slim-catalog.json.xz \
  --currentchen-adoption-dir .lake/p27-currentchen-adoption/attempt-001 \
  --manifest-sha256 "$p27_manifest_sha" \
  --output "$p27_delivery/P27_COMPLETE.delta.tar.xz"
