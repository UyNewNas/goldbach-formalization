"""Receive the already-produced P3 evidence; never invoke Lean or rebuild a supplier."""
from __future__ import annotations

import hashlib
import json
import lzma
from pathlib import Path, PurePosixPath
import tarfile
import io

HERE = Path(__file__).resolve().parent
ARCHIVE = HERE / "qualified-unit-tail-count.tar.xz"
OUT = HERE / "unit-tail-root-evidence"
EXPECTED_XZ = "06fb1ee80e841571ead9ce262042b130c76be70c93c4880b40b5d21cb74c0f0f"
EXPECTED_MANIFEST = "f6246295885137041434ed75c773e4e1d578345bdd552c1033caba016fe36ec3"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


packed = ARCHIVE.read_bytes()
assert len(packed) == 5933976 and digest(packed) == EXPECTED_XZ
plain = lzma.decompress(packed)
assert len(plain) == 105850880
assert digest(plain) == "fa2e7c052e982fbda8a962a0e238c55288f1d6c88dee93fc0566f1453753bbfd"
with tarfile.open(fileobj=io.BytesIO(plain), mode="r:") as tar:
    members = tar.getmembers()
    names = [m.name for m in members]
    assert len(names) == len(set(names)) == 128
    assert all(m.isfile() for m in members)
    assert all(not PurePosixPath(n).is_absolute() and ".." not in PurePosixPath(n).parts for n in names)
    payload = {m.name: tar.extractfile(m).read() for m in members}

manifest_bytes = payload["FILE_MANIFEST.json"]
assert digest(manifest_bytes) == EXPECTED_MANIFEST
manifest = json.loads(manifest_bytes)
assert manifest["excludes"] == ["FILE_MANIFEST.json"]
entries = manifest["files"]
assert len(entries) == 127
assert set(entries) | {"FILE_MANIFEST.json"} == set(payload)
for name, record in entries.items():
    data = payload[name]
    assert len(data) == record["bytes"] and digest(data) == record["sha256"], name

OUT.mkdir(exist_ok=False)
for name, data in payload.items():
    dst = OUT / name
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_bytes(data)

result = {
    "schema": "p29_unit_tail_root_archive_transport_verification_v1",
    "archive": str(ARCHIVE),
    "archive_bytes": len(packed),
    "archive_sha256": digest(packed),
    "uncompressed_tar_bytes": len(plain),
    "uncompressed_tar_sha256": digest(plain),
    "manifest_sha256": digest(manifest_bytes),
    "member_count": len(members),
    "manifest_entry_count": len(entries),
    "all_member_names_sizes_sha256_verified": True,
    "unsafe_or_duplicate_members": False,
    "lean_executions": 0,
    "qualification": "TRANSPORT_ONLY_STAGE_AND_DECLARATION_REVIEW_PENDING",
}
(HERE / "UNIT_TAIL_ROOT_ARCHIVE_TRANSPORT.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
print(json.dumps({"member_names": names}, indent=2))
