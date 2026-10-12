#!/usr/bin/env python3
"""Reassemble and verify the retained split P1 round-3 evidence archive."""

from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path
import tarfile


HERE = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main() -> None:
    receipt = json.loads((HERE / "ARTIFACT.json").read_text(encoding="utf-8"))
    require(receipt["status"] == "ARCHIVED_VERIFIED_HISTORICAL_SAVING_EVIDENCE",
            "artifact status")
    blocks = []
    for part in receipt["parts"]:
        data = (HERE / part["path"]).read_bytes()
        require(len(data) == part["bytes"], f"part size: {part['path']}")
        require(hashlib.sha256(data).hexdigest() == part["sha256"],
                f"part SHA256: {part['path']}")
        blocks.append(data)
    archive = b"".join(blocks)
    require(len(archive) == receipt["bytes"], "combined archive size")
    require(hashlib.sha256(archive).hexdigest() == receipt["sha256"],
            "combined archive SHA256")
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as bundle:
        members = bundle.getmembers()
        require(len(members) == receipt["member_count"], "archive member count")
        require(len({member.name for member in members}) == len(members),
                "unique archive member names")
        require(all(member.isfile() for member in members), "regular archive members")
        manifest = json.load(bundle.extractfile("MANIFEST.json"))
    require(manifest["receipt_sha256"] == receipt["receipt_sha256"],
            "verification receipt binding")
    require(set(manifest["verified_targets"]) == set(receipt["verified_targets"]),
            "verified target scope")
    print(json.dumps({
        "status": "PASS",
        "archive_sha256": receipt["sha256"],
        "archive_bytes": receipt["bytes"],
        "part_count": len(receipt["parts"]),
        "member_count": len(members),
        "verified_target_count": len(receipt["verified_targets"]),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
