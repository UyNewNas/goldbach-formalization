#!/usr/bin/env python3
"""Reorder an existing slim evidence container without changing any member bytes.

This is transport only: no Lean, replay, audit, or new proof credit. Every input
member is checked against SLIM_MANIFEST.json, safely spooled under generated
filenames, and preserved. Native setup/provider/trace texts are grouped by their
original names rather than hashed archive paths. Output uses LZMA2 preset 3 with
a 64 MiB dictionary. The unchanged original verifier must still be run.

Temporary disk space is approximately the uncompressed payload size plus the
new archive; payloads are streamed, not accumulated in RAM. Existing input and
output paths are never overwritten. Publication occurs only after a second
streaming scan confirms identical member names, sizes, and SHA-256 hashes.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import lzma
import os
from pathlib import Path, PurePosixPath
import sys
import tarfile
import tempfile
import time


CHUNK = 1024 * 1024
DICTIONARY = 64 * 1024 * 1024


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def file_info(path: Path) -> dict:
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    return {"bytes": path.stat().st_size, "sha256": digest}


def safe_name(name: str) -> None:
    value = PurePosixPath(name)
    require(bool(name) and not value.is_absolute() and ".." not in value.parts
            and str(value) == name and "\\" not in name and "\x00" not in name,
            "Unsafe member name: " + name)


def scan(path: Path, spool: Path | None = None) -> tuple[dict, dict]:
    """Hash regular members; never extract a member using its archive pathname."""
    seen, stored = {}, {}
    with tarfile.open(path, "r|xz") as archive:
        for member in archive:
            name = member.name
            safe_name(name)
            require(member.isfile(), "Only regular members are supported: " + name)
            require(name not in seen, "Duplicate member: " + name)
            stream = archive.extractfile(member)
            require(stream is not None, "Missing member stream: " + name)
            destination = spool / f"{len(seen):08d}" if spool is not None else None
            target = destination.open("xb") if destination is not None else None
            digest, size = hashlib.sha256(), 0
            try:
                while chunk := stream.read(CHUNK):
                    digest.update(chunk)
                    size += len(chunk)
                    if target is not None:
                        target.write(chunk)
            finally:
                stream.close()
                if target is not None:
                    target.close()
            require(size == member.size, "Truncated member: " + name)
            seen[name] = {"sha256": digest.hexdigest(), "bytes": size}
            if destination is not None:
                stored[name] = destination
    return seen, stored


def check_manifest(seen: dict, stored: dict) -> dict:
    require("SLIM_MANIFEST.json" in seen, "Missing SLIM_MANIFEST.json")
    slim = json.loads(stored["SLIM_MANIFEST.json"].read_bytes())
    require(slim.get("slim_schema") == 1 and isinstance(slim.get("embedded"), dict),
            "Unsupported slim manifest")
    embedded = slim["embedded"]
    require("SLIM_MANIFEST.json" not in embedded
            and set(seen) == set(embedded) | {"SLIM_MANIFEST.json"},
            "Slim member inventory differs")
    for name, item in embedded.items():
        require(all(seen[name][field] == item[field] for field in ("sha256", "bytes")),
                "Member hash/size mismatch: " + name)
    return slim


def order_key(name: str, info: dict) -> tuple:
    if name == "SLIM_MANIFEST.json":
        return (9, "", "", "", name)
    if name in {"ORIGINAL_EXPORT_MANIFEST.json", "REPOSITORY_SOURCE_CATALOG.json",
                "REPACK_IMPLEMENTATION.py"} or name.endswith("/PACKAGE_MANIFEST.json"):
        return (0, "manifest", "", "", name)
    origin = str(info.get("origin", name))
    basename = PurePosixPath(origin).name
    lower = origin.lower()
    if "/context/native/" not in "/" + name:
        return (1, "other", basename, origin, name)
    if lower.endswith(".setup.json") or basename in {"setup.json", "actual-setup.json"}:
        category = "0-setup"
    elif "/providers/" in lower:
        category = "1-provider"
    elif lower.endswith((".trace", ".trace.json")):
        category = "2-trace"
    elif lower.endswith(".lean"):
        category = "3-source"
    else:
        category = "4-native-context"
    return (2, category, basename, origin, name)


def reorder(source: Path, output: Path, expected: str | None, temp_dir: Path | None) -> dict:
    started = time.monotonic()
    require(not os.path.lexists(output), "Output already exists; refusing to overwrite: " + str(output))
    source = source.resolve(strict=True)
    output = output.absolute()
    require(source.is_file() and output.parent.is_dir(), "Input or output parent is not a regular file/directory")
    before = file_info(source)
    require(expected is None or before["sha256"] == expected.lower(), "Input archive SHA-256 mismatch")
    with tempfile.TemporaryDirectory(prefix="winner9-reorder-", dir=temp_dir or output.parent) as directory:
        seen, stored = scan(source, Path(directory))
        slim = check_manifest(seen, stored)
        require(file_info(source) == before, "Input archive changed while being read")
        ordered = sorted(seen, key=lambda name: order_key(name, slim["embedded"].get(name, {})))
        groups = Counter(order_key(name, slim["embedded"].get(name, {}))[1] for name in ordered)
        # A same-filesystem temporary output permits atomic no-clobber publication.
        descriptor, temporary_name = tempfile.mkstemp(prefix=".winner9-reorder-", suffix=".tar.xz", dir=output.parent)
        temporary = Path(temporary_name)
        try:
            with os.fdopen(descriptor, "wb") as raw:
                filters = [{"id": lzma.FILTER_LZMA2, "preset": 3, "dict_size": DICTIONARY}]
                with lzma.LZMAFile(raw, "w", format=lzma.FORMAT_XZ, filters=filters) as compressed:
                    with tarfile.open(fileobj=compressed, mode="w|", format=tarfile.PAX_FORMAT) as archive:
                        for name in ordered:
                            member = tarfile.TarInfo(name)
                            member.size, member.mode, member.mtime = seen[name]["bytes"], 0o644, 0
                            with stored[name].open("rb") as payload:
                                archive.addfile(member, payload)
            after_members, _ = scan(temporary)
            require(after_members == seen, "Output member names/bytes/hashes differ from input")
            after = file_info(temporary)
            require(file_info(source) == before, "Input archive changed during reorder")
            report = {
                "schema": "p2-private-evidence-container-reorder-v1",
                "input": {"path": str(source), **before},
                "output": {"path": str(output), **after},
                "verified_members": len(seen),
                "uncompressed_payload_bytes": sum(item["bytes"] for item in seen.values()),
                "slim_manifest_sha256": seen["SLIM_MANIFEST.json"]["sha256"],
                "all_member_names_bytes_hashes_identical": True,
                "all_manifest_bytes_unchanged": True,
                "accepted_module_count": slim["accepted_module_count"],
                "owned_declaration_count": slim["owned_declaration_count"],
                "compression": {"filter": "LZMA2", "preset": 3, "dictionary_bytes": DICTIONARY},
                "ordering": "native origin category, original basename, original path, archive name",
                "member_groups": dict(groups), "proof_credit": False,
                "original_verifier_required": True,
                "elapsed_seconds": round(time.monotonic() - started, 3),
            }
            # link() fails if a file or symlink appeared at the destination meanwhile.
            os.link(temporary, output)
        finally:
            temporary.unlink(missing_ok=True)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--input-sha256", help="Optional externally pinned input archive SHA-256")
    parser.add_argument("--temp-dir", type=Path, help="Existing directory for uncompressed member spooling")
    args = parser.parse_args()
    try:
        report = reorder(args.archive, args.output, args.input_sha256, args.temp_dir)
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, lzma.LZMAError) as error:
        print("Reorder failed: " + str(error), file=sys.stderr)
        return 2
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
