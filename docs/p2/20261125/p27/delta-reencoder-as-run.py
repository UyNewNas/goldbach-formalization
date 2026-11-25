#!/usr/bin/env python3
"""Transport-only XZ reencoding; never run the proof/export/acceptance tools.

Run only if the independently observed original delta is large enough to justify it:
  python3 -B recompress_delta_stream.py INPUT.delta.tar.xz OUTPUT.delta.tar.xz \
    --input-sha256 INDEPENDENTLY_OBSERVED_ORIGINAL_DELTA_SHA256

The output parent must already exist. Neither an existing output nor the input
is overwritten. This checks byte transport and manifest anchors, not proof acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import sys
import tarfile
import tempfile


MANIFEST_SHA256 = "73179a250532882aa5a945ba149fb734ee776dd3fdcef5d386af69b6303eca08"
CHUNK = 1024 * 1024
DICT_SIZE = 128 * 1024 * 1024
ANCHORS = {"ORIGINAL_EXPORT_MANIFEST.json", "P27_DELTA_MANIFEST.json"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Meter:
    def __init__(self, stream, emit=None):
        self.stream, self.emit = stream, emit
        self.digest, self.size = hashlib.sha256(), 0

    def read(self, size=-1):
        chunk = self.stream.read(size)
        if chunk:
            self.digest.update(chunk)
            self.size += len(chunk)
            if self.emit is not None:
                self.emit(chunk)
        return chunk

    def readable(self):
        return True

    def seekable(self):
        return False

    def identity(self):
        return {"bytes": self.size, "sha256": self.digest.hexdigest()}


def file_identity(stream):
    meter = Meter(stream)
    while meter.read(CHUNK):
        pass
    return meter.identity()


def unique_json(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key in delta manifest")
        result[key] = value
    return result


def inspect_tar_stream(stream, emit=None):
    """Hash every decompressed byte, including padding after tar's end marker."""
    meter = Meter(stream, emit)
    seen, manifest_sha, delta_reference = set(), None, None
    with tarfile.open(fileobj=meter, mode="r|", bufsize=CHUNK) as archive:
        for member in archive:
            if member.name not in ANCHORS:
                continue
            require(member.isfile() and member.name not in seen,
                    "Missing regular/unique manifest member: " + member.name)
            seen.add(member.name)
            with archive.extractfile(member) as payload:
                if member.name == "ORIGINAL_EXPORT_MANIFEST.json":
                    manifest_sha = file_identity(payload)["sha256"]
                else:
                    value = json.load(payload, object_pairs_hook=unique_json)
                    require(isinstance(value, dict), "Delta manifest must be an object")
                    delta_reference = value.get("original_manifest_sha256")
    # tarfile may finish before the decompressed stream ends. Its prefetched
    # bytes were already metered; drain the remainder without altering it.
    while meter.read(CHUNK):
        pass
    require(seen == ANCHORS, "Both original and delta manifest members are required")
    require(manifest_sha == delta_reference == MANIFEST_SHA256,
            "Original exporter manifest anchor differs")
    return {**meter.identity(), "original_export_manifest_sha256": manifest_sha,
            "delta_manifest_reference": delta_reference}


def reencode(source_path, output_path, expected_input_sha):
    require(re.fullmatch(r"[0-9a-f]{64}", expected_input_sha) is not None,
            "Supply the independently observed original compressed delta SHA-256")
    source_path, output_path = source_path.absolute(), output_path.absolute()
    require(source_path.is_file() and not source_path.is_symlink(),
            "Input must be an existing regular file, not a symlink")
    require(output_path.parent.is_dir(), "Output parent directory must already exist")
    require(not os.path.lexists(output_path), "Output already exists; nothing overwritten")
    temporary = None
    try:
        with source_path.open("rb") as source:
            before = file_identity(source)
            require(before["sha256"] == expected_input_sha, "Original compressed input SHA differs")
            source.seek(0)
            used_input = Meter(source)
            with tempfile.NamedTemporaryFile(mode="wb", dir=output_path.parent,
                                             prefix="." + output_path.name + ".", suffix=".tmp",
                                             delete=False) as target:
                temporary = Path(target.name)
                compressor = lzma.LZMACompressor(
                    format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64,
                    filters=[{"id": lzma.FILTER_LZMA2, "preset": 6, "dict_size": DICT_SIZE}])

                def emit(chunk):
                    target.write(compressor.compress(chunk))

                with lzma.LZMAFile(used_input, mode="rb", format=lzma.FORMAT_XZ) as decoded:
                    original_tar = inspect_tar_stream(decoded, emit)
                require(used_input.identity() == before, "Input bytes used during decoding changed")
                target.write(compressor.flush())
                target.flush()
                os.fsync(target.fileno())

            with lzma.LZMAFile(temporary, mode="rb", format=lzma.FORMAT_XZ) as decoded:
                reencoded_tar = inspect_tar_stream(decoded)
            require(reencoded_tar == original_tar, "Reencoded complete tar stream differs")
            with temporary.open("rb") as encoded:
                output_identity = file_identity(encoded)
            source.seek(0)
            after = file_identity(source)
            require(after == before, "Original compressed input changed after reencoding")
            require(not source_path.is_symlink()
                    and os.path.samestat(os.fstat(source.fileno()), source_path.stat()),
                    "Original input path was replaced")

            receipt = {
                "schema": "p27-delta-xz-reencoding-v1",
                "status": "IDENTICAL_COMPLETE_TAR_STREAM_REENCODED",
                "input": {"path": str(source_path), "independent_sha256": expected_input_sha,
                          "before": before, "during_decode": used_input.identity(), "after": after},
                "output": {"path": str(output_path), **output_identity},
                "tar_stream_before": original_tar, "tar_stream_after": reencoded_tar,
                "original_manifest_sha256": MANIFEST_SHA256,
                "encoding": {"format": "XZ", "filter": "LZMA2", "preset": 6,
                             "dictionary_bytes": DICT_SIZE, "check": "CRC64"},
                "input_unchanged": True, "complete_tar_bytes_equal": True,
                "transport_encoding_only": True, "proof_credit": 0,
                "compile_credit": False, "kernel_credit": False,
            }
            # Same-directory hard-link publication is atomic and refuses an
            # existing destination, including one created after the first check.
            os.link(temporary, output_path)
        return receipt
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--input-sha256", required=True)
    args = parser.parse_args()
    try:
        receipt = reencode(args.input, args.output, args.input_sha256)
    except (OSError, ValueError, tarfile.TarError, lzma.LZMAError) as error:
        print(json.dumps({"status": "REENCODING_FAILED", "error": str(error),
                          "transport_encoding_only": True, "proof_credit": 0,
                          "compile_credit": False, "kernel_credit": False}), file=sys.stderr)
        return 2
    print(json.dumps(receipt, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
