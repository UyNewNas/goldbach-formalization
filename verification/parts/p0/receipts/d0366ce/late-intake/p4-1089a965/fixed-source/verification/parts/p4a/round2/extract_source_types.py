#!/usr/bin/env python3
"""Read-only Part 4 source-type extraction, not compiler verification.

Usage from the repository root:
  python verification/parts/p4a/round2/extract_source_types.py --repo .
  python verification/parts/p4a/round2/extract_source_types.py --repo . \
    --check-json verification/parts/p4a/round2/SOURCE_TYPES.json

Without --check-json, JSON is printed to stdout. This script writes no files,
does not require .git, and never runs Lean, a build, replay, or an axiom audit.
It extracts theorem signatures ending in ':= by' from the five known modules.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

STATUS = "SOURCE_EXTRACTED_NOT_COMPILER_INVENTORY"
MODULES = (
    "ActualUpperPolicyDensity",
    "UpperCoefficientPerturbation",
    "ActualUpperDensityAssembly",
    "RealPhysicalUpperWeightBridge",
    "RealUpperCountingAssembly",
)
DECLARATION = re.compile(
    r"(?m)^(?:@\[[^\n]*?\] )?theorem ([A-Za-z_][A-Za-z0-9_]*)\b"
)
PROOF_DELIMITER = re.compile(r"\s:= by(?:\s|$)")


def extract_module(repo: Path, module: str) -> dict:
    relative = f"ImbalancedChen/{module}.lean"
    source_bytes = (repo / relative).read_bytes()
    source = source_bytes.decode("utf-8")
    declarations = []
    for match in DECLARATION.finditer(source):
        tail = source[match.start():]
        delimiter = PROOF_DELIMITER.search(tail)
        if delimiter is None:
            raise ValueError(f"No ':= by' delimiter: {module}.{match.group(1)}")
        signature = tail[:delimiter.start()].rstrip()
        if len(list(DECLARATION.finditer(signature))) != 1:
            raise ValueError(f"Unexpected declaration boundary: {module}.{match.group(1)}")
        name = match.group(1)
        full_name = f"ImbalancedChen.{name}"
        declarations.append(
            {
                "name": name,
                "full_name": full_name,
                "signature": signature,
                "qualified_signature": signature.replace(
                    "theorem " + name, "theorem " + full_name, 1
                ),
            }
        )
    blob_header = b"blob " + str(len(source_bytes)).encode("ascii") + b"\0"
    return {
        "module": f"ImbalancedChen.{module}",
        "path": relative,
        "imports": [line for line in source.splitlines() if line.startswith("import ")],
        "public_theorem_count": len(declarations),
        "declarations": declarations,
        "sha256": hashlib.sha256(source_bytes).hexdigest(),
        "git_blob_sha1": hashlib.sha1(blob_header + source_bytes).hexdigest(),
        "source_bytes": len(source_bytes),
    }


def verify_saved_inventory(current: dict, saved: dict) -> None:
    if saved.get("status") != STATUS:
        raise ValueError("Saved file is not explicitly a source-only inventory")
    current_files = {item["path"]: item for item in current["files"]}
    saved_files = {item["path"]: item for item in saved["files"]}
    if current_files.keys() != saved_files.keys():
        raise ValueError("Module set differs")
    if current["public_theorem_count"] != saved.get("public_theorem_count"):
        raise ValueError("Public theorem count differs")
    for path, item in current_files.items():
        previous = saved_files[path]
        for field in ("sha256", "git_blob_sha1", "public_theorem_count"):
            if item[field] != previous.get(field):
                raise ValueError(f"{path}: {field} differs")
        if item["declarations"] != previous["declarations"]:
            raise ValueError(f"{path}: original or qualified signatures differ")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path("."))
    parser.add_argument("--expected-count", type=int, default=53)
    parser.add_argument("--check-json", type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    files = [extract_module(repo, module) for module in MODULES]
    total = sum(item["public_theorem_count"] for item in files)
    if total != args.expected_count:
        raise ValueError(f"Expected {args.expected_count} declarations; found {total}")
    data = {
        "status": STATUS,
        "extracted_at_utc": datetime.now(timezone.utc).isoformat(),
        "namespace": "ImbalancedChen",
        "proofs_included": False,
        "full_source_hashes_included": True,
        "public_theorem_count": total,
        "verification_note": "Source-text extraction only; no compiler verification.",
        "qualification_note": (
            "signature preserves the source text. qualified_signature only qualifies "
            "the declared theorem name; all other identifiers retain their original "
            "ImbalancedChen namespace context. This is not compiler elaboration."
        ),
        "files": files,
    }
    if args.check_json is not None:
        path = args.check_json
        if not path.is_absolute():
            path = repo / path
        verify_saved_inventory(data, json.loads(path.read_text()))
        print(json.dumps({
            "status": STATUS,
            "modules": len(files),
            "public_theorems": total,
            "original_signatures_match": True,
            "qualified_signatures_match": True,
            "source_hashes_match": True,
            "compiler_run": False,
        }, ensure_ascii=False))
    else:
        print(json.dumps(data, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()

