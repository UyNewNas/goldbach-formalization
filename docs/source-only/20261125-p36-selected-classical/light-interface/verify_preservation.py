#!/usr/bin/env python3
"""Check exact extraction bytes without invoking Lean or accessing the network.

Provide original immutable blobs in --blob-dir directories (filenames are Git
blob SHA-1s), or in --git-repo object stores. This verifies source preservation;
it does not certify elaboration, compilation, or kernel acceptance.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git_blob_hash(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository-root", type=Path, required=True)
    parser.add_argument("--blob-dir", type=Path, action="append", default=[])
    parser.add_argument("--git-repo", type=Path, action="append", default=[])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    root = args.repository_root.resolve()
    audit_path = Path(__file__).with_name("PRESERVATION.json")
    audit = json.loads(audit_path.read_text())
    git_repos = [root] + args.git_repo

    def original(blob):
        for folder in args.blob_dir:
            path = folder / blob
            if path.is_file():
                data = path.read_bytes()
                assert git_blob_hash(data) == blob, ("bad original blob", blob)
                return data
        for repo in git_repos:
            result = subprocess.run(
                ["git", "-C", str(repo), "cat-file", "blob", blob],
                capture_output=True,
                env={**os.environ, "GIT_NO_LAZY_FETCH": "1"},
                timeout=10,
            )
            if result.returncode == 0:
                assert git_blob_hash(result.stdout) == blob
                return result.stdout
        raise RuntimeError("Exact original blob unavailable locally: " + blob)

    core_bytes = {}
    for row in audit["cores"]:
        data = (root / row["path"]).read_bytes()
        assert sha256(data) == row["sha256"], row["path"]
        core_bytes[row["module"]] = data

    declarations_by_module = {}
    for row in audit["declarations"]:
        declarations_by_module.setdefault(row["source_module"], []).append(row)
    checked_declarations = 0
    checked_wrappers = []
    for row in audit["compatibility_files"]:
        data = original(row["original_git_blob"])
        assert sha256(data) == row["original_sha256"], row["module"]
        patched = (root / row["compatibility_path"]).read_bytes()
        assert sha256(patched) == row["compatibility_sha256"], row["compatibility_path"]
        prefix = "".join("import " + x + "\n" for x in row["added_core_imports"]).encode()
        assert patched.startswith(prefix)
        kept = patched[len(prefix):]
        for change in reversed(row["import_replacements"]):
            old, new = change["old"].encode(), change["new"].encode()
            assert kept.count(new) == 1, (row["module"], new)
            kept = kept.replace(new, old, 1)
        spans = sorted(declarations_by_module.get(row["module"], []),
                       key=lambda x: x["source_start_byte"])
        reconstructed = b""
        previous_end = 0
        for declaration in spans:
            start, end = declaration["source_start_byte"], declaration["source_end_byte"]
            block = data[start:end]
            assert sha256(block) == declaration["statement_and_body_sha256"]
            assert core_bytes[declaration["destination_module"]].count(block) == 1
            retained_length = start - previous_end
            assert retained_length >= 0
            reconstructed += kept[:retained_length] + block
            kept = kept[retained_length:]
            previous_end = end
            checked_declarations += 1
        reconstructed += kept
        assert reconstructed == data, row["module"]
        checked_wrappers.append(row["module"])

    assert checked_declarations == audit["extracted_declaration_count"]
    # These words are forbidden as commands/tactics in new core code. Remove
    # Lean comments before scanning so prose cannot produce a false result.
    forbidden = []
    for module, data in core_bytes.items():
        text = data.decode()
        text = re.sub(r"/-[\s\S]*?-/", "", text)
        text = re.sub(r"(?m)--[^\n]*", "", text)
        words = re.findall(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", text)
        if words:
            forbidden.append({"module": module, "words": words})
    assert not forbidden, forbidden
    report = {
        "status": "EXACT_SOURCE_PRESERVATION_VERIFIED_NOT_LEAN_ACCEPTANCE",
        "preservation_manifest_sha256": sha256(audit_path.read_bytes()),
        "core_files_checked": len(core_bytes),
        "verbatim_declarations_checked": checked_declarations,
        "compatibility_files_reconstructed": len(checked_wrappers),
        "all_reconstructed_originals_equal": True,
        "forbidden_commands_in_cores": forbidden,
        "network_access": False,
        "compiler_invoked": False,
        "kernel_acceptance_claimed": False,
    }
    output = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
