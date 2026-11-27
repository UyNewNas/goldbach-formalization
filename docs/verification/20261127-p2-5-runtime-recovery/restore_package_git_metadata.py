#!/usr/bin/env python3
"""Restore absent package Git metadata from real pinned upstream checkouts.

No package source or build artifact is replaced. A new .git pointer refers to a
genuine fetched checkout; this does not reconstruct historical verification
receipts or change the external qualification gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import lzma
import os
from pathlib import Path
import subprocess

SNAPSHOT_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
PACKAGES = {
    "LeanArchitect": ("https://github.com/hanwenzhu/LeanArchitect.git", "78dd66840d3efe8c824c699fc03381cec817c271"),
    "goldbach": ("https://github.com/subfish-zhou/goldbach-lean.git", "09b97db5764ade1246bfb77206baa1b124760958"),
}


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def verify_package_files(snapshot, root):
    files = {name: row for name, row in snapshot["files"].items()
             if Path(name).is_relative_to(root)}
    require(files, "No frozen files under package root")
    for name, row in files.items():
        path = Path(name)
        require(path.is_file() and path.stat().st_size == row["bytes"]
                and digest(path) == row["sha256"], "Frozen package file differs: " + name)
    return {"files": len(files), "expected_map_sha256": hashlib.sha256(
        json.dumps(files, sort_keys=True, separators=(",", ":")).encode()).hexdigest()}


def run(args):
    raw = lzma.decompress(args.snapshot.read_bytes())
    require(hashlib.sha256(raw).hexdigest() == SNAPSHOT_SHA, "Snapshot identity differs")
    snapshot = json.loads(raw)
    out = args.out_dir.absolute()
    out.mkdir(parents=True, exist_ok=False)
    report = {"schema": "p25-genuine-package-git-metadata-recovery-v1",
              "snapshot_sha256": SNAPSHOT_SHA, "packages": {},
              "package_sources_or_artifacts_replaced": False,
              "historical_receipts_reconstructed": False,
              "original_external_snapshot_verified": False,
              "compile_credit": False, "R19_accepted": False, "P2_5_proved": False}
    try:
        for name, (url, pin) in PACKAGES.items():
            entry = snapshot["packages"][name]
            require(entry["commit"] == pin, "Package snapshot pin differs")
            root = Path(entry["root"])
            require(root.is_dir() and not root.is_symlink(), "Expected real existing package directory")
            pointer = root / ".git"
            require(not pointer.exists() and not pointer.is_symlink(), "Refuse to replace existing Git metadata")
            before = verify_package_files(snapshot, root)
            checkout = out / name
            commands = [["git", "init", "--quiet", str(checkout)],
                        ["git", "-C", str(checkout), "remote", "add", "origin", url],
                        ["git", "-C", str(checkout), "fetch", "--depth", "1", "origin", pin],
                        ["git", "-C", str(checkout), "checkout", "--quiet", "--detach", pin]]
            log = out / (name + ".log")
            with log.open("x") as stream:
                for command in commands:
                    subprocess.run(command, check=True, stdout=stream, stderr=subprocess.STDOUT,
                                   timeout=180, env=dict(os.environ, GIT_TERMINAL_PROMPT="0"))
            actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
            require(actual == pin, "Fetched Git object differs from lock")
            subprocess.run(["git", "-C", str(checkout), "config", "core.worktree", str(root)], check=True)
            require(verify_package_files(snapshot, root) == before, "Package bytes changed during metadata fetch")
            pointer_body = "gitdir: " + str(checkout / ".git") + "\n"
            with pointer.open("x") as stream:
                stream.write(pointer_body)
                stream.flush()
                os.fsync(stream.fileno())
            head = subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
            top = subprocess.check_output(["git", "-C", str(root), "rev-parse", "--show-toplevel"], text=True).strip()
            require(head == pin and Path(top).resolve() == root.resolve(), "Restored Git metadata resolves incorrectly")
            require(verify_package_files(snapshot, root) == before, "Package bytes changed after metadata publication")
            report["packages"][name] = {"root": str(root), "upstream": url, "commit": pin,
                "fetched_checkout": str(checkout), "commands": commands, "frozen_files": before,
                "git_pointer_sha256": digest(pointer), "log_sha256": digest(log),
                "status": "GENUINE_PINNED_GIT_METADATA_RESTORED"}
            print("RESTORED_GENUINE_PACKAGE_GIT", name, pin, flush=True)
        report["status"] = "BOTH_PACKAGE_METADATA_RESTORED_WITH_FROZEN_BYTES_UNCHANGED"
    except Exception as error:
        report.update(status="INCOMPLETE", error=str(error))
        raise
    finally:
        (out / "GIT_METADATA_RESULT.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    run(parser.parse_args())
