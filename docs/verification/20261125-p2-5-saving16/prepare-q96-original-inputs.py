#!/usr/bin/env python3
"""Install only the fourteen authenticated original saving16 witness files.

Run from the actual P2 project root under /workspace. This is raw-input
preparation, not a Lean proof, parser replay, numerical check or acceptance.
Reuse matching files and archives; never overwrite another target's bytes.
The ZIP/member verification follows the existing full87 v3 installer.
"""
from pathlib import Path
import collections
import hashlib
import json
import os
import shutil
import stat
import subprocess
import tempfile
import zipfile


MANIFEST_SHA = "79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0"
ASSET_BYTES = 323605374
ASSET_SHA = "8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1"
ASSET_URL = (
    "https://github.com/UyNewNas/chen-imbalanced-semiprimes/"
    "releases/download/v2026.10.10/chen-numerical-evidence-20261010.zip"
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha_file(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def verify(path, row):
    require(stat.S_ISREG(path.lstat().st_mode), f"Not a regular file: {path}")
    require(path.stat().st_size == row["bytes"], f"Size mismatch: {path}")
    require(sha_file(path) == row["sha256"], f"SHA mismatch: {path}")


def find_cached_archive(workspace, observations):
    # Read-only discovery avoids downloading an original archive already here.
    # Do not follow directory symlinks or inspect Git object stores.
    for directory, dirs, files in os.walk(workspace, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d != ".git")
        for name in sorted(files):
            if not name.lower().endswith(".zip"):
                continue
            path = Path(directory) / name
            try:
                info = path.lstat()
                if not stat.S_ISREG(info.st_mode) or info.st_size != ASSET_BYTES:
                    continue
                actual = sha_file(path)
                observations.append({"path": str(path), "bytes": info.st_size,
                                     "sha256": actual, "matches": actual == ASSET_SHA})
                if actual == ASSET_SHA:
                    return path
            except FileNotFoundError:
                continue
    return None


def main():
    repo = Path.cwd().resolve()
    workspace = Path("/workspace")
    require(repo.parent == workspace, "Run from the actual P2 project root")
    require((repo / "ImbalancedChen/P2OriginalSaving16OriginalArchive.lean").is_file(),
            "Missing original archive source")
    manifest = repo / (
        "docs/verification/20261125-p2-5-saving16/"
        "Q96_EXISTING_INPUTS_AND_SOURCES.json"
    )
    raw = manifest.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == MANIFEST_SHA, "Manifest changed")
    rows = json.loads(raw)["saving16_inputs"]
    ids = [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14]
    names = [f"eighth-prefix-family-20261009-cell-{i:02}.witness.json" for i in ids]
    prefix = "chen-numerical-evidence-20261010-renewal-v2/goldbach-research/"
    require(len(rows) == 14, "Expected exactly fourteen original inputs")
    require([r["install_path"] for r in rows] ==
            ["../goldbach-research/" + n for n in names], "Unexpected input paths")
    require(sum(r["bytes"] for r in rows) == 93508187, "Input lengths changed")
    for row, name in zip(rows, names):
        require(row["origin"] == {"kind": "release_member", "member": prefix + name},
                "Unexpected original member")
    dest = workspace / "goldbach-research"
    require(not dest.is_symlink(), "Destination directory is a symlink")
    require(not dest.exists() or dest.is_dir(), "Destination is not a directory")
    missing = []
    for row, name in zip(rows, names):
        path = dest / name
        if os.path.lexists(path):
            verify(path, row)
        else:
            missing.append((row, name))

    installed, cache_observations = [], []
    cached_archive = None
    whole_zip_verified = False
    free_before = shutil.disk_usage(workspace).free
    if missing:
        cached_archive = find_cached_archive(workspace, cache_observations)
        required = sum(r["bytes"] for r, _ in missing)
        if cached_archive is None:
            required += ASSET_BYTES
        require(shutil.disk_usage(workspace).free >= required + 256 * 1024 * 1024,
                "Insufficient space for the bounded raw-input staging operation")
        with tempfile.TemporaryDirectory(prefix="p25-q96-inputs-", dir=workspace) as temporary:
            staging = Path(temporary)
            archive = cached_archive or staging / "original-release.zip"
            if cached_archive is None:
                subprocess.run([
                    "curl", "--fail", "--location", "--retry", "3",
                    "--connect-timeout", "20", "--max-time", "900",
                    "--proto", "=https", "--proto-redir", "=https",
                    "--max-filesize", str(ASSET_BYTES),
                    ASSET_URL, "--output", str(archive),
                ], check=True, timeout=1000)
            require(archive.stat().st_size == ASSET_BYTES, "Release ZIP size differs")
            require(sha_file(archive) == ASSET_SHA, "Release ZIP SHA differs")
            whole_zip_verified = True
            with zipfile.ZipFile(archive) as z:
                counts = collections.Counter(z.namelist())
                require(all(c == 1 for c in counts.values()), "Duplicate ZIP members")
                # Verify all missing members before installing any target.
                for row, name in missing:
                    member = row["origin"]["member"]
                    require(counts[member] == 1, f"Missing member: {member}")
                    info = z.getinfo(member)
                    require(not info.is_dir() and info.file_size == row["bytes"],
                            f"Unexpected member length: {member}")
                    staged = staging / name
                    with z.open(info) as source, staged.open("xb") as out:
                        shutil.copyfileobj(source, out, length=1024 * 1024)
                    verify(staged, row)
            require(not dest.is_symlink(), "Destination changed to a symlink")
            dest.mkdir(exist_ok=True)
            for row, name in missing:
                target = dest / name
                try:
                    os.link(staging / name, target)
                    installed.append(name)
                except FileExistsError:
                    verify(target, row)

    for row, name in zip(rows, names):
        verify(dest / name, row)
    result = {
        "status": "RAW_INPUTS_READY_NO_LEAN_OR_NUMERICAL_REPLAY",
        "manifest_sha256": MANIFEST_SHA,
        "expected_release_sha256": ASSET_SHA,
        "whole_zip_verified_this_run": whole_zip_verified,
        "reused_archive": str(cached_archive) if cached_archive else None,
        "archive_cache_observations": cache_observations,
        "destination": str(dest), "file_count": len(rows),
        "total_bytes": sum(r["bytes"] for r in rows),
        "newly_installed": installed,
        "disk_free_before": free_before,
        "disk_free_after": shutil.disk_usage(workspace).free,
        "files": [{"name": n, "bytes": r["bytes"], "sha256": r["sha256"]}
                  for r, n in zip(rows, names)],
        "compiled": False, "kernel_verified": False,
        "numerical_replay_performed": False,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
