"""Read-only verification of the original pins or one exact historical overlay.

This module never applies a patch, updates an index, or runs Lean/network commands.
The historical acceptance files are provenance, not permission to change sources.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess


TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
PINS = {
    "goldbach": "09b97db5764ade1246bfb77206baa1b124760958",
    "mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
    "LeanArchitect": "78dd66840d3efe8c824c699fc03381cec817c271",
    "plausible": "b1c4a69a7e247ab7df20460212001673d74f08c0",
    "LeanSearchClient": "0498c7c070c143a3bf7379f4d99a2c63bb9d9715",
    "importGraph": "18a90119a5d316358fde6c86e0ca24e59212e32c",
    "proofwidgets": "b1436dc749e722c9920036b52cdc43b3451d0b69",
    "aesop": "57d3325be72a842920813bcb40f96a6f7393c185",
    "Qq": "ee41917ae11d38479fb8fb24745f7ca4bf0a784d",
    "batteries": "41bd267b3f6b7252f6676af46d4ffc6783b64de9",
    "Cli": "da07ca808b6718cb2aed14dba154e5a08b8f8ecf",
}
BUNDLE = "verification/dependency-overlays/stage002"
BUNDLE_SHA256 = {
    "verification/dependency-overlays/apply.py": "5d634a74ba657bcf3a99d75597c6fcbce021e658fd5948af09f6174c2e02f407",
    BUNDLE + "/manifest.json": "4abf90022ae71d5202744fcc6c491794d614c23b12ef8df117699f96a5c10f41",
    BUNDLE + "/activation.json": "aa07d40f5e319e2654031fff941c1f444dfedd682eeec29fdf4b4ad3426591ef",
    BUNDLE + "/acceptance-review.json": "4b4ddac9fab8953b06c1b0c2960a3ae82349369c03afc89b8001ee91909aa543",
    BUNDLE + "/dependency.patch": "4560aec58248a79a45b7261b635851a95e2e33e994d0a6dc18d266248bb71820",
}
OVERLAY_FILES = frozenset({
    "MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiFiniteAbel.lean",
    "MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvrySmoothCutoff.lean",
    "MathlibNt/SieveTheory/LiLiuGoldbachOnePlusOneNineFinite.lean",
})
EVIDENCE_FILES = ("verification/parts/p0/verify_dependency_state.py", *BUNDLE_SHA256)
STATES = ("original-clean", "goldbach-stage002-exact")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_path(root: Path, relative: str) -> Path:
    part = PurePosixPath(relative)
    require(bool(part.parts) and not part.is_absolute() and str(part) == relative
            and all(p not in (".", "..") for p in part.parts) and "\\" not in relative,
            f"Unsafe relative path: {relative}")
    target = root
    for name in part.parts:
        target = target / name
        require(not target.is_symlink(), f"Symlink path rejected: {relative}")
    require(target.resolve().is_relative_to(root), f"Path escaped root: {relative}")
    return target


def git(directory: Path, *args: str) -> bytes:
    # Do not allow inherited Git routing or optional index refreshes to affect this check.
    environment = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    environment["GIT_OPTIONAL_LOCKS"] = "0"
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-c", "core.fsmonitor=false", "-c", "core.fileMode=true",
         "-c", "diff.autoRefreshIndex=false", "-c", "core.trustctime=true",
         "-c", "core.checkStat=default",
         "-C", str(directory), *args], env=environment, stderr=subprocess.PIPE)


def zero_paths(data: bytes) -> list[str]:
    return [item.decode("utf-8") for item in data.split(b"\0") if item]


def load_overlay(root: Path) -> tuple[dict, dict[str, str]]:
    payloads = {}
    for relative, expected in BUNDLE_SHA256.items():
        target = safe_path(root, relative)
        require(target.is_file(), f"Missing historical overlay evidence: {relative}")
        payloads[relative] = target.read_bytes()
        require(sha256(payloads[relative]) == expected,
                f"Historical overlay evidence hash changed: {relative}")
    manifest = json.loads(payloads[BUNDLE + "/manifest.json"])
    activation = json.loads(payloads[BUNDLE + "/activation.json"])
    review = json.loads(payloads[BUNDLE + "/acceptance-review.json"])
    require(activation.get("status") == "PASS"
            and activation.get("manifestSha256") == BUNDLE_SHA256[BUNDLE + "/manifest.json"]
            and activation.get("reviewSha256") == BUNDLE_SHA256[BUNDLE + "/acceptance-review.json"],
            "Historical overlay activation binding differs")
    require(manifest.get("package") == "goldbach" and manifest.get("basePin") == PINS["goldbach"]
            and manifest.get("patchFile") == "dependency.patch"
            and manifest.get("patchSha256") == BUNDLE_SHA256[BUNDLE + "/dependency.patch"]
            and set(manifest.get("files", {})) == OVERLAY_FILES,
            "Historical overlay manifest identity differs")
    require(review.get("status") == "PASS" and review.get("basePin") == PINS["goldbach"]
            and review.get("manifestSha256") == activation["manifestSha256"]
            and review.get("overlayPatchSha256") == manifest["patchSha256"]
            and review.get("files") == manifest["files"]
            and review.get("ciIntegrationReview", {}).get("applyScriptSha256")
                == BUNDLE_SHA256["verification/dependency-overlays/apply.py"],
            "Historical overlay acceptance binding differs")
    return manifest, {relative: sha256(data) for relative, data in payloads.items()}


def verify_dependency_state(root: Path, expected_state: str = "original-clean") -> dict:
    require(expected_state in STATES, f"Unknown expected dependency state: {expected_state}")
    root = Path(root).resolve(strict=True)
    require(safe_path(root, "lean-toolchain").read_text().strip() == TOOLCHAIN, "Toolchain pin changed")
    lock_bytes = safe_path(root, "lake-manifest.json").read_bytes()
    lock = json.loads(lock_bytes)
    packages = lock["packages"]
    require(len(packages) == len(PINS) and len({p["name"] for p in packages}) == len(PINS)
            and {p["name"]: p["rev"] for p in packages} == PINS,
            "Manifest pins changed")
    require(lock.get("packagesDir") == ".lake/packages"
            and all(p.get("type") == "git" for p in packages), "Unexpected dependency materialization")
    manifest, bundle_hashes = (load_overlay(root) if expected_state == "goldbach-stage002-exact"
                               else (None, {}))
    heads, changes, files = {}, {}, {}
    for name, revision in PINS.items():
        package = safe_path(root, ".lake/packages/" + name)
        require(package.is_dir(), f"Missing materialized dependency: {name}")
        require(git(package, "rev-parse", "--show-toplevel").decode().strip() == str(package),
                f"{name}: not the dependency Git root")
        actual = git(package, "rev-parse", "HEAD").decode().strip()
        require(actual == revision, f"{name}: checkout revision differs")
        heads[name] = actual
        flags = git(package, "ls-files", "-v", "-z").split(b"\0")
        require(all(not entry or entry.startswith(b"H ") for entry in flags),
                f"{name}: hidden/skip-worktree index entries rejected")
        require(not git(package, "ls-files", "--unmerged", "-z"), f"{name}: unmerged index entries")
        require(not git(package, "diff", "--no-ext-diff", "--cached", "--name-only", "-z", "HEAD", "--"),
                f"{name}: staged dependency changes rejected")
        status_entries = zero_paths(git(package, "status", "--porcelain=v1", "-z",
                                        "--untracked-files=no", "--no-renames"))
        require(all(len(entry) > 3 and entry[2] == " " for entry in status_entries),
                f"{name}: malformed tracked status")
        changed = [entry[3:] for entry in status_entries]
        changes[name] = sorted(changed)
        if name != "goldbach" or expected_state == "original-clean":
            require(not changed, f"{name}: tracked dependency files changed")
        else:
            require(set(changed) == OVERLAY_FILES and len(changed) == len(OVERLAY_FILES),
                    "goldbach: tracked changes are not exactly the historical three-file overlay")
        if name == "goldbach":
            require(not git(package, "ls-files", "--others", "--exclude=.lake/", "-z"),
                    "goldbach: extra untracked dependency content outside .lake")
        if name == "goldbach" and manifest is not None:
            for relative, metadata in manifest["files"].items():
                target = safe_path(package, relative)
                require(target.is_file() and stat.S_ISREG(target.stat().st_mode),
                        f"Missing regular overlay source: {relative}")
                require(target.stat().st_mode & 0o111 == 0, f"Executable overlay source: {relative}")
                tree = git(package, "ls-tree", "-z", "HEAD", "--", relative)
                header, separator, path = tree.rstrip(b"\0").partition(b"\t")
                entry = header.decode().split()
                require(separator == b"\t" and path.decode() == relative and len(entry) == 3
                        and entry[0] == "100644" and entry[1] == "blob"
                        and entry[2] == metadata["baseGitBlob"], f"Base blob/mode mismatch: {relative}")
                base_hash = sha256(git(package, "show", "HEAD:" + relative))
                require(base_hash == metadata["baseSha256"], f"Base source SHA mismatch: {relative}")
                actual_hash = sha256(target.read_bytes())
                require(actual_hash == metadata["patchedSha256"], f"Patched source SHA mismatch: {relative}")
                files[relative] = {"base_git_blob": entry[2], "base_sha256": base_hash,
                                   "working_sha256": actual_hash, "git_mode": entry[0],
                                   "working_executable": False}
    return {
        "schema": "p0-dependency-state-v1", "expected_state": expected_state,
        "source_classification": ("historical exact patched dependency, not original fixed source"
                                  if manifest is not None else "original fixed source, tracked-clean"),
        "toolchain": TOOLCHAIN, "manifest_sha256": sha256(lock_bytes),
        "package_heads": heads, "tracked_changed_files": changes,
        "goldbach_base_pin": PINS["goldbach"],
        "overlay_patch_sha256": manifest["patchSha256"] if manifest is not None else None,
        "overlay_evidence_sha256": bundle_hashes, "overlay_sources": files,
        "dependency_mutation_performed": False,
    }
