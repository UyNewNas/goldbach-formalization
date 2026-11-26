#!/usr/bin/env python3
"""Transport the admission/W-layer export as five exact Git blobs.

Supply --pins with a JSON object containing source_commit and a files map.
Each of the five filenames maps to {"sha256": "...", "size_bytes": n}.
Capture the source commit and owner/runtime digests from the original task,
the group/base receipt and archive digests from the exporter, and byte counts
from the completed export. Keep this manifest separate from the export.

stage writes objects and an additive commit to an isolated bare repository.
publish is the only command that writes an external ref. The work ref
checks are snapshots, not a lock across refs. If a push was attempted and
readback fails, the artifact ref may already have changed. Run readback
against the same validated destination before deciding how to recover.
fetch reads that ref once into a local bare repository and installs verified
bytes in --destination. Run the separate group evidence verifier afterward.
"""

import argparse
from contextlib import contextmanager, nullcontext
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from urllib.parse import urlsplit


ARTIFACT_REF = "refs/heads/artifacts/p36-normalized-density-20261126"
ARTIFACT_BASE = "f86223d06127fb6a0f3394ce4f6479e1e27fcfde"
WORK_REF = "refs/heads/work/p3-6-warm-payment-20261126"
WORK_BASE = "b3f306cc3b430fc40c3b3ec4110d323443d2f609"
ARTIFACT_PREFIX = "admission-w-layer"
PUBLIC_REMOTE = "https://github.com/UyNewNas/goldbach-formalization.git"
CLOUD_BARE = Path("/workspace/p36-authorized-publication-20261126/repository.git")
AUTHORIZED_REPO = Path("/workspace/p36-original-u5-20261125")
LOCKED_REMOTE = "p36-validated-destination"
FILES = (
    "evidence.tar.xz",
    "RECEIPT.json",
    "GROUP_RECEIPT.json",
    "OWNER_MANIFEST.json",
    "GROUP_RUNTIME_BINDING.json",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def is_digest(value, digits):
    return isinstance(value, str) and re.fullmatch(rf"[0-9a-f]{{{digits}}}", value) is not None


def git_env(extra=None, isolated=False):
    env = dict(os.environ, GIT_TERMINAL_PROMPT="0", GIT_NO_LAZY_FETCH="1")
    for key in (
        "GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
        "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE",
    ):
        env.pop(key, None)
    for key in tuple(env):
        if key.startswith("GIT_TRACE") or key == "GIT_CURL_VERBOSE" or (
            isolated and key.startswith("GIT_CONFIG")
        ):
            env.pop(key)
    if isolated:
        env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
    if extra:
        env.update(extra)
    return env


def git(repo, *args, extra_env=None, isolated=False):
    completed = subprocess.run(
        ["git", "-C", os.fspath(repo), *args],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=git_env(extra_env, isolated),
    )
    if completed.returncode:
        # Remote diagnostics can include authenticated URLs.
        raise RuntimeError(f"Git {args[0]} failed with exit {completed.returncode}")
    return completed.stdout


def require_bare(repo):
    require(git(repo, "rev-parse", "--is-bare-repository").strip() == b"true",
            "The transport requires an isolated bare repository")


def load_pins(path):
    pins = json.loads(path.read_bytes())
    require(isinstance(pins, dict) and set(pins) == {"source_commit", "files"},
            "Expected independent source_commit and files pins")
    require(is_digest(pins["source_commit"], 40), "Expected an exact source commit")
    files = pins["files"]
    require(isinstance(files, dict) and set(files) == set(FILES),
            "Expected independent pins for the exact five files")
    for name, pin in files.items():
        require(isinstance(pin, dict) and set(pin) == {"sha256", "size_bytes"},
                f"Expected SHA-256 and byte count for {name}")
        require(is_digest(pin["sha256"], 64), f"Invalid SHA-256 for {name}")
        require(type(pin["size_bytes"]) is int and pin["size_bytes"] > 0,
                f"Invalid byte count for {name}")
    return pins


def verify_file(path, pin):
    require(path.is_file() and not path.is_symlink(), f"Expected a regular file: {path}")
    require(path.stat().st_size == pin["size_bytes"], f"Byte count mismatch: {path}")
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    require(digest == pin["sha256"], f"SHA-256 mismatch: {path}")


def verify_receipt(raw, pins):
    receipt = json.loads(raw)
    require(isinstance(receipt, dict), "Expected a group receipt object")
    files = pins["files"]
    expected = {
        "status": "VERIFIED_OWNED_GROUP_EXPORT",
        "source_commit": pins["source_commit"],
        "archive_sha256": files["evidence.tar.xz"]["sha256"],
        "archive_bytes": files["evidence.tar.xz"]["size_bytes"],
        "base_receipt_sha256": files["RECEIPT.json"]["sha256"],
        "runtime_binding_sha256": files["GROUP_RUNTIME_BINDING.json"]["sha256"],
    }
    for name, value in expected.items():
        require(receipt.get(name) == value, f"Group receipt differs from pin: {name}")
    source_manifest = receipt.get("source_manifest")
    require(isinstance(source_manifest, dict)
            and source_manifest.get("sha256") == files["OWNER_MANIFEST.json"]["sha256"],
            "Group receipt differs from the independent owner manifest pin")
    require(receipt.get("whole_p36_closed") is False and receipt.get("currentVerified") is False,
            "The group receipt must retain its open whole-node status")


def verify_blob(repo, name, oid, pin, output=None):
    digest = hashlib.sha256()
    size = 0
    command = ["git", "-C", os.fspath(repo), "cat-file", "blob", oid]
    with subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=git_env(),
    ) as child:
        while block := child.stdout.read(1024 * 1024):
            digest.update(block)
            size += len(block)
            if output is not None:
                output.write(block)
    require(child.returncode == 0, f"Cannot read exact Git blob for {name}")
    require(size == pin["size_bytes"], f"Git blob byte count mismatch: {name}")
    require(digest.hexdigest() == pin["sha256"], f"Git blob SHA-256 mismatch: {name}")


def verify_commit(repo, commit, pins, destination=None):
    require(is_digest(commit, 40), "Expected an exact artifact commit")
    parents = git(repo, "rev-list", "--parents", "-n", "1", commit).decode().split()
    require(parents == [commit, ARTIFACT_BASE], "Artifact commit must directly extend the pinned parent")
    delta = git(repo, "diff-tree", "--no-commit-id", "--name-status", "--no-renames",
                "-r", "-z", ARTIFACT_BASE, commit).decode().split("\0")[:-1]
    paths = {f"{ARTIFACT_PREFIX}/{name}" for name in FILES}
    require(len(delta) == 2 * len(FILES)
            and set(delta[::2]) == {"A"} and set(delta[1::2]) == paths,
            "Artifact commit must preserve the old tree and add only the five pinned paths")

    records = {}
    for entry in git(repo, "ls-tree", "-r", "-z", commit, "--", ARTIFACT_PREFIX).decode().split("\0")[:-1]:
        info, path = entry.split("\t", 1)
        mode, kind, oid = info.split()
        require(mode == "100644" and kind == "blob" and is_digest(oid, 40),
                f"Expected a regular Git blob: {path}")
        records[path] = oid
    require(set(records) == paths, "Unexpected paths in the staged group artifact tree")
    blobs = {name: records[f"{ARTIFACT_PREFIX}/{name}"] for name in FILES}

    for name, oid in blobs.items():
        stream = (destination / name).open("xb") if destination is not None else nullcontext()
        with stream as output:
            verify_blob(repo, name, oid, pins["files"][name], output)
    verify_receipt(git(repo, "cat-file", "blob", blobs["GROUP_RECEIPT.json"]), pins)
    return {"artifact_commit": commit, "artifact_parent": ARTIFACT_BASE,
            "artifact_ref": ARTIFACT_REF,
            "files": {name: {**pins["files"][name], "git_blob_sha": oid}
                      for name, oid in blobs.items()}}


def stage(source, bare, pins):
    require_bare(bare)
    git(bare, "cat-file", "-e", f"{ARTIFACT_BASE}^{{commit}}")
    for name in FILES:
        verify_file(source / name, pins["files"][name])
    verify_receipt((source / "GROUP_RECEIPT.json").read_bytes(), pins)

    with tempfile.TemporaryDirectory(prefix="p36-artifact-index-") as directory:
        index = {"GIT_INDEX_FILE": str(Path(directory) / "index")}
        git(bare, "read-tree", ARTIFACT_BASE, extra_env=index)
        for name in FILES:
            oid = git(bare, "hash-object", "-w", "--no-filters", "--",
                      str(source / name)).decode().strip()
            git(bare, "update-index", "--add", "--cacheinfo",
                f"100644,{oid},{ARTIFACT_PREFIX}/{name}", extra_env=index)
        tree = git(bare, "write-tree", extra_env=index).decode().strip()
    commit = git(bare, "-c", "user.name=Codex", "-c", "user.email=codex@openai.com",
                 "-c", "commit.gpgsign=false", "commit-tree", tree, "-p", ARTIFACT_BASE,
                 "-m", "Preserve P3.6 admission and W-layer group evidence").decode().strip()
    return {"status": "STAGED_WITHOUT_PUSH", **verify_commit(bare, commit, pins)}


def validate_destination(endpoint):
    message = "Unexpected push destination; expected the pinned GitHub repository over HTTPS"
    require(not re.search(r"[\x00-\x20\x7f]", endpoint), message)
    try:
        url = urlsplit(endpoint)
        port = url.port
    except ValueError:
        raise ValueError(message) from None
    repo_path = "/uynewnas/goldbach-formalization"
    require(url.scheme == "https" and url.hostname == "github.com"
            and port in (None, 443) and not url.query and not url.fragment
            and url.path.casefold() in {repo_path, repo_path + ".git"}, message)


def quote_config(value):
    escapes = {"\\": "\\\\", '"': '\\"', "\n": "\\n", "\t": "\\t", "\b": "\\b"}
    return '"' + "".join(escapes.get(char, char) for char in value) + '"'


def transport_config(authorized, endpoint):
    # Preserve effective authentication and HTTP settings. Copying rewrite or
    # include directives would let Git resolve the already-checked URL again.
    config = []
    for entry in git(authorized, "config", "--includes", "--null", "--list").decode().split("\0"):
        key, separator, value = entry.partition("\n")
        section, _, rest = key.partition(".")
        subsection, _, variable = rest.rpartition(".")
        transport_setting = section in {"http", "https", "credential"} and variable != "followredirects"
        if key in {"remote.origin.proxy", "remote.origin.proxyauthmethod"}:
            subsection = LOCKED_REMOTE
        elif not transport_setting and key != "core.askpass":
            continue
        header = f"[{section} {quote_config(subsection)}]" if subsection else f"[{section}]"
        setting = f"\t{variable} = {quote_config(value)}" if separator else f"\t{variable}"
        config.extend((header, setting))
    config.extend(("[http]", "\tfollowRedirects = false",
                   f'[remote "{LOCKED_REMOTE}"]', f"\turl = {quote_config(endpoint)}"))
    return "\n".join(config) + "\n"


@contextmanager
def locked_destination(authorized):
    endpoints = git(authorized, "remote", "get-url", "--push", "--all", "origin").decode().splitlines()
    require(len(endpoints) == 1, "Expected exactly one configured push destination")
    endpoint = endpoints[0]
    validate_destination(endpoint)
    with tempfile.TemporaryDirectory(prefix="p36-locked-destination-") as directory:
        repo = Path(directory)
        git(repo, "init", "--quiet", "--bare", "--template=", isolated=True)
        config = repo / "config"
        config.chmod(0o600)
        with config.open("a", encoding="utf-8") as output:
            output.write(transport_config(authorized, endpoint))
        yield repo


def read_refs(destination):
    refs = {}
    response = git(destination, "ls-remote", "--refs", LOCKED_REMOTE, WORK_REF, ARTIFACT_REF,
                   isolated=True)
    for line in response.decode().splitlines():
        oid, ref = line.split()
        require(ref in {WORK_REF, ARTIFACT_REF} and ref not in refs and is_digest(oid, 40),
                "Unexpected remote ref response")
        refs[ref] = oid
    require(set(refs) == {WORK_REF, ARTIFACT_REF}, "Both prerequisite remote refs must exist")
    return refs


def publish(bare, authorized, commit, pins):
    require_bare(bare)
    result = verify_commit(bare, commit, pins)
    with locked_destination(authorized) as destination:
        before = read_refs(destination)
        require(before[WORK_REF] == WORK_BASE, "Remote work ref differs from the pinned base")
        require(before[ARTIFACT_REF] in {ARTIFACT_BASE, commit},
                "Remote artifact ref moved from the pinned parent")
        if before[ARTIFACT_REF] != commit:
            alternates = {"GIT_ALTERNATE_OBJECT_DIRECTORIES": str(bare / "objects")}
            try:
                git(destination, "push", "--porcelain", "--no-follow-tags", "--recurse-submodules=no",
                    LOCKED_REMOTE, f"{commit}:{ARTIFACT_REF}", extra_env=alternates, isolated=True)
                after = read_refs(destination)
            except (RuntimeError, ValueError) as exc:
                raise RuntimeError(
                    f"{exc}. The artifact ref may already have changed; run readback for {commit}."
                ) from None
        else:
            after = before
    require(after == {WORK_REF: WORK_BASE, ARTIFACT_REF: commit},
            f"Readback changed across the artifact push: {after}. "
            f"The artifact ref may already have changed; run readback for {commit}.")
    return {"status": "ARTIFACT_REF_VERIFIED", **result,
            "remote_refs_before": before, "remote_refs_after": after}


def readback(authorized, commit):
    require(is_digest(commit, 40), "Expected an exact artifact commit")
    with locked_destination(authorized) as destination:
        refs = read_refs(destination)
    return {"status": "READBACK_ONLY", "remote_refs": refs,
            "artifact_matches_requested_commit": refs[ARTIFACT_REF] == commit,
            "work_matches_pinned_base": refs[WORK_REF] == WORK_BASE}


def fetch(bare, destination, commit, remote, pins):
    require(is_digest(commit, 40), "Expected an exact artifact commit")
    require_bare(bare)
    baseline = subprocess.run(
        ["git", "-C", os.fspath(bare), "cat-file", "-e", f"{ARTIFACT_BASE}^{{commit}}"],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=git_env(),
    )
    negotiation = [f"--negotiation-tip={ARTIFACT_BASE}"] if baseline.returncode == 0 else []
    git(bare, "fetch", "--depth=2", "--no-tags", "--no-recurse-submodules",
        "--no-auto-maintenance", *negotiation, "--", remote, ARTIFACT_REF)
    require(git(bare, "rev-parse", "FETCH_HEAD").decode().strip() == commit,
            "Fetched artifact ref differs from the independently pinned commit")

    require(not destination.is_symlink(), "Evidence destination must be a regular directory")
    destination.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".p36-artifact-", dir=destination) as directory:
        staging = Path(directory)
        result = verify_commit(bare, commit, pins, staging)
        for name in FILES:
            target = destination / name
            if target.exists() or target.is_symlink():
                verify_file(target, pins["files"][name])
        for name in FILES:
            target = destination / name
            try:
                os.link(staging / name, target)
            except FileExistsError:
                verify_file(target, pins["files"][name])
    return {"status": "FIVE_FILES_RETRIEVED_AND_VERIFIED", **result,
            "destination": str(destination)}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pins", type=Path, required=True,
                        help="independent original/export hashes and file sizes")
    actions = parser.add_subparsers(dest="action", required=True)
    staging = actions.add_parser("stage", help="verify originals and build the local Git commit")
    staging.add_argument("--source", type=Path, required=True, help="completed exporter output directory")
    staging.add_argument("--bare", type=Path, default=CLOUD_BARE)
    writing = actions.add_parser("publish", help="write only the existing artifact ref by fast-forward")
    writing.add_argument("--commit", required=True, help="exact SHA emitted by stage")
    writing.add_argument("--bare", type=Path, default=CLOUD_BARE)
    writing.add_argument("--authorized", type=Path, default=AUTHORIZED_REPO)
    recovery = actions.add_parser("readback", help="read both refs after an ambiguous push without writing")
    recovery.add_argument("--commit", required=True, help="exact intended artifact SHA")
    recovery.add_argument("--authorized", type=Path, default=AUTHORIZED_REPO)
    reading = actions.add_parser("fetch", help="fetch once and install the five verified files")
    reading.add_argument("--commit", required=True, help="exact published artifact SHA")
    reading.add_argument("--bare", type=Path, required=True, help="isolated local fetch repository")
    reading.add_argument("--destination", type=Path, required=True)
    reading.add_argument("--remote", default=PUBLIC_REMOTE)
    args = parser.parse_args(argv)
    pins = load_pins(args.pins)
    if args.action == "stage":
        result = stage(args.source.resolve(), args.bare.resolve(), pins)
    elif args.action == "publish":
        result = publish(args.bare.resolve(), args.authorized.resolve(), args.commit, pins)
    elif args.action == "readback":
        result = readback(args.authorized.resolve(), args.commit)
    else:
        result = fetch(args.bare.resolve(), args.destination.absolute(), args.commit, args.remote, pins)
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
