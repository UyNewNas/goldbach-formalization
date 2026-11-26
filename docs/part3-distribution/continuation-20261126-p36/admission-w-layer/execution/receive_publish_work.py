#!/usr/bin/env python3
"""Verify a frozen publication pack, then optionally fast-forward the work ref.

Use the explicit actions verify, publish or readback. Only publish writes an
external ref. Authentication and destination locking come from the independently
reviewed, SHA-pinned sibling transport module. The two remote ref checks are
snapshots, not an atomic cross-ref lock. After an ambiguous push, use readback;
it performs no pack installation or remote mutation.
"""

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys


BASE = "b3f306cc3b430fc40c3b3ec4110d323443d2f609"
ARTIFACT = "59cf6341935bc0b8b780526e2d9d2f12d5f1a893"
ARTIFACT_PARENT = "f86223d06127fb6a0f3394ce4f6479e1e27fcfde"
WORK_REF = "refs/heads/work/p3-6-warm-payment-20261126"
ARTIFACT_REF = "refs/heads/artifacts/p36-normalized-density-20261126"
TRANSPORT_SHA256 = "7652ccfee12b1496928d0ff68c28ba68929195ec1201b60f0a9cadf5aaa1c4ee"
INCREMENT = "docs/part3-distribution/continuation-20261126-p36/admission-w-layer"
EVIDENCE_FILES = {"evidence.tar.xz", "RECEIPT.json", "GROUP_RECEIPT.json",
                  "OWNER_MANIFEST.json", "GROUP_RUNTIME_BINDING.json"}
REQUIRED_FILES = {"publication.pack", "publication.idx", "ALL_OBJECTS.txt",
                  "PACKED_OBJECTS.txt", "EXCLUDED_EVIDENCE_BLOBS.json",
                  "CHANGED_FILES.json", "VERIFY_PACK.txt"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value, length):
    return isinstance(value, str) and re.fullmatch(rf"[0-9a-f]{{{length}}}", value) is not None


def file_pin(path):
    require(path.is_file() and not path.is_symlink(), f"Expected a regular file: {path.name}")
    with path.open("rb") as stream:
        sha = hashlib.file_digest(stream, "sha256").hexdigest()
    return {"sha256": sha, "size_bytes": path.stat().st_size}


def load_transport():
    path = Path(__file__).with_name("transport_group_artifacts.py")
    require(path.is_file() and not path.is_symlink(), "Expected the reviewed transport source file")
    source = path.read_bytes()
    require(hashlib.sha256(source).hexdigest() == TRANSPORT_SHA256, "Reviewed transport module hash mismatch")
    spec = importlib.util.spec_from_file_location("p36_reviewed_artifact_transport", path)
    module = importlib.util.module_from_spec(spec)
    exec(compile(source, str(path), "exec"), module.__dict__)
    require(module.WORK_REF == WORK_REF and module.ARTIFACT_REF == ARTIFACT_REF,
            "Reviewed transport ref constants differ")
    return module


def git(transport, repo, *args, stdin=None, extra_env=None):
    env = transport.git_env(extra_env, isolated=True)
    # Proof/closure checks must inspect the actual object graph. Auth and URL
    # handling remain exclusively in the reviewed locked_destination context.
    for name in ("GIT_SHALLOW_FILE", "GIT_REPLACE_REF_BASE", "GIT_GRAFT_FILE"):
        env.pop(name, None)
    env.update(GIT_NO_REPLACE_OBJECTS="1", GIT_GRAFT_FILE=os.devnull)
    result = subprocess.run(
        ["git", "--no-replace-objects", "-C", str(repo), *args], stdin=stdin,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=env,
    )
    if result.returncode:
        raise RuntimeError(f"Git {args[0]} failed with exit {result.returncode}")
    return result.stdout, result.stderr


def gout(transport, repo, *args):
    return git(transport, repo, *args)[0]


def entry(transport, repo, commit, path):
    rows = gout(transport, repo, "ls-tree", "-z", commit, "--", path).split(b"\0")[:-1]
    if not rows:
        return None
    require(len(rows) == 1, f"Expected one committed path: {path}")
    info, actual = rows[0].decode().split("\t", 1)
    mode, kind, oid = info.split()
    require(actual == path and kind == "blob" and mode in {"100644", "100755", "120000"}
            and digest(oid, 40), f"Unsupported committed path: {path}")
    raw = gout(transport, repo, "cat-file", "blob", oid)
    return {"mode": mode, "kind": kind, "git_blob_sha": oid,
            "size_bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def object_ids(path):
    raw = path.read_bytes()
    rows = raw.decode().splitlines()
    require(rows and all(digest(row, 40) for row in rows)
            and rows == sorted(set(rows))
            and raw == "".join(row + "\n" for row in rows).encode(),
            f"Expected a canonical exact object inventory: {path.name}")
    return set(rows)


def save(directory, filename, value):
    raw = (json.dumps(value, indent=2) + "\n").encode()
    stem, suffix = Path(filename).stem, Path(filename).suffix
    for index in range(1000):
        name = filename if index == 0 else f"{stem}.{index:03d}{suffix}"
        path = directory / name
        try:
            with path.open("xb") as output:
                output.write(raw)
            return path
        except FileExistsError:
            require(path.is_file() and not path.is_symlink(), "Unexpected existing receiver record")
            if path.read_bytes() == raw:
                return path
    raise RuntimeError("Too many retained receiver records")


def verify(args, transport):
    directory, bare = args.input_dir, args.bare
    manifest_path = directory / "PACK_MANIFEST.json"
    require(file_pin(manifest_path)["sha256"] == args.manifest_sha256,
            "Manifest differs from the independently supplied SHA-256")
    manifest = json.loads(manifest_path.read_bytes())
    expected = {"status": "EXACT_NON_THIN_PUBLICATION_PACK_VERIFIED_LOCALLY",
                "base_commit": BASE, "target_commit": args.commit,
                "artifact_commit": ARTIFACT, "artifact_parent": ARTIFACT_PARENT,
                "whole_p36_closed": False, "currentVerified": False,
                "remote_write_performed": False}
    require(isinstance(manifest, dict), "Expected a manifest object")
    for key, value in expected.items():
        require(manifest.get(key) == value and type(manifest.get(key)) is type(value),
                f"Manifest field mismatch: {key}")
    files = manifest.get("files")
    require(isinstance(files, dict) and REQUIRED_FILES <= set(files)
            and set(files) <= REQUIRED_FILES | {"publication.rev"}, "Unexpected manifest file set")
    for name, pin in files.items():
        require(isinstance(pin, dict) and set(pin) == {"sha256", "size_bytes"}
                and digest(pin["sha256"], 64) and type(pin["size_bytes"]) is int
                and pin["size_bytes"] > 0 and file_pin(directory / name) == pin,
                f"Transported file differs from its manifest: {name}")
    require(manifest.get("pack_sha256") == files["publication.pack"]["sha256"]
            and manifest.get("pack_bytes") == files["publication.pack"]["size_bytes"],
            "Pack summary differs from its file pin")
    for key in ("all_new_object_count", "packed_object_count", "changed_path_count"):
        require(type(manifest.get(key)) is int and manifest[key] > 0, f"Invalid count: {key}")
    require(type(manifest.get("excluded_evidence_blob_count")) is int
            and manifest["excluded_evidence_blob_count"] == 5, "Expected five excluded evidence blobs")
    require(gout(transport, bare, "rev-parse", "--is-bare-repository").strip() == b"true"
            and gout(transport, bare, "rev-parse", "--is-shallow-repository").strip() == b"false",
            "The retained receiver must be a complete, non-shallow bare repository")
    require(gout(transport, bare, "rev-list", "--parents", "-n", "1", ARTIFACT).decode().split()
            == [ARTIFACT, ARTIFACT_PARENT], "Artifact checkpoint or parent mismatch")
    excluded = json.loads((directory / "EXCLUDED_EVIDENCE_BLOBS.json").read_bytes())
    require(isinstance(excluded, list) and len(excluded) == 5
            and all(isinstance(row, dict) for row in excluded)
            and {row.get("name") for row in excluded} == EVIDENCE_FILES,
            "Expected the exact five excluded evidence names")
    for row in excluded:
        require(set(row) == {"name", "target_path", "artifact_path", "git_blob_sha", "size_bytes", "sha256"}
                and row["target_path"] == f"{INCREMENT}/accepted-group/{row['name']}"
                and row["artifact_path"] == f"admission-w-layer/{row['name']}"
                and digest(row["git_blob_sha"], 40) and digest(row["sha256"], 64)
                and type(row["size_bytes"]) is int and row["size_bytes"] > 0,
                "Invalid excluded evidence entry")
        expected_entry = {"mode": "100644", "kind": "blob",
                          **{key: row[key] for key in ("git_blob_sha", "size_bytes", "sha256")}}
        require(entry(transport, bare, ARTIFACT, row["artifact_path"]) == expected_entry,
                f"Retained artifact bytes mismatch: {row['name']}")
    all_ids, packed_ids = object_ids(directory / "ALL_OBJECTS.txt"), object_ids(directory / "PACKED_OBJECTS.txt")
    excluded_ids = {row["git_blob_sha"] for row in excluded}
    require(len(excluded_ids) == 5 and packed_ids.isdisjoint(excluded_ids)
            and all_ids == packed_ids | excluded_ids
            and len(all_ids) == manifest["all_new_object_count"]
            and len(packed_ids) == manifest["packed_object_count"]
            and sorted(excluded_ids) == manifest.get("excluded_evidence_blob_shas")
            and args.commit in packed_ids, "Exact object selection or five-blob exclusion mismatch")
    pack = directory / "publication.pack"
    with pack.open("rb") as stream:
        header = stream.read(12)
        stream.seek(-20, os.SEEK_END)
        trailer = stream.read(20).hex()
    require(header[:4] == b"PACK" and int.from_bytes(header[8:12], "big") == len(packed_ids)
            and trailer == manifest.get("pack_git_trailer_sha1"), "Pack header or trailer mismatch")
    with pack.open("rb") as stream:
        imported, _ = git(transport, bare, "index-pack", "--strict", "--stdin", stdin=stream)
    require(imported.decode().strip().split()[-1] == trailer, "Imported pack object digest mismatch")
    idx = bare / "objects" / "pack" / f"pack-{trailer}.idx"
    pack_listing = gout(transport, bare, "verify-pack", "-v", str(idx)).decode()
    rows = [line.split() for line in pack_listing.splitlines() if re.match(r"^[0-9a-f]{40} ", line)]
    require(len(rows) == len(packed_ids) and {row[0] for row in rows} == packed_ids
            and all(len(row) == 5 for row in rows), "Received pack must contain exactly the full selected objects")
    for revision in (BASE, args.commit, args.expected_remote):
        require(gout(transport, bare, "cat-file", "-t", revision).strip() == b"commit", "Expected exact commit objects")
    gout(transport, bare, "merge-base", "--is-ancestor", BASE, args.expected_remote)
    gout(transport, bare, "merge-base", "--is-ancestor", args.expected_remote, args.commit)
    actual_ids = gout(transport, bare, "rev-list", "--objects", "--no-object-names",
                       args.commit, f"^{BASE}").decode().splitlines()
    require(len(actual_ids) == len(all_ids) and set(actual_ids) == all_ids,
            "Receiver revision walk differs from the exact full object inventory")
    for row in excluded:
        expected_entry = {"mode": "100644", "kind": "blob",
                          **{key: row[key] for key in ("git_blob_sha", "size_bytes", "sha256")}}
        require(entry(transport, bare, args.commit, row["target_path"]) == expected_entry,
                f"Target evidence bytes mismatch: {row['name']}")
    closure = gout(transport, bare, "rev-list", "--objects", "--no-object-names",
                   "--missing=print", args.commit).decode().splitlines()
    require(closure and all(digest(oid, 40) for oid in closure),
            "Full target closure has missing or invalid objects; no shallow boundary is permitted")
    fsck_out, fsck_err = git(transport, bare, "fsck", "--full", "--no-reflogs", "--no-dangling", args.commit)
    changes = json.loads((directory / "CHANGED_FILES.json").read_bytes())
    delta = gout(transport, bare, "diff-tree", "--no-commit-id", "--name-status", "--no-renames",
                 "-r", "-z", BASE, args.commit).decode().split("\0")[:-1]
    require(len(delta) % 2 == 0 and isinstance(changes, list)
            and len(changes) == len(delta) // 2 == manifest["changed_path_count"],
            "Changed-path count differs from the receiver tree diff")
    actual_changes = []
    for status, path in zip(delta[::2], delta[1::2]):
        require(status in {"A", "M", "D", "T"}, "Unexpected changed-path status")
        actual_changes.append({"path": path, "status": status,
                               "base": entry(transport, bare, BASE, path),
                               "target": entry(transport, bare, args.commit, path)})
    require(changes == actual_changes, "Changed-file modes, blobs, sizes or SHA-256 values differ")
    checks = {"status": "COMPLETE_RECEIVER_VERIFICATION_PASSED", "base_commit": BASE,
              "target_commit": args.commit, "expected_remote": args.expected_remote,
              "artifact_commit": ARTIFACT, "manifest_sha256": args.manifest_sha256,
              "receiver_sha256": file_pin(Path(__file__))["sha256"],
              "transport_sha256": TRANSPORT_SHA256, "bare_repository": str(bare),
              "is_shallow": False, "index_pack_exit_code": 0, "full_missing_object_count": 0,
              "full_closure_object_count": len(closure), "full_fsck_exit_code": 0,
              "fsck_stdout_sha256": hashlib.sha256(fsck_out).hexdigest(),
              "fsck_stderr_sha256": hashlib.sha256(fsck_err).hexdigest(),
              "pack_sha256": manifest["pack_sha256"], "packed_object_count": len(packed_ids),
              "excluded_evidence_blob_count": 5, "changed_path_count": len(changes),
              "whole_p36_closed": False, "currentVerified": False, "remote_write_performed": False}
    checks_path = save(directory, "RECEIVER_CHECKS.json", checks)
    return checks, checks_path


def readback(args, transport):
    with transport.locked_destination(args.authorized) as destination:
        refs = transport.read_refs(destination)
    return {"status": "READBACK_ONLY", "target_commit": args.commit,
            "manifest_sha256": args.manifest_sha256, "remote_refs": refs,
            "work_matches_target": refs[WORK_REF] == args.commit,
            "work_matches_expected_prior": refs[WORK_REF] == args.expected_remote,
            "artifact_matches_pin": refs[ARTIFACT_REF] == ARTIFACT,
            "remote_write_performed": False}


def publish(args, transport, checks, checks_path):
    attempted = False
    before = None
    try:
        with transport.locked_destination(args.authorized) as destination:
            before = transport.read_refs(destination)
            require(before[ARTIFACT_REF] == ARTIFACT, "Remote artifact ref differs from the fixed published checkpoint")
            require(before[WORK_REF] in {args.expected_remote, args.commit},
                    "Remote work ref differs from the independently expected ancestor and target")
            if before[WORK_REF] != args.commit:
                attempted = True
                git(transport, destination, "push", "--porcelain", "--no-follow-tags", "--recurse-submodules=no",
                    transport.LOCKED_REMOTE, f"{args.commit}:{WORK_REF}",
                    extra_env={"GIT_ALTERNATE_OBJECT_DIRECTORIES": str(args.bare / "objects")})
                after = transport.read_refs(destination)
            else:
                after = before
            require(after == {WORK_REF: args.commit, ARTIFACT_REF: ARTIFACT},
                    "Remote refs differ on the post-push readback")
        publication = {"status": "WORK_REF_VERIFIED", "target_commit": args.commit,
                       "expected_remote": args.expected_remote, "base_commit": BASE,
                       "artifact_commit": ARTIFACT, "work_ref": WORK_REF,
                       "manifest_sha256": args.manifest_sha256, "receiver_checks_file": str(checks_path),
                       "receiver_checks_sha256": file_pin(checks_path)["sha256"],
                       "remote_refs_before": before, "remote_refs_after": after,
                       "update_method": "ordinary_fast_forward", "force_used": False,
                       "push_attempted": attempted, "already_at_target": not attempted,
                       "whole_p36_closed": False, "currentVerified": False}
        publication_path = save(args.input_dir, "PUBLICATION.json", publication)
        return {**publication, "publication_file": str(publication_path),
                "publication_sha256": file_pin(publication_path)["sha256"]}
    except (OSError, RuntimeError, ValueError) as exc:
        if attempted or before is not None and before.get(WORK_REF) == args.commit:
            failure = {"status": "PUBLICATION_OUTCOME_UNCONFIRMED", "target_commit": args.commit,
                       "manifest_sha256": args.manifest_sha256, "push_attempted": attempted,
                       "remote_refs_before": before, "receiver_checks_file": str(checks_path),
                       "message": "The work ref may already have changed. Run the readback action before retrying."}
            try:
                save(args.input_dir, "PUBLICATION_UNCONFIRMED.json", failure)
            except (OSError, RuntimeError, ValueError):
                pass
            raise RuntimeError(f"{exc}. The work ref may already have changed; run readback for {args.commit}.") from None
        raise


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("verify", "publish", "readback"))
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--expected-remote", default=BASE)
    parser.add_argument("--bare", type=Path, default=Path("/workspace/p36-authorized-publication-20261126/repository.git"))
    parser.add_argument("--authorized", type=Path, default=Path("/workspace/p36-original-u5-20261125"))
    args = parser.parse_args(argv)
    require(digest(args.commit, 40) and digest(args.expected_remote, 40)
            and digest(args.manifest_sha256, 64), "Exact commit and manifest digest pins are mandatory")
    args.input_dir, args.bare, args.authorized = args.input_dir.resolve(), args.bare.resolve(), args.authorized.resolve()
    transport = load_transport()
    if args.action == "readback":
        result = readback(args, transport)
    else:
        checks, path = verify(args, transport)
        result = ({**checks, "receiver_checks_file": str(path)} if args.action == "verify"
                  else publish(args, transport, checks, path))
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, KeyError, IndexError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
