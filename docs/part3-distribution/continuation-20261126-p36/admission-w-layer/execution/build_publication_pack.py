#!/usr/bin/env python3
"""Build an exact, non-thin publication pack without network or ref writes.

The receiver must already contain the complete pinned base and the five blobs
from the independently published artifact commit. This command verifies both
trees and the recorded bytes before omitting those blobs from the exact
``target ^base`` object set. It never treats an unrelated artifact commit as a
revision exclusion. A successful build proves the pack's contents, not remote
connectivity or publication. Those checks must run again at the receiver.

The output directory must be new. Failed output remains available for diagnosis.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


BASE = "b3f306cc3b430fc40c3b3ec4110d323443d2f609"
ARTIFACT = "59cf6341935bc0b8b780526e2d9d2f12d5f1a893"
ARTIFACT_PARENT = "f86223d06127fb6a0f3394ce4f6479e1e27fcfde"
ARTIFACT_REF = "refs/heads/artifacts/p36-normalized-density-20261126"
PROJECT = Path("/workspace/library-files/p36-warm-payment-20261126")
ARTIFACT_REPO = Path("/workspace/scratch/aef9b33cc628/p36-admission-artifact.git")
INCREMENT = Path("docs/part3-distribution/continuation-20261126-p36/admission-w-layer")
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


def is_digest(value, length):
    return isinstance(value, str) and re.fullmatch(rf"[0-9a-f]{{{length}}}", value) is not None


def git_env():
    env = dict(os.environ)
    for key in tuple(env):
        if key.startswith("GIT_CONFIG") or key.startswith("GIT_TRACE") or key in {
            "GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
            "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
            "GIT_NAMESPACE", "GIT_CURL_VERBOSE", "GIT_SHALLOW_FILE",
        }:
            env.pop(key, None)
    env.update(
        GIT_TERMINAL_PROMPT="0", GIT_NO_LAZY_FETCH="1", GIT_NO_REPLACE_OBJECTS="1",
        GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", GIT_GRAFT_FILE=os.devnull,
    )
    return env


def git(repo, *args, input_bytes=None, stdout=subprocess.PIPE):
    result = subprocess.run(
        ["git", "--no-replace-objects", "-C", str(repo), *args],
        input=input_bytes, stdout=stdout, stderr=subprocess.PIPE, env=git_env(),
    )
    if result.returncode:
        # This helper never needs credential or remote diagnostics.
        raise RuntimeError(f"Git {args[0]} failed with exit {result.returncode}")
    return result.stdout


def exact_commit(repo, commit):
    require(is_digest(commit, 40), "Provide an exact lowercase 40-digit commit SHA")
    require(git(repo, "cat-file", "-t", commit).strip() == b"commit",
            "The pinned object must be a commit")


def tree_entry(repo, commit, path):
    raw = git(repo, "ls-tree", "-z", commit, "--", path)
    records = raw.split(b"\0")[:-1]
    require(len(records) == 1, f"Expected exactly one committed path: {path}")
    info, actual = records[0].decode().split("\t", 1)
    mode, kind, oid = info.split()
    require(actual == path and is_digest(oid, 40), f"Invalid committed entry: {path}")
    return {"mode": mode, "kind": kind, "git_blob_sha": oid}


def blob_record(repo, oid):
    require(is_digest(oid, 40), "Expected an exact blob object ID")
    require(git(repo, "cat-file", "-t", oid).strip() == b"blob", "Expected a Git blob")
    digest = hashlib.sha256()
    size = 0
    command = ["git", "--no-replace-objects", "-C", str(repo), "cat-file", "blob", oid]
    with subprocess.Popen(
        command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, env=git_env(),
    ) as child:
        while block := child.stdout.read(1024 * 1024):
            digest.update(block)
            size += len(block)
    require(child.returncode == 0, "Cannot read the exact committed Git blob")
    return {"git_blob_sha": oid, "size_bytes": size, "sha256": digest.hexdigest()}


def artifact_records(project, artifact_repo, target, publication_file):
    require(publication_file.is_file() and not publication_file.is_symlink(),
            "Expected the retained artifact publication record")
    publication_bytes = publication_file.read_bytes()
    publication = json.loads(publication_bytes)
    require(publication.get("status") == "ARTIFACT_REF_VERIFIED"
            and publication.get("artifact_commit") == ARTIFACT
            and publication.get("artifact_parent") == ARTIFACT_PARENT
            and publication.get("artifact_ref") == ARTIFACT_REF,
            "Artifact publication record differs from the fixed checkpoint")
    pins = publication.get("files")
    require(isinstance(pins, dict) and set(pins) == set(FILES),
            "Expected pins for exactly the five published files")
    exact_commit(artifact_repo, ARTIFACT)
    require(git(artifact_repo, "rev-parse", "--is-bare-repository").strip() == b"true",
            "Artifact verification requires its isolated bare repository")
    parents = git(artifact_repo, "rev-list", "--parents", "-n", "1", ARTIFACT).decode().split()
    require(parents == [ARTIFACT, ARTIFACT_PARENT], "Artifact parent differs from its pin")
    records = []
    for name in FILES:
        pin = pins[name]
        require(isinstance(pin, dict)
                and set(pin) == {"sha256", "size_bytes", "git_blob_sha"}
                and is_digest(pin["sha256"], 64) and is_digest(pin["git_blob_sha"], 40)
                and type(pin["size_bytes"]) is int and pin["size_bytes"] > 0,
                f"Invalid independent artifact pin: {name}")
        artifact_path = f"admission-w-layer/{name}"
        target_path = (INCREMENT / "accepted-group" / name).as_posix()
        stored = tree_entry(artifact_repo, ARTIFACT, artifact_path)
        intended = tree_entry(project, target, target_path)
        require(stored["mode"] == intended["mode"] == "100644"
                and stored["kind"] == intended["kind"] == "blob"
                and stored["git_blob_sha"] == intended["git_blob_sha"] == pin["git_blob_sha"],
                f"Evidence tree/blob mismatch: {name}")
        require(blob_record(artifact_repo, pin["git_blob_sha"]) == pin,
                f"Published evidence bytes differ from the independent pin: {name}")
        require(blob_record(project, pin["git_blob_sha"]) == pin,
                f"Target evidence bytes differ from the independent pin: {name}")
        records.append({"name": name, "target_path": target_path,
                        "artifact_path": artifact_path, **pin})
    require(len({row["git_blob_sha"] for row in records}) == len(FILES),
            "Expected five distinct published evidence blobs")
    return records, hashlib.sha256(publication_bytes).hexdigest()


def changed_files(project, target):
    raw = git(project, "diff-tree", "--no-commit-id", "--name-status", "--no-renames",
              "-r", "-z", BASE, target)
    entries = raw.decode().split("\0")[:-1]
    require(len(entries) % 2 == 0, "Unexpected changed-path format")
    records = []
    for status, path in zip(entries[::2], entries[1::2]):
        require(status in {"A", "M", "D", "T"}, "Unexpected changed-path status")
        record = {"path": path, "status": status}
        for label, commit, absent in (("base", BASE, status == "A"),
                                       ("target", target, status == "D")):
            if absent:
                record[label] = None
                continue
            entry = tree_entry(project, commit, path)
            require(entry["kind"] == "blob" and entry["mode"] in {"100644", "100755", "120000"},
                    f"Unsupported non-blob changed path: {path}")
            record[label] = {**entry, **blob_record(project, entry["git_blob_sha"])}
        records.append(record)
    return records


def write_json(path, value):
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def build(project, artifact_repo, target, output, publication_file):
    exact_commit(project, BASE)
    exact_commit(project, target)
    require(target != BASE, "The target must be a new descendant of the pinned base")
    git(project, "merge-base", "--is-ancestor", BASE, target)
    require(not output.exists(), "Output directory must be new; prior attempts are retained")
    excluded, publication_sha = artifact_records(project, artifact_repo, target, publication_file)
    excluded_ids = {row["git_blob_sha"] for row in excluded}
    object_lines = git(project, "rev-list", "--objects", "--no-object-names",
                       target, f"^{BASE}").decode().splitlines()
    require(all(is_digest(oid, 40) for oid in object_lines), "Unexpected revision object ID")
    all_ids = set(object_lines)
    require(len(all_ids) == len(object_lines), "Duplicate entries in the revision object inventory")
    require(excluded_ids <= all_ids,
            "Each of the five published blobs must occur in the exact target-minus-base object set")
    packed_ids = all_ids - excluded_ids
    require(target in packed_ids and len(all_ids) - len(packed_ids) == 5,
            "The exact target commit and exact five-blob exclusion are required")
    changes = changed_files(project, target)

    output.mkdir(parents=True)
    all_file = output / "ALL_OBJECTS.txt"
    packed_file = output / "PACKED_OBJECTS.txt"
    all_file.write_text("".join(f"{oid}\n" for oid in sorted(all_ids)))
    packed_bytes = "".join(f"{oid}\n" for oid in sorted(packed_ids)).encode()
    packed_file.write_bytes(packed_bytes)
    write_json(output / "EXCLUDED_EVIDENCE_BLOBS.json", excluded)
    write_json(output / "CHANGED_FILES.json", changes)
    pack = output / "publication.pack"
    index = output / "publication.idx"
    with pack.open("xb") as stream:
        git(project, "pack-objects", "--stdout", "--compression=9", "--threads=1",
            "--window=0", "--no-reuse-delta", "--no-reuse-object",
            input_bytes=packed_bytes, stdout=stream)
    git(project, "index-pack", "--strict", "-o", str(index), str(pack))
    verification = git(project, "verify-pack", "-v", str(index)).decode()
    actual = {line.split()[0] for line in verification.splitlines()
              if re.match(r"^[0-9a-f]{40} ", line)}
    require(actual == packed_ids and not actual & excluded_ids,
            "Pack contents differ from the explicit selected object set")
    require(all(len(line.split()) == 5 for line in verification.splitlines()
                if re.match(r"^[0-9a-f]{40} ", line)),
            "This publication pack must contain full objects without delta bases")
    (output / "VERIFY_PACK.txt").write_text(verification)
    with pack.open("rb") as stream:
        pack_sha256 = hashlib.file_digest(stream, "sha256").hexdigest()
    with pack.open("rb") as stream:
        header = stream.read(12)
        stream.seek(-20, os.SEEK_END)
        trailer = stream.read(20).hex()
    require(header[:4] == b"PACK" and int.from_bytes(header[8:12], "big") == len(packed_ids),
            "Pack header object count differs from the exact inventory")
    files = {}
    for path in sorted(output.iterdir()):
        if path.is_file():
            with path.open("rb") as stream:
                digest = hashlib.file_digest(stream, "sha256").hexdigest()
            files[path.name] = {"sha256": digest, "size_bytes": path.stat().st_size}
    record = {
        "status": "EXACT_NON_THIN_PUBLICATION_PACK_VERIFIED_LOCALLY",
        "base_commit": BASE,
        "target_commit": target,
        "artifact_commit": ARTIFACT,
        "artifact_parent": ARTIFACT_PARENT,
        "artifact_publication_record_sha256": publication_sha,
        "builder_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "all_new_object_count": len(all_ids),
        "packed_object_count": len(packed_ids),
        "excluded_evidence_blob_count": len(excluded_ids),
        "excluded_evidence_blob_shas": sorted(excluded_ids),
        "changed_path_count": len(changes),
        "pack_sha256": pack_sha256,
        "pack_bytes": pack.stat().st_size,
        "pack_git_trailer_sha1": trailer,
        "files": files,
        "whole_p36_closed": False,
        "currentVerified": False,
        "remote_write_performed": False,
        "receiver_requirement": "Complete pinned base and five exact artifact blobs already present; index-pack, missing-object/connectivity checks and changed-file hash verification remain mandatory before publication.",
    }
    write_json(output / "PACK_MANIFEST.json", record)
    return {"status": record["status"], "target_commit": target,
            "output_dir": str(output), "manifest": str(output / "PACK_MANIFEST.json"),
            "all_new_object_count": len(all_ids), "packed_object_count": len(packed_ids),
            "pack_bytes": record["pack_bytes"], "pack_sha256": pack_sha256,
            "remote_write_performed": False}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", required=True, help="exact final reviewed commit SHA")
    parser.add_argument("--output-dir", type=Path, required=True, help="new directory for immutable outputs")
    parser.add_argument("--project", type=Path, default=PROJECT)
    parser.add_argument("--artifact-repo", type=Path, default=ARTIFACT_REPO)
    parser.add_argument("--artifact-publication", type=Path,
                        default=Path(__file__).with_name("ARTIFACT_PUBLICATION.json"))
    args = parser.parse_args(argv)
    result = build(args.project.resolve(), args.artifact_repo.resolve(), args.commit,
                   args.output_dir.absolute(), args.artifact_publication.resolve())
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
