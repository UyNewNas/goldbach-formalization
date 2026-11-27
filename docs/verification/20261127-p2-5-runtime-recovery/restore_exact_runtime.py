#!/usr/bin/env python3
"""Restore only missing, SHA-bound files named in an existing runtime snapshot.

This is byte recovery, not qualification, compilation, or proof acceptance.
Previously exact inventory rows are not rehashed. Existing mismatches, symlinks,
old snapshots, and receipts are never overwritten or synthesized. A fresh output
directory records every targeted result. Without --apply, no target is written.

Inputs: pinned snapshot and inventory; optional original CI part-000 metadata
and payload packets (plain inner ZIPs or single-member GitHub wrapper ZIPs);
optional explicitly named donor files/directories. Directory searches hash only
regular files whose sizes match still-uncovered requested content. No network,
compiler, kernel, subprocess, or repository mutation is performed.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from contextlib import ExitStack, contextmanager
from datetime import datetime, timezone
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import stat
import sys
import uuid
import zipfile


SNAPSHOT_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
CHECKPOINT_SHA = "aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a"
CHECKPOINT_BYTES = 67075207
ARTIFACT_SHA = "c506ac0c034e971c5554802a4e551762f122a42d25701b07a5a6c4c6471d4b7b"
CREDIT = dict(compile_credit=False, kernel_credit=False, cache_acceptance=False,
              qualification_performed=False, runtime_restored=False, P2_5_proved=False)
FLAGS = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
DIR_FLAGS = FLAGS | os.O_DIRECTORY


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(body):
    return hashlib.sha256(body).hexdigest()


def stamp(info):
    return info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns


def content_key(row):
    size, digest = row["bytes"], row["sha256"]
    require(type(size) is int and size >= 0 and isinstance(digest, str)
            and re.fullmatch("[0-9a-f]{64}", digest), "invalid content identity")
    return size, digest


def workspace_path(value):
    path = Path(value)
    require(path.is_absolute() and ".." not in path.parts and str(path) == str(value)
            and path.is_relative_to("/workspace") and path != Path("/workspace"),
            "path is not a normalized /workspace descendant: " + str(value))
    return path


def read_regular(path, expected=None):
    with os.fdopen(os.open(path, FLAGS), "rb") as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode), "source is not a regular file: " + str(path))
        if expected:
            require(before.st_size == expected[0], "source size mismatch: " + str(path))
        body = stream.read()
        require(stamp(os.fstat(stream.fileno())) == stamp(before),
                "source changed while reading: " + str(path))
    if expected:
        require((len(body), sha(body)) == expected, "source digest mismatch: " + str(path))
    return body


def pinned_json(path, digest):
    body = read_regular(path)
    if path.suffix == ".xz":
        body = lzma.decompress(body)
    require(sha(body) == digest, "input digest mismatch: " + str(path))
    return json.loads(body), len(body)


def checked_zip(stream, stack):
    archive = stack.enter_context(zipfile.ZipFile(stream))
    names = archive.namelist()
    require(len(names) == len(set(names)), "duplicate ZIP members")
    for info in archive.infolist():
        require(not info.flag_bits & 1 and not stat.S_ISLNK(info.external_attr >> 16),
                "encrypted or symlink ZIP member")
    return archive


def open_part(path, stack):
    """Keep nested wrappers open; do not expand packets onto the filesystem."""
    stream = stack.enter_context(os.fdopen(os.open(path, FLAGS), "rb"))
    require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), "packet is not a regular file")
    outer = checked_zip(stream, stack)
    markers = {"EXPORT_MANIFEST.json", "PACKET_INDEX.json"}
    if markers.intersection(outer.namelist()):
        stream.seek(0)
        return path.name, stream, outer
    members = [i for i in outer.infolist() if not i.is_dir()]
    require(len(members) == 1 and re.fullmatch(r"part-[0-9]{3}\.zip", members[0].filename),
            "expected a single original part-NNN.zip wrapper member")
    inner_stream = stack.enter_context(outer.open(members[0]))
    inner = checked_zip(inner_stream, stack)
    inner_stream.seek(0)
    return members[0].filename, inner_stream, inner


def stream_sha(stream):
    stream.seek(0)
    digest, count = hashlib.sha256(), 0
    for block in iter(lambda: stream.read(1048576), b""):
        digest.update(block)
        count += len(block)
    stream.seek(0)
    return count, digest.hexdigest()


def metadata_bodies(archive, path):
    names = ("CHECKPOINT.json", "REQUEST.json", "EXPORT_MANIFEST.json",
             "ORIGINAL_ARTIFACT_METADATA.json")
    bodies, sources = {}, defaultdict(list)
    for name in names:
        body = archive.read(name)
        bodies[name] = body
        sources[(len(body), sha(body))].append(("packet", archive, str(path), name))
    return bodies, sources


def read_metadata(path, expected_sha, stack):
    with os.fdopen(os.open(path, FLAGS), "rb") as stream:
        require(stream_sha(stream)[1] == expected_sha, "metadata packet digest mismatch")
    name, _, archive = open_part(path, stack)
    require(name == "part-000.zip", "expected original metadata part-000.zip")
    bodies, sources = metadata_bodies(archive, path)
    raw = bodies["CHECKPOINT.json"]
    require((len(raw), sha(raw)) == (CHECKPOINT_BYTES, CHECKPOINT_SHA),
            "original checkpoint identity differs")
    manifest = json.loads(bodies["EXPORT_MANIFEST.json"])
    request = bodies["REQUEST.json"]
    original = json.loads(bodies["ORIGINAL_ARTIFACT_METADATA.json"])
    require(manifest["schema"] == "p2-original-native-byte-export-v1"
            and manifest["original_artifact"]["id"] == 13749339878
            and manifest["original_artifact"]["sha256"] == ARTIFACT_SHA
            and manifest["original_artifact"]["checkpoint_sha256"] == CHECKPOINT_SHA
            and manifest["whole_original_archive_sha256_verified"] is True
            and manifest["original_checkpoint_sha256_verified"] is True
            and manifest["original_bytes_or_classifications_modified"] is False
            and all(manifest.get(k) is False for k in ("compile_credit", "kernel_credit", "cache_acceptance"))
            and manifest["request_sha256"] == sha(request)
            and original["id"] == 13749339878
            and original["digest"] == "sha256:" + ARTIFACT_SHA,
            "original byte-export metadata binding differs")
    return manifest, sources


def read_packets(manifest, paths, stack):
    rows = {row["file"]: row for row in manifest["payload_packets"]}
    require(len(rows) == len(manifest["payload_packets"]), "duplicate packet manifest rows")
    sources, seen = defaultdict(list), set()
    for path in paths:
        name, stream, archive = open_part(path, stack)
        require(name in rows and name not in seen, "unknown or duplicate payload packet: " + name)
        seen.add(name)
        require(stream_sha(stream) == content_key(rows[name]), "packet digest mismatch: " + name)
        index = json.loads(archive.read("PACKET_INDEX.json"))
        require(index["schema"] == "p2-original-native-byte-packet-v1"
                and name == f"part-{index['part']:03d}.zip"
                and index["original_artifact"] == manifest["original_artifact"]
                and index["request_sha256"] == manifest["request_sha256"]
                and len(index["payloads"]) == rows[name]["payload_count"],
                "payload packet index binding differs")
        require(set(archive.namelist()) == {"PACKET_INDEX.json", *index["payloads"]},
                "packet members differ from original payload index")
        for member, row in index["payloads"].items():
            key = content_key(row)
            info = archive.getinfo(member)
            require(member == "objects/" + key[1] and info.file_size == key[0]
                    and info.compress_type == zipfile.ZIP_STORED, "invalid content-addressed payload")
            sources[key].append(("packet", archive, str(path), member))
    return sources


def source_label(source):
    return (dict(kind="file", path=str(source[1])) if source[0] == "file"
            else dict(kind="packet", path=source[2], member=source[3]))


def source_bytes(source, expected):
    body = (read_regular(source[1], expected) if source[0] == "file"
            else source[1].read(source[3]))
    require((len(body), sha(body)) == expected, "payload digest mismatch")
    return body


def path_problem(path):
    for parent in reversed(path.parents):
        try:
            info = parent.lstat()
        except FileNotFoundError:
            continue
        if not stat.S_ISDIR(info.st_mode):
            return "ancestor is not a real directory: " + str(parent)
    return None


@contextmanager
def parent_fd(path):
    """Traverse/create real directories using descriptors, never symlink paths."""
    current = os.open("/", DIR_FLAGS)
    try:
        for part in path.parent.parts[1:]:
            try:
                child = os.open(part, DIR_FLAGS, dir_fd=current)
            except FileNotFoundError:
                try:
                    os.mkdir(part, 0o755, dir_fd=current)
                except FileExistsError:
                    pass
                child = os.open(part, DIR_FLAGS, dir_fd=current)
            os.close(current)
            current = child
        yield current
    finally:
        os.close(current)


def install(path, body):
    """Publish a verified private temporary inode with atomic no-overwrite link."""
    with parent_fd(path) as directory:
        temporary = ".p25-restore-" + uuid.uuid4().hex
        descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                             0o644, dir_fd=directory)
        try:
            with os.fdopen(descriptor, "wb") as stream:
                stream.write(body)
                stream.flush()
                os.fsync(stream.fileno())
            os.link(temporary, path.name, src_dir_fd=directory, dst_dir_fd=directory,
                    follow_symlinks=False)
            os.fsync(directory)
        finally:
            os.unlink(temporary, dir_fd=directory)


def extra_sources(files, directories, wanted, sources, errors):
    # A historically listed donor may have disappeared. Only an authenticated
    # packet can avoid the directory fallback; unverified file donors cannot.
    sizes = {size for size, digest in wanted
             if not any(source[0] == "packet" for source in sources.get((size, digest), []))}
    counts = dict(regular_candidates_hashed=0, candidate_bytes_hashed=0)
    def inspect(path):
        try:
            info = path.lstat()
            if stat.S_ISREG(info.st_mode) and info.st_size in sizes:
                body = read_regular(path)
                counts["regular_candidates_hashed"] += 1
                counts["candidate_bytes_hashed"] += len(body)
                key = len(body), sha(body)
                if key in wanted:
                    sources[key].append(("file", path))
        except (OSError, ValueError) as error:
            errors.append(dict(path=str(path), error=str(error)))
    for path in files:
        inspect(path)
    for directory in directories:
        require(directory.is_dir() and not directory.is_symlink(), "invalid explicit donor directory")
        for root, dirs, names in os.walk(directory, followlinks=False):
            dirs[:] = sorted(d for d in dirs if d != ".git" and not (Path(root) / d).is_symlink())
            for name in sorted(names):
                inspect(Path(root) / name)
    return counts


def restore(args):
    snapshot, snapshot_bytes = pinned_json(args.snapshot, args.snapshot_sha256)
    inventory, inventory_bytes = pinned_json(args.inventory, args.inventory_sha256)
    require(snapshot.get("schema") == "p2-winner9-qualified-native-environment-v1"
            and snapshot.get("compile_credit") is False and snapshot.get("kernel_credit") is False,
            "unexpected snapshot schema or proof credit")
    require(inventory.get("schema") == "p2-runtime-readonly-inventory-v1"
            and inventory["snapshot"]["raw_sha256"] == args.snapshot_sha256,
            "inventory is not bound to the supplied snapshot")
    require(set(inventory["files"]) == set(snapshot["files"]), "inventory/snapshot paths differ")
    for path, expected in snapshot["files"].items():
        workspace_path(path)
        require(content_key(inventory["files"][path]["expected"]) == content_key(expected),
                "inventory/snapshot expected bytes differ: " + path)
    output = workspace_path(str(args.out_dir))
    require(not output.exists() and not output.is_symlink() and not path_problem(output),
            "output directory must be fresh with real directory ancestors")
    require(all(not Path(p).is_relative_to(output) for p in snapshot["files"]),
            "report directory overlaps snapshot targets")
    targets = {p: row for p, row in inventory["files"].items() if row["status"] != "exact"}
    report = dict(schema="p25-exact-runtime-restore-v1", started_utc=datetime.now(timezone.utc).isoformat(),
                  apply=args.apply, snapshot=dict(path=str(args.snapshot), bytes=snapshot_bytes,
                  sha256=args.snapshot_sha256), inventory=dict(path=str(args.inventory),
                  bytes=inventory_bytes, sha256=args.inventory_sha256), **CREDIT,
                  previously_exact_not_rechecked=len(snapshot["files"]) - len(targets),
                  files={}, source_errors=[], byte_restoration_performed=False)
    wanted = {content_key(row["expected"]) for row in targets.values()}
    with ExitStack() as stack:
        sources = defaultdict(list)
        if args.metadata_packet:
            require(args.metadata_sha256 is not None, "--metadata-sha256 is required")
            manifest, metadata_sources = read_metadata(args.metadata_packet, args.metadata_sha256, stack)
            for candidates in (metadata_sources, read_packets(manifest, args.packet, stack)):
                for key, values in candidates.items():
                    sources[key].extend(values)
            report["metadata_packet"] = dict(path=str(args.metadata_packet), sha256=args.metadata_sha256,
                                             checkpoint_sha256=CHECKPOINT_SHA,
                                             request_sha256=manifest["request_sha256"])
        else:
            require(not args.packet, "payload packets require pinned metadata")
        for size, digest in wanted:
            row = inventory.get("donors", {}).get(f"{size}:{digest}", {})
            for candidate in row.get("candidates", []):
                path = Path(candidate.get("resolved_path", candidate["path"]))
                sources[(size, digest)].append(("file", path))
        report["explicit_donor_scan"] = extra_sources(
            args.donor_file, args.donor_dir, wanted, sources, report["source_errors"])
        # The report directory is reserved only after all immutable inputs validate.
        with parent_fd(output) as directory:
            os.mkdir(output.name, 0o755, dir_fd=directory)
        for name, row in sorted(targets.items()):
            path, key = Path(name), content_key(row["expected"])
            item = dict(expected=snapshot["files"][name], inventory_status=row["status"])
            report["files"][name] = item
            try:
                problem = path_problem(path)
                if problem:
                    item.update(status="blocked_path", error=problem)
                    continue
                if path.exists() or path.is_symlink():
                    try:
                        read_regular(path, key)
                        item["status"] = "exact_now"
                    except (OSError, ValueError):
                        item["status"] = "existing_conflict"
                    continue
                body, selected = None, None
                for candidate in sources.get(key, []):
                    try:
                        body = source_bytes(candidate, key)
                        selected = candidate
                        break
                    except (OSError, ValueError, zipfile.BadZipFile) as error:
                        report["source_errors"].append(dict(source=source_label(candidate), error=str(error)))
                if selected is None:
                    item["status"] = "missing"
                    continue
                item.update(status="ready", source=source_label(selected))
                if args.apply:
                    install(path, body)
                    report["byte_restoration_performed"] = True
                    read_regular(path, key)
                    item["status"] = "restored"
            except FileExistsError:
                item.update(status="existing_conflict", error="destination appeared; no overwrite attempted")
            except (OSError, ValueError) as error:
                item.update(status="blocked_path", error=str(error))
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    report["summary"] = dict(Counter(row["status"] for row in report["files"].values()))
    report["missing_by_role"] = dict(Counter(row["expected"].get("role", "unspecified")
                                            for row in report["files"].values()
                                            if row["status"] == "missing"))
    report["limitations"] = [
        "Only previously nonexact inventory rows were inspected; prior exact rows were not rehashed.",
        "Exact copied bytes do not establish import resolution, package Git pins, runtime qualification, or proof credit.",
        "No original qualification or compilation receipt was synthesized.",
        "New files use mode 0644. Runtime executable permissions, if needed, require separate verification.",
    ]
    body = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode()
    install(output / "RESTORE_RESULT.json", body)
    print(json.dumps(dict(report=str(output / "RESTORE_RESULT.json"), summary=report["summary"], **CREDIT)))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", type=Path, required=True)
    parser.add_argument("--snapshot-sha256", default=SNAPSHOT_SHA, help="SHA of uncompressed original snapshot")
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--inventory-sha256", required=True)
    parser.add_argument("--metadata-packet", type=Path)
    parser.add_argument("--metadata-sha256", help="SHA of the supplied metadata packet or its outer wrapper")
    parser.add_argument("--packet", type=Path, action="append", default=[])
    parser.add_argument("--donor-file", type=Path, action="append", default=[])
    parser.add_argument("--donor-dir", type=Path, action="append", default=[])
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    try:
        return restore(args)
    except (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile, lzma.LZMAError) as error:
        print("RESTORE_REFUSED " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
