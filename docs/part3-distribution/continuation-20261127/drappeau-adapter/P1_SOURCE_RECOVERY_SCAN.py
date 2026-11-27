import base64
import collections
import datetime
import hashlib
import json
import os
import signal
import stat
import tarfile
import time
import zipfile

TARGETS = [
    {"basename": "Part3NativeCuspAllowedRowRightAction.lean", "bytes": 3939, "sha256": "30526477182739aa5b30fdf90768db1794d1d0e493c6decd0a66e4f2e305e6e6"},
    {"basename": "Part3NativeAllCuspEisenstein.lean", "bytes": 5217, "sha256": "43f0110880087df79b0faccc8f57b5218bcbbd3e3ed509b7488903b5cbe3b31a"},
    {"basename": "Part3NativeAllCuspEisensteinSpatialConvergence.lean", "bytes": 6366, "sha256": "71ab5c0d4579f8629c46b6be0e91e25404e4da17d106bc98974aa5e3bc71774b"},
    {"basename": "Part3OriginalCharacterPairDilation.lean", "bytes": 6909, "sha256": "c35493a2a803c72472e9ab70cfc0bdffb615dafb994c2688b58b68e2fe86131e"},
    {"basename": "Part3NativeAllCuspFrameCovariance.lean", "bytes": 7678, "sha256": "8522119e88e35f168f4965f028204ecfe16c21a8f02313090f9c4851703b88b9"},
    {"basename": "Part3CharacterPairDivisorAmplitude.lean", "bytes": 9365, "sha256": "99deabe8782b6626f2fc9dbc73cf4b9589442b7b5c46bf34de6e8c8755741fb8"},
]
SCAN_ROOT = "/workspace"
SECONDS = 100
started = time.monotonic()
SIZES = {item["bytes"] for item in TARGETS}
BY_HASH = {item["sha256"]: item for item in TARGETS}
MAX_BYTES = max(SIZES)
archive_suffixes = (
    ".zip", ".zipx", ".whl", ".jar", ".tar", ".tar.gz", ".tgz",
    ".tar.bz2", ".tbz", ".tbz2", ".tar.xz", ".txz", ".tar.zst", ".tzst",
)
summary = {
    "schema": "p35-remote-size-sha-recovery-v1",
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "targets": TARGETS,
    "scope": {
        "root": SCAN_ROOT,
        "filesystem_filename_suffix_restriction": None,
        "prune": ["all .git directories", "all node_modules directories", "all .lake/packages directories", "all .lake/build directories"],
        "preserved": ".lake/proof-continuation and other source-review/draft directories",
        "directory_symlinks": "not followed",
        "file_symlinks": "followed only when the resolved file is inside /workspace",
        "archive_discovery": "conventional suffixes, case-insensitive",
        "archive_suffixes": archive_suffixes,
        "archive_member_filename_suffix_restriction": None,
        "nested_archives": "not recursively opened",
        "git_objects": "not scanned",
        "writes_to_remote_filesystem": False,
        "snapshot": "live traversal, not an atomic filesystem snapshot",
    },
    "enumeration": {"directories": 0, "files_seen": 0, "regular_files": 0, "pruned_paths": [], "skipped_directory_symlinks": [], "skipped_file_symlinks_outside_scope": [], "complete": False},
    "files": {"size_candidates": 0, "hashed_candidates": 0, "exact_sha_matches": 0, "candidates": []},
    "archives": {"discovered": 0, "attempted": 0, "completed": 0, "members_enumerated": 0, "regular_members": 0, "size_candidates": 0, "hashed_candidates": 0, "exact_sha_matches": 0, "records": [], "unattempted": [], "complete": False},
    "exact_matches": [],
    "errors": [],
    "deadline": {"seconds": SECONDS, "hit": False, "phase": "enumeration", "path": None},
}
archive_paths = []
seen_match_content = set()
last_progress = started


class ScanDeadline(Exception):
    pass


def deadline_signal(_signum, _frame):
    raise ScanDeadline("internal scan deadline reached")


def check_deadline():
    global last_progress
    now = time.monotonic()
    if now - started >= SECONDS:
        raise ScanDeadline("internal scan deadline reached")
    if now - last_progress >= 25:
        print(json.dumps({"event": "progress", "elapsed_seconds": round(now - started, 3), "phase": summary["deadline"]["phase"], "files_seen": summary["enumeration"]["files_seen"], "archives_completed": summary["archives"]["completed"], "members_enumerated": summary["archives"]["members_enumerated"]}), flush=True)
        last_progress = now


def error(stage, path, exc):
    summary["errors"].append({"stage": stage, "path": path, "error": str(exc), "exception": type(exc).__name__})


def note_hash(record, data, section):
    digest = hashlib.sha256(data).hexdigest()
    record["observed_bytes"] = len(data)
    record["sha256"] = digest
    section["hashed_candidates"] += 1
    target = BY_HASH.get(digest)
    if target is not None and len(data) == target["bytes"]:
        match = dict(record, target=target["basename"])
        summary["exact_matches"].append(match)
        section["exact_sha_matches"] += 1
        event = dict(match, event="exact_sha256_match")
        if digest not in seen_match_content:
            event["source_bytes_base64"] = base64.b64encode(data).decode("ascii")
            seen_match_content.add(digest)
        print(json.dumps(event), flush=True)


def read_candidate(stream, record, section):
    data = stream.read(MAX_BYTES + 1)
    if len(data) != record["bytes"]:
        raise OSError("observed byte length differs from size metadata: %d != %d" % (len(data), record["bytes"]))
    note_hash(record, data, section)


signal.signal(signal.SIGALRM, deadline_signal)
signal.alarm(SECONDS)
try:
    for directory, dirs, files in os.walk(SCAN_ROOT, topdown=True, followlinks=False,
            onerror=lambda exc: error("walk", getattr(exc, "filename", None), exc)):
        check_deadline()
        summary["deadline"]["path"] = directory
        summary["enumeration"]["directories"] += 1
        retained = []
        for child in sorted(dirs):
            path = os.path.join(directory, child)
            if child in {".git", "node_modules"} or (os.path.basename(directory) == ".lake" and child in {"packages", "build"}):
                summary["enumeration"]["pruned_paths"].append(path)
            elif os.path.islink(path):
                summary["enumeration"]["skipped_directory_symlinks"].append(path)
            else:
                retained.append(child)
        dirs[:] = retained
        for filename in sorted(files):
            check_deadline()
            path = os.path.join(directory, filename)
            summary["enumeration"]["files_seen"] += 1
            summary["deadline"]["path"] = path
            try:
                info = os.lstat(path)
                if stat.S_ISLNK(info.st_mode):
                    resolved = os.path.realpath(path)
                    if os.path.commonpath([SCAN_ROOT, resolved]) != SCAN_ROOT:
                        summary["enumeration"]["skipped_file_symlinks_outside_scope"].append(path)
                        continue
                    info = os.stat(path)
                if not stat.S_ISREG(info.st_mode):
                    continue
                summary["enumeration"]["regular_files"] += 1
                if info.st_size in SIZES:
                    record = {"kind": "filesystem_file", "path": path, "bytes": info.st_size}
                    summary["files"]["size_candidates"] += 1
                    summary["files"]["candidates"].append(record)
                    with open(path, "rb") as stream:
                        read_candidate(stream, record, summary["files"])
                if filename.lower().endswith(archive_suffixes):
                    archive_paths.append({"path": path, "bytes": info.st_size})
            except ScanDeadline:
                raise
            except (OSError, ValueError) as exc:
                error("file_stat_or_hash", path, exc)
    summary["enumeration"]["complete"] = True
    summary["archives"]["discovered"] = len(archive_paths)
    archive_paths.sort(key=lambda item: (item["bytes"], item["path"]))
    summary["deadline"]["phase"] = "archives"
    for index, archive in enumerate(archive_paths):
        check_deadline()
        path = archive["path"]
        summary["deadline"]["path"] = path
        summary["archives"]["attempted"] += 1
        record = dict(archive, status="running", members_enumerated=0, regular_members=0, size_candidates=0, hashed_candidates=0, exact_sha_matches=0, candidates=[])
        summary["archives"]["records"].append(record)
        try:
            if path.lower().endswith((".zip", ".zipx", ".whl", ".jar")):
                record["format"] = "zip"
                with zipfile.ZipFile(path, "r") as container:
                    for member in container.infolist():
                        check_deadline()
                        record["members_enumerated"] += 1
                        if member.is_dir():
                            continue
                        record["regular_members"] += 1
                        if member.file_size not in SIZES:
                            continue
                        candidate = {"kind": "zip_member", "archive": path, "member": member.filename, "bytes": member.file_size}
                        record["size_candidates"] += 1
                        record["candidates"].append(candidate)
                        try:
                            with container.open(member, "r") as stream:
                                read_candidate(stream, candidate, record)
                        except ScanDeadline:
                            raise
                        except Exception as exc:
                            error("zip_member_hash", path + "::" + member.filename, exc)
            else:
                record["format"] = "tar"
                with tarfile.open(path, "r|*") as container:
                    for member in container:
                        check_deadline()
                        record["members_enumerated"] += 1
                        if not member.isfile():
                            continue
                        record["regular_members"] += 1
                        if member.size not in SIZES:
                            continue
                        candidate = {"kind": "tar_member", "archive": path, "member": member.name, "bytes": member.size}
                        record["size_candidates"] += 1
                        record["candidates"].append(candidate)
                        try:
                            stream = container.extractfile(member)
                            if stream is None:
                                raise OSError("regular member has no readable stream")
                            with stream:
                                read_candidate(stream, candidate, record)
                        except ScanDeadline:
                            raise
                        except Exception as exc:
                            error("tar_member_hash", path + "::" + member.name, exc)
            record["status"] = "completed"
            summary["archives"]["completed"] += 1
        except ScanDeadline:
            record["status"] = "deadline"
            raise
        except Exception as exc:
            record["status"] = "error"
            error("archive", path, exc)
        finally:
            for key in ("members_enumerated", "regular_members", "size_candidates", "hashed_candidates", "exact_sha_matches"):
                summary["archives"][key] += record[key]
    summary["archives"]["complete"] = True
except ScanDeadline:
    summary["deadline"]["hit"] = True
except Exception as exc:
    error("fatal", summary["deadline"]["path"], exc)
finally:
    signal.alarm(0)
    summary["archives"]["discovered"] = len(archive_paths)
    attempted = {record["path"] for record in summary["archives"]["records"]}
    summary["archives"]["unattempted"] = [item for item in archive_paths if item["path"] not in attempted]
    summary["completed_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    summary["elapsed_seconds"] = round(time.monotonic() - started, 6)
    summary["errors_count"] = len(summary["errors"])
    summary["match_count"] = len(summary["exact_matches"])
    print(json.dumps({"event": "scan_result", "result": summary}), flush=True)
