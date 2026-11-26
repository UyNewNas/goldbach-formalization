python3 -I -B - <<'PY'
import os, stat, time, json, sys
from collections import Counter
ROOT = "/workspace"
BASENAMES = (
    "Part5OriginalH430FullMemberMeasurable",
    "Part5OriginalH430FullMemberStrips",
    "Part5OriginalH430HistoryRoughnessCore",
    "Part5OriginalH430HistoryQuotientCounts",
)
NAMES = {name + ext: (name, ext) for name in BASENAMES
         for ext in (".lean", ".olean", ".json")}
MAX_SECONDS = 45
MAX_ENTRIES = 1000000
MAX_DIRECTORIES = 100000
MAX_DEPTH = 64
MAX_MATCHES = 256
MAX_OUTPUT_BYTES = 131072
SUMMARY_RESERVE = 8192
started = time.monotonic()
counts = Counter()
errors = Counter()
stack = []
written = 0
stop_reason = None
completed = False

def emit(row, reserve=SUMMARY_RESERVE):
    global written
    payload = (json.dumps(row, ensure_ascii=True, separators=(",", ":")) + "\n").encode()
    if written + len(payload) + reserve > MAX_OUTPUT_BYTES:
        return False
    sys.stdout.buffer.write(payload)
    sys.stdout.buffer.flush()
    written += len(payload)
    return True

def close_frame(frame):
    descriptor, iterator, _, _ = frame
    iterator.close()
    try:
        os.close(descriptor)
    except OSError:
        pass

try:
    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_DIRECTORY"):
        raise RuntimeError("NO_NOFOLLOW_DIRECTORY_SUPPORT")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    root_fd = os.open(ROOT, flags)
    try:
        root_iterator = os.scandir(root_fd)
    except BaseException:
        os.close(root_fd)
        raise
    stack.append((root_fd, root_iterator, ROOT, 0))
    counts["directories_opened"] = 1
    while stack:
        if time.monotonic() - started >= MAX_SECONDS:
            stop_reason = "TIME_LIMIT"
            break
        if counts["entries_seen"] >= MAX_ENTRIES:
            stop_reason = "ENTRY_LIMIT"
            break
        descriptor, iterator, directory, depth = stack[-1]
        try:
            entry = next(iterator)
        except StopIteration:
            close_frame(stack.pop())
            continue
        except OSError as exc:
            errors["scandir_errno_" + str(exc.errno)] += 1
            close_frame(stack.pop())
            continue
        counts["entries_seen"] += 1
        if entry.name == ".git":
            counts["git_entries_excluded"] += 1
            continue
        if entry.name in NAMES:
            if counts["matches_emitted"] >= MAX_MATCHES:
                stop_reason = "MATCH_LIMIT"
                break
            try:
                info = os.stat(entry.name, dir_fd=descriptor, follow_symlinks=False)
            except OSError as exc:
                errors["matched_lstat_errno_" + str(exc.errno)] += 1
            else:
                kind = ("regular" if stat.S_ISREG(info.st_mode) else
                        "symlink_not_followed" if stat.S_ISLNK(info.st_mode) else
                        "directory" if stat.S_ISDIR(info.st_mode) else "other")
                row = {"kind": "exact_basename_match", "basename": NAMES[entry.name][0],
                       "extension": NAMES[entry.name][1],
                       "path": os.path.join(directory, entry.name), "entry_type": kind,
                       "lstat": {"dev": info.st_dev, "inode": info.st_ino,
                                 "mode": info.st_mode, "size": info.st_size,
                                 "mtime_ns": info.st_mtime_ns, "ctime_ns": info.st_ctime_ns},
                       "file_content_read": False, "qualification_claim": False}
                if not emit(row):
                    stop_reason = "OUTPUT_LIMIT"
                    break
                counts["matches_emitted"] += 1
        try:
            if entry.is_symlink():
                counts["symlinks_not_followed"] += 1
                continue
            is_directory = entry.is_dir(follow_symlinks=False)
        except OSError as exc:
            errors["entry_type_errno_" + str(exc.errno)] += 1
            continue
        if not is_directory:
            continue
        if depth >= MAX_DEPTH:
            errors["depth_limit_subtrees_not_visited"] += 1
            continue
        if counts["directories_opened"] >= MAX_DIRECTORIES:
            stop_reason = "DIRECTORY_LIMIT"
            break
        child_fd = None
        try:
            child_fd = os.open(entry.name, flags, dir_fd=descriptor)
            child_iterator = os.scandir(child_fd)
        except OSError as exc:
            if child_fd is not None:
                os.close(child_fd)
            errors["directory_open_errno_" + str(exc.errno)] += 1
            continue
        stack.append((child_fd, child_iterator, os.path.join(directory, entry.name), depth + 1))
        counts["directories_opened"] += 1
    completed = not stack and stop_reason is None and not errors
except Exception as exc:
    stop_reason = "UNEXPECTED_" + type(exc).__name__
    if isinstance(exc, OSError):
        errors["top_errno_" + str(exc.errno)] += 1
finally:
    while stack:
        close_frame(stack.pop())

summary = {
    "kind": "bounded_exact_basename_locator_summary", "root": ROOT,
    "exact_names": sorted(NAMES), "hidden_directories_included": True,
    "excluded_entry_name": ".git", "all_symlinks_not_followed": True,
    "nonsymlink_scope_completed": completed, "stop_reason": stop_reason,
    "counts": dict(counts), "errors_by_kind_only": dict(errors),
    "elapsed_seconds": time.monotonic() - started,
    "limits": {"seconds": MAX_SECONDS, "entries": MAX_ENTRIES,
               "directories": MAX_DIRECTORIES, "depth": MAX_DEPTH,
               "matches": MAX_MATCHES, "stdout_bytes": MAX_OUTPUT_BYTES},
    "file_content_reads": 0, "filesystem_writes": 0, "Lean_invocations": 0,
    "qualified_objects_or_source_claim": False,
    "absence_scope": "Only this exact basename set in the completed nonsymlink directory scope; no global absence or JSON-content search."
}
if not emit(summary, reserve=0):
    raise SystemExit(3)
raise SystemExit(0 if completed else 2)
PY
