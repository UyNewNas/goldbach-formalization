"""Shared, source-pinned helpers for a two-job solid-XZ diagnostic-metadata retention draft02.

Importing this file performs no workspace reads or writes.  Nothing here invokes
the compiler, the audit runner, a registry writer, or a remote API.
"""
from __future__ import annotations

import contextlib
import fcntl
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import sys
import tarfile
import time

MANIFEST_SHA256 = "d8ec23b6d0d2aca0ffc4f24abc4693c3df7f587f23336757c37417391d5af71a"
SCRIPT_NAMES = (
    "retention-manifest.json", "retention_common.py", "stage1_preserve.py",
    "stage2_verify_release.py", "restore_metadata.py",
    "original-archive-1087-command.sh", "original-archive-b55-command.sh",
    "evidence-1087-blob.json", "evidence-b55-blob.json",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def now():
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def process_identity():
    return {"pid": os.getpid(), "start_ticks": Path("/proc/self/stat").read_text().split()[21],
            "boot_id": Path("/proc/sys/kernel/random/boot_id").read_text().strip()}


def load_manifest():
    directory = Path(__file__).resolve().parent
    path = directory / "retention-manifest.json"
    raw = path.read_bytes()
    require(sha(raw) == MANIFEST_SHA256, "Retention manifest bytes changed")
    value = json.loads(raw)
    require(directory == Path(value["scripts_dir"]), "Only the fixed new scripts directory is executable")
    targets = value["targets"]
    require(len(targets) == value["target_count"] == 13, "Whitelist count changed")
    require(len({r["path"] for r in targets}) == 13, "Duplicate whitelist path")
    require(sum(r["bytes"] for r in targets) == value["logical_bytes"] == 135877860,
            "Whitelist logical byte total changed")
    return value


def script_bindings(manifest):
    directory = Path(manifest["scripts_dir"])
    return {name: {"bytes": (directory / name).stat().st_size,
                   "sha256": digest(directory / name)} for name in SCRIPT_NAMES}


def fsync_dir(path):
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def write_new(path, raw):
    path = Path(path)
    with path.open("xb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    fsync_dir(path.parent)


def free_bytes(path):
    st = os.statvfs(path)
    return st.f_bavail * st.f_frsize


def reserve(manifest, additional=0):
    available = free_bytes(manifest["worktree"])
    require(available >= manifest["reserve_bytes"] + additional,
            f"Persistent reserve would be breached: free={available}, additional={additional}")
    return available


@contextlib.contextmanager
def original_lock(manifest):
    # Same existing lock as the original compiler/audit wrappers; do not create one.
    fd = os.open(manifest["lock_path"], os.O_RDONLY | os.O_NOFOLLOW)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        yield
    finally:
        os.close(fd)


def file_info(path, *, single_link=False):
    path = Path(path)
    require(path.is_absolute() and path.resolve(strict=True) == path,
            "Noncanonical or symlink path: " + str(path))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, "rb") as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode), "Not a regular file: " + str(path))
        require(not single_link or before.st_nlink == 1,
                "Release target has more than one hard link: " + str(path))
        h = hashlib.file_digest(stream, "sha256").hexdigest()
        after = os.fstat(stream.fileno())
    identity = lambda s: (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns, s.st_nlink)
    require(identity(before) == identity(after), "File changed while reading: " + str(path))
    return {"path": str(path), "bytes": after.st_size, "sha256": h,
            "device": after.st_dev, "inode": after.st_ino,
            "mtime_ns": after.st_mtime_ns, "ctime_ns": after.st_ctime_ns,
            "links": after.st_nlink, "allocated_bytes": after.st_blocks * 512}


def check_target(record):
    value = file_info(record["path"], single_link=True)
    require(value["bytes"] == record["bytes"] and value["sha256"] == record["sha256"],
            "Whitelist source bytes changed: " + record["path"])
    return value


def capture_canonical(manifest):
    """Read a fresh current registry; never assume the earlier 1c1929 digest."""
    root = Path(manifest["worktree"])
    git = lambda *args, cwd=root: subprocess.check_output(["git", *args], cwd=cwd, text=True).strip()
    require(git("rev-parse", "HEAD") == manifest["source_pin"], "P2 is not at the authorized b55 pin")
    require(not git("status", "--porcelain", "--untracked-files=no"), "Tracked source is dirty")
    files = {name: digest(root / name) for name in manifest["pinned_files"]}
    require(files == manifest["pinned_files"], "Pinned source/verifier bytes changed")
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(root / "verification/part2"))
    from run_winner9_private_audit import LEAN, LEANCHECKER, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
    from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes
    require(PIN == manifest["mathlib_pin"] and git("rev-parse", "HEAD", cwd=MATHLIB) == PIN,
            "Locked live Mathlib pin changed")
    runtime = {"lean": digest(LEAN), "leanchecker": digest(LEANCHECKER)}
    require(runtime == manifest["runtime_sha256"], "Lean/checker runtime bytes changed")
    snap_path = Path(manifest["native_snapshot_path"])
    require(digest(snap_path) == manifest["native_snapshot_sha256"], "Native snapshot bytes changed")
    lib = root / ".lake/p2-private/lib"
    external = ExternalSnapshot(snap_path, lean=LEAN, mathlib_pin=PIN, project_lib=lib)
    native = external.binding()
    require(native["snapshot_sha256"] == manifest["native_snapshot_sha256"] and
            native["context_signature"] == manifest["native_context_signature"], "Native context differs")
    full = project_nodes(root, manifest["whole_target"])
    require(len(full) == 324 and sha(("\n".join(full) + "\n").encode()) == manifest["full324_ordered_fingerprint"],
            "Full ordered 324 closure changed")
    mark_project_nodes(full, set(external.modules))
    toolchain = {"lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
                 "lean_binary_sha256": runtime["lean"], "mathlib_commit": PIN}
    frozen = snapshot(root, lib, full, toolchain, external)
    registry = root / ".lake/p2-private/records.json"
    registry_raw = registry.read_bytes()
    records = json.loads(registry_raw)
    prereq = {}
    for target in manifest["strict321_roots"]:
        prereq.update(project_nodes(root, target))
    require(len(prereq) == 321, "Original symbolic prerequisite closure differs")
    verify_compilation(records, prereq, frozen)  # Read-only original API, no driver invocation.
    forbidden = {str(registry), *[str(root / n) for n in manifest["pinned_files"]],
                 *[str(node["source"]) for node in full.values()],
                 *[v["object"] for v in frozen["project"].values()], *external.files}
    require(not ({r["path"] for r in manifest["targets"]} & forbidden),
            "A release target aliases a canonical/native input")
    require(digest(registry) == sha(registry_raw), "Registry changed during the read-only snapshot")
    headers = {}
    for suffix in ["ArchivedTotalCandidate", "CachedEndpointCandidate", "WholeFunctionalEndpoint"]:
        name = "ImbalancedChen.P2OriginalCompact" + suffix
        record = records.get(name, {})
        headers[name] = {k: record.get(k) for k in
                         ["module", "exit_code", "source_sha256", "object_sha256", "closure_signature"]}
    retained = {r["path"]: {"bytes": Path(r["path"]).stat().st_size, "sha256": digest(r["path"])}
                for r in manifest["excluded_conditional"]}
    for r in manifest["excluded_conditional"]:
        require(retained[r["path"]] == {"bytes": r["bytes"], "sha256": r["sha256"]},
                "Excluded original metadata changed: " + r["path"])
    return {"head": manifest["source_pin"], "tracked_clean": True,
            "pinned_files": files, "runtime": runtime, "mathlib_pin": PIN,
            "full324_frozen_snapshot_sha256": sha(encoded(frozen)),
            "full324_ordered_fingerprint": manifest["full324_ordered_fingerprint"],
            "registry_bytes": len(registry_raw), "registry_sha256": sha(registry_raw),
            "A_B_W_current_record_headers_observed_only": headers,
            "native_binding_sha256": sha(encoded(native)),
            "excluded_conditional_files": retained,
            "original_verify_compilation_321_read_only_passed": True,
            "new_compiler_or_audit_credit": False}


def verify_archive(spec, *, extracts=None, tar_destination=None):
    """Verify exact gzip, every tar byte, every member, and the complete FILES index."""
    path = Path(spec["path"])
    actual = file_info(path)
    require(actual["bytes"] == spec["gzip_bytes"] and actual["sha256"] == spec["gzip_sha256"],
            "Backup gzip differs: " + str(path))
    if "git_blob_sha" in spec:
        h = hashlib.sha1(b"blob " + str(actual["bytes"]).encode() + b"\0")
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1048576), b""):
                h.update(chunk)
        require(h.hexdigest() == spec["git_blob_sha"], "Backup Git blob differs")
    h = hashlib.sha256(); total = 0
    with contextlib.ExitStack() as stack:
        source = stack.enter_context(gzip.open(path, "rb"))
        sink = stack.enter_context(Path(tar_destination).open("xb")) if tar_destination else None
        for data in iter(lambda: source.read(1048576), b""):
            total += len(data); h.update(data)
            if sink is not None:
                sink.write(data)
    require(total == spec["tar_bytes"] and h.hexdigest() == spec["tar_sha256"], "Complete tar stream differs")
    seen = {}; index_raw = None
    extracts = extracts or {}
    require(set(extracts) <= set(spec["members"]), "Unexpected requested archive member")
    with tarfile.open(path, mode="r|gz") as archive:
        for member in archive:
            name = member.name; member_path = PurePosixPath(name)
            require(member.isfile() and not member_path.is_absolute() and ".." not in member_path.parts and
                    name in spec["members"] and name not in seen, "Unexpected/unsafe/duplicate tar member")
            expected = spec["members"][name]
            require(member.size == expected["bytes"], "Tar member size differs")
            mh = hashlib.sha256(); n = 0; kept = []
            with contextlib.ExitStack() as stack:
                source = stack.enter_context(archive.extractfile(member))
                sink = stack.enter_context(Path(extracts[name]).open("xb")) if name in extracts else None
                for data in iter(lambda: source.read(1048576), b""):
                    n += len(data); mh.update(data)
                    if sink is not None:
                        sink.write(data)
                    if name == "FILES.json":
                        kept.append(data)
            seen[name] = {"bytes": n, "sha256": mh.hexdigest()}
            require(seen[name] == expected, "Tar member SHA differs: " + name)
            if name == "FILES.json":
                index_raw = b"".join(kept)
    require(seen == spec["members"] and len(seen) == spec["file_count"], "Incomplete member coverage")
    require(index_raw is not None and json.loads(index_raw) == {k: v for k, v in seen.items() if k != "FILES.json"},
            "FILES index is incomplete or inconsistent")
    require(digest(path) == spec["gzip_sha256"], "Archive changed during validation")
    return {"gzip_bytes": actual["bytes"], "gzip_sha256": actual["sha256"],
            "tar_bytes": total, "tar_sha256": h.hexdigest(), "member_count": len(seen),
            "FILES_bytes": len(index_raw), "FILES_sha256": sha(index_raw),
            "every_member_verified": True, "full_tar_byte_stream_verified": True}


def copy_exact(source, destination, expected):
    with Path(source).open("rb") as reader, Path(destination).open("xb") as writer:
        shutil.copyfileobj(reader, writer, 1048576)
    require(Path(destination).stat().st_size == expected["bytes"] and digest(destination) == expected["sha256"],
            "Independent reconstruction/copy differs")




def receipt_info(path):
    path = Path(path)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": digest(path)}


def marker_path(record):
    return Path(record["path"] + ".P24_RECONSTRUCT.json")


def ensure_marker_absent(record):
    require(not os.path.lexists(marker_path(record)), "Reconstruction marker already exists; manual review required")


def matching_identity(actual, original):
    keys = ("path", "bytes", "sha256", "device", "inode", "mtime_ns", "ctime_ns", "links")
    return all(actual[k] == original[k] for k in keys)


def observe_targets(records):
    """Report actual partial state even if an unlink-adjacent operation failed."""
    result = {"missing": [], "remaining": [], "uninspectable": []}
    for record in records:
        try:
            st = os.lstat(record["path"])
            result["remaining"].append({"path": record["path"], "bytes_observed": st.st_size,
                                        "regular_file": stat.S_ISREG(st.st_mode),
                                        "device": st.st_dev, "inode": st.st_ino})
        except FileNotFoundError:
            result["missing"].append({"path": record["path"], "expected_bytes": record["bytes"],
                                      "expected_sha256": record["sha256"]})
        except OSError as error:
            result["uninspectable"].append({"path": record["path"],
                                           "error": type(error).__name__ + ": " + str(error)})
    return result


# The functions below are draft02-only.  The original canonical guard above is
# inherited from reviewed draft01; the payload is metadata, not Lean evaluation.
def gzip_runtime_profile():
    import inspect
    import zlib
    executable = Path(sys.executable).resolve(strict=True)
    zlib_file = getattr(zlib, "__file__", None)
    zlib_path = Path(zlib_file).resolve(strict=True) if zlib_file is not None else None
    require(zlib_path is not None or (zlib.__spec__.origin == "built-in" and "zlib" in sys.builtin_module_names),
            "Unidentified zlib implementation")
    return {"python_version": sys.version, "python_hexversion": sys.hexversion,
            "python_executable": str(executable), "python_executable_sha256": digest(executable),
            "gzip_module": str(Path(gzip.__file__).resolve()), "gzip_module_sha256": digest(gzip.__file__),
            "gzip_compress_signature": str(inspect.signature(gzip.compress)),
            "original_implicit_compresslevel": inspect.signature(gzip.compress).parameters["compresslevel"].default,
            "zlib_module_origin": zlib.__spec__.origin,
            "zlib_extension": str(zlib_path) if zlib_path else None,
            "zlib_extension_sha256": digest(zlib_path) if zlib_path else None,
            "builtin_zlib_owner_executable_sha256": digest(executable) if zlib_path is None else None,
            "zlib_compiled_version": zlib.ZLIB_VERSION, "zlib_runtime_version": zlib.ZLIB_RUNTIME_VERSION,
            "platform": sys.platform, "byteorder": sys.byteorder,
            "original_recipe": "gzip.compress(tar, mtime=0)"}


def require_independent_tmp(manifest):
    require(os.stat("/tmp").st_dev != os.stat(manifest["worktree"]).st_dev,
            "Full reconstruction requires the separately measured /tmp filesystem")
    need = (2 * sum(a["tar_bytes"] for a in manifest["archives"]) + manifest["logical_bytes"] +
            2 * manifest["supplement_raw_bytes"] + 2 * manifest["max_control_files_bytes"] +
            sum(a["gzip_bytes"] for a in manifest["archives"]) + manifest["reserve_bytes"])
    require(free_bytes("/tmp") >= need, f"Insufficient independent /tmp capacity: need={need}")
    return need


def rebuild_gzip(tar_path, destination, original, runtime):
    require(gzip_runtime_profile() == runtime, "Exact gzip/zlib/interpreter runtime changed")
    tar_path = Path(tar_path)
    require(tar_path.stat().st_size == original["tar_bytes"] and digest(tar_path) == original["tar_sha256"],
            "Original complete tar bytes differ")
    # This is the literal original call: no regeneration of tar headers, JSON,
    # compression defaults, gzip headers, member order, timestamps, or padding.
    raw_tar = tar_path.read_bytes()
    raw_gzip = gzip.compress(raw_tar, mtime=0)
    require(len(raw_gzip) == original["gzip_bytes"] and sha(raw_gzip) == original["gzip_sha256"],
            "Current pinned runtime does not reproduce the exact original gzip")
    require(hashlib.sha1(b"blob " + str(len(raw_gzip)).encode() + b"\0" + raw_gzip).hexdigest() == original["git_blob_sha"],
            "Reconstructed original Git blob differs")
    write_new(destination, raw_gzip)
    return receipt_info(destination)


def bytes_equal_files(left, right):
    with Path(left).open("rb") as a, Path(right).open("rb") as b:
        while True:
            x, y = a.read(1048576), b.read(1048576)
            if x != y:
                return False
            if not x:
                return True


def build_solid_bundle(manifest, directory, canonical_before, original_infos, runtime):
    """Build in independent tmp; no original or persistent backup is removed."""
    import lzma
    directory = Path(directory)
    sources = {}
    originals_verified = {}
    for original in manifest["archives"]:
        descriptor = Path(original["descriptor_path"])
        require(descriptor.stat().st_size == original["descriptor_bytes"] and digest(descriptor) == original["descriptor_sha256"],
                "Original archive descriptor changed")
        tar_path = directory/(original["id"]+"-original.tar")
        originals_verified[original["id"]] = verify_archive(original, tar_destination=tar_path)
        rebuilt = directory/(original["id"]+"-reproduced.tar.gz")
        rebuild_gzip(tar_path, rebuilt, original, runtime)
        require(bytes_equal_files(rebuilt, original["path"]), "Original gzip byte comparison failed")
        sources["archives/evidence-"+original["id"]+".tar"] = tar_path
        sources["metadata/evidence-"+original["id"]+"-descriptor.json"] = descriptor.read_bytes()
    for record in manifest["targets"]:
        if record["restore_kind"] == "outer_member":
            check_target(record)
            sources[record["solid_member"]] = Path(record["path"])
    script_dir = Path(manifest["scripts_dir"])
    for name in SCRIPT_NAMES:
        sources[("recipe/" if name.endswith(".py") or name == "retention-manifest.json" else "metadata/")+name] = (script_dir/name).read_bytes()
    sources["metadata/gzip-runtime-and-recipe.json"] = encoded(runtime)
    sources["metadata/original-file-stat-map.json"] = encoded(original_infos)
    sources["metadata/canonical-context-before.json"] = encoded(canonical_before)
    sources["metadata/script-bindings.json"] = encoded(script_bindings(manifest))
    index = {name: {"bytes": value.stat().st_size if isinstance(value, Path) else len(value),
                    "sha256": digest(value) if isinstance(value, Path) else sha(value)} for name, value in sources.items()}
    index_raw = encoded(index); sources["FILES.json"] = index_raw
    members = dict(index, **{"FILES.json": {"bytes": len(index_raw), "sha256": sha(index_raw)}})
    destination = directory/"preserved-complete-inputs.tar.xz"
    tar_hash = hashlib.sha256(); tar_bytes = 0

    class CountedWriter:
        def __init__(self, stream): self.stream = stream
        def write(self, data):
            nonlocal tar_bytes
            require(free_bytes(directory) >= len(data)+manifest["reserve_bytes"], "Temporary reserve breached")
            tar_hash.update(data); tar_bytes += len(data)
            return self.stream.write(data)
        def flush(self): self.stream.flush()

    with lzma.open(destination, "xb", format=lzma.FORMAT_XZ, check=lzma.CHECK_CRC64, preset=6) as compressed:
        with tarfile.open(mode="w|", fileobj=CountedWriter(compressed), format=tarfile.USTAR_FORMAT) as archive:
            for name in sorted(sources):
                info = tarfile.TarInfo(name); info.size = members[name]["bytes"]
                info.uid = info.gid = info.mtime = 0; info.uname = info.gname = ""; info.mode = 0o444
                value = sources[name]
                if isinstance(value, Path):
                    with value.open("rb") as stream:
                        archive.addfile(info, stream)
                else:
                    archive.addfile(info, io.BytesIO(value))
    spec = {"path": str(destination), "xz_bytes": destination.stat().st_size, "xz_sha256": digest(destination),
            "tar_bytes": tar_bytes, "tar_sha256": tar_hash.hexdigest(), "members": members,
            "file_count": len(members), "FILES_member": members["FILES.json"],
            "format": "one solid XZ stream over a complete outer tar", "xz_preset": 6, "xz_check": "CRC64"}
    verification = verify_solid_bundle(spec)
    return spec, {"original_archives": originals_verified, "solid_bundle": verification,
                  "both_original_gzip_files_reproduced_and_byte_compared": True}


def verify_solid_bundle(spec, *, extracts=None):
    import lzma
    path = Path(spec["path"])
    require(path.stat().st_size == spec["xz_bytes"] and digest(path) == spec["xz_sha256"], "Solid XZ bytes differ")
    th = hashlib.sha256(); total = 0
    with lzma.open(path, "rb") as stream:
        for data in iter(lambda: stream.read(1048576), b""):
            th.update(data); total += len(data)
    require(total == spec["tar_bytes"] and th.hexdigest() == spec["tar_sha256"], "Complete outer tar stream differs")
    extracts = extracts or {}; require(set(extracts) <= set(spec["members"]), "Unknown solid bundle extraction")
    seen = {}; files_raw = None
    with tarfile.open(path, mode="r|xz") as archive:
        for member in archive:
            name = member.name; safe = PurePosixPath(name)
            require(member.isfile() and not safe.is_absolute() and ".." not in safe.parts and name not in seen and name in spec["members"],
                    "Unsafe/duplicate/unexpected solid bundle member")
            require(member.size == spec["members"][name]["bytes"], "Solid member size differs")
            h = hashlib.sha256(); n = 0; chunks = []
            with contextlib.ExitStack() as stack:
                source = stack.enter_context(archive.extractfile(member))
                target = stack.enter_context(Path(extracts[name]).open("xb")) if name in extracts else None
                for data in iter(lambda: source.read(1048576), b""):
                    h.update(data); n += len(data)
                    if target is not None: target.write(data)
                    if name == "FILES.json": chunks.append(data)
            seen[name] = {"bytes": n, "sha256": h.hexdigest()}
            require(seen[name] == spec["members"][name], "Solid member bytes differ: "+name)
            if name == "FILES.json": files_raw = b"".join(chunks)
    require(seen == spec["members"] and len(seen) == spec["file_count"], "Solid member coverage incomplete")
    require(files_raw is not None and json.loads(files_raw) == {n:r for n,r in seen.items() if n != "FILES.json"},
            "Solid FILES index differs")
    require(digest(path) == spec["xz_sha256"], "Solid bundle changed while reading")
    return {"xz_bytes": spec["xz_bytes"], "xz_sha256": spec["xz_sha256"],
            "tar_bytes": total, "tar_sha256": th.hexdigest(), "member_count": len(seen),
            "FILES_sha256": sha(files_raw), "every_byte_member_and_index_verified": True}


def reconstruct_all(manifest, spec, directory, expected_runtime):
    """Uses only the solid XZ and SHA-bound installed recipe, never loose originals."""
    directory = Path(directory)
    # Recheck against the measured bundle after any stage1 build temporaries
    # already occupy tmpfs.  This includes the complete copy, all extracted
    # outer members, duplicate inner JSONs, both rebuilt gzips and block overhead.
    scratch_need = (spec["xz_bytes"] + sum(r["bytes"] for r in spec["members"].values()) +
                    sum(r["bytes"] for r in manifest["targets"] if r["restore_kind"] == "inner_member") +
                    sum(a["gzip_bytes"] for a in manifest["archives"]) +
                    manifest["reserve_bytes"] + manifest.get("max_control_files_bytes", 4194304))
    require(free_bytes(directory) >= scratch_need, "Insufficient measured space for full independent reconstruction")
    copied = directory/"independent-inputs.tar.xz"
    copy_exact(spec["path"], copied, {"bytes": spec["xz_bytes"], "sha256": spec["xz_sha256"]})
    copied_spec = dict(spec, path=str(copied))
    extracted = {name: directory/f"outer-member-{i:03d}.bin" for i,name in enumerate(sorted(spec["members"]))}
    outer = verify_solid_bundle(copied_spec, extracts=extracted)
    stored_manifest = json.loads(extracted["recipe/retention-manifest.json"].read_bytes())
    require(stored_manifest == manifest, "Stored reconstruction map differs")
    runtime = json.loads(extracted["metadata/gzip-runtime-and-recipe.json"].read_bytes())
    require(runtime == expected_runtime == gzip_runtime_profile(), "Gzip runtime recipe changed between jobs")
    for name in SCRIPT_NAMES:
        key = ("recipe/" if name.endswith(".py") or name == "retention-manifest.json" else "metadata/")+name
        require(extracted[key].read_bytes() == (Path(manifest["scripts_dir"])/name).read_bytes(),
                "Retained recipe input differs: "+name)
    reconstructed = {}; nested = {}
    for original in manifest["archives"]:
        stored_descriptor = extracted["metadata/evidence-"+original["id"]+"-descriptor.json"]
        require(stored_descriptor.stat().st_size == original["descriptor_bytes"] and
                digest(stored_descriptor) == original["descriptor_sha256"], "Retained original descriptor differs")
        tar_path = extracted["archives/evidence-"+original["id"]+".tar"]
        gz = directory/(original["id"]+"-independently-reconstructed.tar.gz")
        rebuild_gzip(tar_path, gz, original, runtime)
        inner_extracts = {}
        for i,record in enumerate(manifest["targets"]):
            if record["backup_id"] == original["id"] and record["restore_kind"] == "inner_member":
                target = directory/f"inner-reconstructed-{i:02d}.json"
                inner_extracts[record["member"]] = target; reconstructed[record["path"]] = target
            elif record["backup_id"] == original["id"] and record["restore_kind"] == "gzip_from_tar":
                reconstructed[record["path"]] = gz
        nested[original["id"]] = verify_archive(dict(original,path=str(gz)), extracts=inner_extracts)
    for record in manifest["targets"]:
        if record["restore_kind"] == "outer_member": reconstructed[record["path"]] = extracted[record["solid_member"]]
    require(set(reconstructed) == {r["path"] for r in manifest["targets"]}, "Not all thirteen targets reconstructed")
    for record in manifest["targets"]:
        restored = reconstructed[record["path"]]
        require(restored.stat().st_size == record["bytes"] and digest(restored) == record["sha256"], "Reconstruction bytes differ")
    return reconstructed, {"outer_bundle": outer, "original_inner_archives": nested,
                           "all_thirteen_exact_bytes_reconstructed_from_solid_bundle_only": True}
