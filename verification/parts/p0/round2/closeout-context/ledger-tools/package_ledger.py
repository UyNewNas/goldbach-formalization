#!/usr/bin/env python3
"""Package one frozen ledger directory for Git handoff without running verification.

Usage:
  python3 package_ledger.py LEDGER_OUTPUT_DIR REPO_TARGET_DIR
  python3 package_ledger.py --self-check

The complete input directory is retained byte-for-byte inside a deterministic
tar.gz.b64 archive. Only three readable Markdown files and compact machine
indices are copied outside that archive. No Lean source is copied to a default
repository root. Input and output directories must be separate.
"""
from __future__ import annotations

import argparse
import ast
import base64
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import tarfile
import tempfile


SCHEMA = "chen-ledger-package-v1"
DIRECT_MARKDOWN = ("MODULE_LEDGER.md", "COMPILER_TYPES.md", "SOURCE_THEOREM_TYPES.md")
REQUIRED = ("module-ledger.json",) + DIRECT_MARKDOWN
ARCHIVE_FILE = "complete-ledger.tar.gz.b64"
CHUNK = 1024 * 1024


def json_bytes(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def hash_file(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(CHUNK), b""):
            h.update(chunk)
    return h.hexdigest()


def safe_relative(name):
    if not isinstance(name, str) or not name or "\\" in name or "\0" in name:
        raise ValueError("invalid relative archive path")
    p = PurePosixPath(name)
    if not p.parts or p.is_absolute() or str(p) != name or any(x in (".", "..") for x in p.parts):
        raise ValueError("non-canonical or escaping archive path: " + name)
    return p


def validate_archive_root(name):
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", name) or name in (".", ".."):
        raise ValueError("archive root must be a simple relative basename")
    return name


def inventory(directory):
    """Inventory only this directory, without following source/evidence pointers."""
    files, directories = [], []
    for current, dirs, names in os.walk(directory, followlinks=False):
        dirs.sort()
        names.sort()
        for name in dirs:
            p = Path(current) / name
            if p.is_symlink():
                raise ValueError("symlink directory is not allowed: " + str(p))
            rel = p.relative_to(directory).as_posix()
            safe_relative(rel)
            directories.append(rel)
        for name in names:
            p = Path(current) / name
            if p.is_symlink() or not stat.S_ISREG(p.stat().st_mode):
                raise ValueError("only regular source files are allowed: " + str(p))
            rel = p.relative_to(directory).as_posix()
            safe_relative(rel)
            files.append({"path": rel, "bytes": p.stat().st_size,
                          "sha256": hash_file(p),
                          "mode": 0o755 if p.stat().st_mode & 0o111 else 0o644})
    return {"files": sorted(files, key=lambda x: x["path"]),
            "directories": sorted(directories)}


def selected(obj, keys):
    return {k: obj[k] for k in keys if k in obj}


def build_index(ledger, original_sha256):
    """A deliberately small projection; the archive keeps every original field."""
    modules = ledger.get("modules")
    if not isinstance(modules, list) or any(not isinstance(m, dict) for m in modules):
        raise ValueError("module-ledger.json must have a modules array")
    names = [m.get("module") for m in modules]
    if any(not isinstance(n, str) or not n for n in names) or len(names) != len(set(names)):
        raise ValueError("module names must be nonempty and unique")
    if ledger.get("module_count", len(modules)) != len(modules):
        raise ValueError("module_count differs from actual modules array")
    result = {"schema": "chen-ledger-package-index-v1",
              "projection_only": True,
              "complete_ledger_relative_path": "module-ledger.json",
              "complete_ledger_sha256": original_sha256,
              "source_ledger_metadata": selected(ledger, (
                  "schema", "snapshot_started_utc", "snapshot_completed_utc",
                  "proof_baseline", "P0_first_document_commit", "manuscript_baseline",
                  "certificate_version", "module_count", "compile_status_counts",
                  "compiler_all_declaration_count", "source_theorem_head_count")),
              "accepted_integration": selected(ledger.get("accepted_integration", {}), (
                  "branch", "commit", "tree", "validated_new_production_modules",
                  "local_checkout_head", "local_checkout_matches_declared_sha",
                  "full_project_build_on_this_SHA_passed",
                  "full_project_kernel_and_axiom_gates_passed",
                  "final_hLower_hUpper_free_main_theorem_available")),
              "modules": []}
    for m in sorted(modules, key=lambda item: item["module"]):
        v = m.get("validation", {})
        result["modules"].append({
            **selected(m, ("module", "path", "part_owner", "source_part", "receiving_parts",
                            "outstanding_validation_gates")),
            "source_original": selected(m.get("source_original", {}),
                                        ("commit", "based_on_commit", "sha256", "git_blob_sha1")),
            "current_source": selected(m.get("current_source", {}),
                                       ("source_fixed_commit", "based_on_fixed_commit",
                                        "source_sha256", "git_blob_sha1")),
            "compile": selected(v.get("compile", {}), ("status", "stock_lean_cli_or_full_lake_build")),
            "kernel_replay": selected(v.get("kernel_replay", {}), ("status", "scope")),
            "axioms": selected(v.get("axioms", {}), (
                "status", "owned_declaration_count", "actual_axiom_union",
                "new_axiom_declarations", "unsafe_owned_declarations", "scope")),
            "type_counts": selected(m.get("types", {}), (
                "source_extracted_count", "compiler_printed_count", "compiler_all_declaration_count")),
            "integration_acceptance": selected(m.get("integration_acceptance", {}),
                                                ("accepted", "declared_by_input", "commit",
                                                 "declared_source_hash_matches", "meaning"))})
    return result


def tar_info(name, *, directory=False, size=0, mode=0o644):
    info = tarfile.TarInfo(name + "/" if directory else name)
    info.type = tarfile.DIRTYPE if directory else tarfile.REGTYPE
    info.size = 0 if directory else size
    info.mode = 0o755 if directory else mode
    info.uid = info.gid = 0
    info.uname = info.gname = ""
    info.mtime = 0
    return info


def create_archive(source, archive_root, before, destination):
    with Path(destination).open("wb") as output:
        with gzip.GzipFile(filename="", mode="wb", compresslevel=9, mtime=0, fileobj=output) as gz:
            with tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT) as tar:
                tar.addfile(tar_info(archive_root, directory=True))
                for rel in before["directories"]:
                    tar.addfile(tar_info(archive_root + "/" + rel, directory=True))
                for entry in before["files"]:
                    data = (source / entry["path"]).read_bytes()
                    if len(data) != entry["bytes"] or sha256(data) != entry["sha256"]:
                        raise ValueError("input changed while packaging: " + entry["path"])
                    tar.addfile(tar_info(archive_root + "/" + entry["path"],
                                         size=len(data), mode=entry["mode"]), io.BytesIO(data))


UNPACK_SOURCE = r'''#!/usr/bin/env python3
"""Restore and verify this ledger package using the Python standard library."""
import argparse
import base64
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        for b in iter(lambda: f.read(1024 * 1024), b""):
            h.update(b)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--destination", type=Path, default=Path.cwd())
    args = ap.parse_args()
    package = Path(__file__).resolve().parent
    manifest_file = package / "package-manifest.json"
    expected_manifest = (package / "package-manifest.json.sha256").read_text(encoding="utf-8").split()[0]
    if digest(manifest_file) != expected_manifest:
        raise ValueError("package manifest SHA256 mismatch")
    manifest = json.loads(manifest_file.read_text(encoding="utf-8"))
    if manifest["schema"] != "chen-ledger-package-v1":
        raise ValueError("unsupported package schema")
    archive = manifest["archive"]
    encoded = package / archive["base64_file"]
    if encoded.name != archive["base64_file"] or digest(encoded) != archive["base64_sha256"]:
        raise ValueError("base64 archive filename/hash mismatch")
    root_name = archive["root"]
    if PurePosixPath(root_name).parts != (root_name,) or root_name in (".", ".."):
        raise ValueError("invalid archive root")
    target = args.destination.resolve()
    target.mkdir(parents=True, exist_ok=True)
    final = target / root_name
    if final.exists() or final.is_symlink():
        raise FileExistsError("refusing to overwrite " + str(final))
    files = {entry["path"]: entry for entry in manifest["input_inventory"]["files"]}
    directories = set(manifest["input_inventory"]["directories"])
    with tempfile.TemporaryDirectory(prefix="ledger-restore-", dir=target) as temporary:
        temporary = Path(temporary)
        compressed = temporary / "input.tar.gz"
        with encoded.open("rb") as source, compressed.open("wb") as output:
            base64.decode(source, output)
        if (compressed.stat().st_size != archive["gzip_bytes"]
                or digest(compressed) != archive["gzip_sha256"]):
            raise ValueError("decoded gzip archive size/hash mismatch")
        restored = temporary / root_name
        restored.mkdir()
        seen_files, seen_dirs = set(), set()
        seen_members = set()
        with tarfile.open(compressed, "r:gz") as tar:
            for member in tar:
                path = PurePosixPath(member.name)
                if (path.is_absolute() or ".." in path.parts or "\\" in member.name
                        or not path.parts or path.parts[0] != root_name
                        or member.name in seen_members):
                    raise ValueError("unsafe/duplicate archive member " + member.name)
                seen_members.add(member.name)
                rel = PurePosixPath(*path.parts[1:]).as_posix()
                if len(path.parts) == 1:
                    if not member.isdir():
                        raise ValueError("archive root is not a directory")
                    continue
                destination = restored.joinpath(*path.parts[1:])
                if member.isdir():
                    if rel not in directories:
                        raise ValueError("unexpected directory " + rel)
                    destination.mkdir(parents=True, exist_ok=True)
                    seen_dirs.add(rel)
                elif member.isfile() and rel in files:
                    expected = files[rel]
                    if member.size != expected["bytes"]:
                        raise ValueError("member size mismatch " + rel)
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    with tar.extractfile(member) as source, destination.open("xb") as output:
                        shutil.copyfileobj(source, output, 1024 * 1024)
                    if digest(destination) != expected["sha256"]:
                        raise ValueError("restored file SHA256 mismatch " + rel)
                    destination.chmod(expected["mode"])
                    seen_files.add(rel)
                else:
                    raise ValueError("unexpected/nonregular archive member " + member.name)
        if seen_files != set(files) or seen_dirs != directories:
            raise ValueError("archive inventory is incomplete")
        if final.exists() or final.is_symlink():
            raise FileExistsError("destination appeared during restoration")
        restored.rename(final)
    print(json.dumps({"restored": str(final), "verified_files": len(files),
                      "gzip_sha256": archive["gzip_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
'''


def package(source, target, archive_root):
    source, target = source.resolve(), target.resolve()
    if not source.is_dir():
        raise ValueError("ledger output directory does not exist")
    if source == target or source in target.parents or target in source.parents:
        raise ValueError("input and output directories must not overlap")
    if target.exists() and (not target.is_dir() or any(target.iterdir())):
        raise ValueError("repo target must be absent or an empty directory")
    before = inventory(source)
    by_path = {e["path"]: e for e in before["files"]}
    for name in REQUIRED:
        if name not in by_path:
            raise ValueError("required frozen output missing: " + name)
    original_bytes = (source / "module-ledger.json").read_bytes()
    if sha256(original_bytes) != by_path["module-ledger.json"]["sha256"]:
        raise ValueError("module-ledger changed during inventory")
    ledger_index = build_index(json.loads(original_bytes), sha256(original_bytes))
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="ledger-package-", dir=target.parent) as work:
        work = Path(work)
        stage = work / "package"
        stage.mkdir()
        compressed = work / "complete-ledger.tar.gz"
        create_archive(source, archive_root, before, compressed)
        with compressed.open("rb") as src, (stage / ARCHIVE_FILE).open("wb") as dst:
            base64.encode(src, dst)
        for name in DIRECT_MARKDOWN:
            data = (source / name).read_bytes()
            if sha256(data) != by_path[name]["sha256"]:
                raise ValueError("readable file changed during packaging: " + name)
            (stage / name).write_bytes(data)
        (stage / "ledger-index.json").write_bytes(json_bytes(ledger_index))
        if "acceptance-input.json" in by_path:
            data = (source / "acceptance-input.json").read_bytes()
            if sha256(data) != by_path["acceptance-input.json"]["sha256"]:
                raise ValueError("acceptance input changed during packaging")
            (stage / "acceptance-input.json").write_bytes(data)
        (stage / "unpack_ledger.py").write_bytes(UNPACK_SOURCE.encode("utf-8"))
        direct = [{"path": p.name, "bytes": p.stat().st_size, "sha256": hash_file(p)}
                  for p in sorted(stage.iterdir()) if p.name != ARCHIVE_FILE]
        manifest = {
            "schema": SCHEMA,
            "source_directory_basename": source.name,
            "complete_original_module_ledger_sha256": sha256(original_bytes),
            "all_input_files_archived_without_rewriting": True,
            "input_inventory": before,
            "input_file_count": len(before["files"]),
            "input_total_bytes": sum(f["bytes"] for f in before["files"]),
            "archive": {"root": archive_root, "base64_file": ARCHIVE_FILE,
                        "base64_bytes": (stage / ARCHIVE_FILE).stat().st_size,
                        "base64_sha256": hash_file(stage / ARCHIVE_FILE),
                        "gzip_bytes": compressed.stat().st_size,
                        "gzip_sha256": hash_file(compressed),
                        "format": "POSIX PAX tar inside gzip, then MIME base64 (76 columns)",
                        "determinism": "Sorted paths; tar uid/gid/mtime=0 and empty owner names; "
                                       "normalized 0644/0755 file modes; gzip mtime=0, empty filename, level=9. "
                                       "Identical inputs/root and Python-zlib implementation produce identical bytes."},
            "direct_readable_and_index_files": direct,
            "index_scope": "Compact projection only. Every original JSON field, full type, source copy "
                           "and evidence file remains in the complete archive.",
            "verification_scope": "Packaging checks bytes and identities only; no Lean/kernel/axiom/CI gate is run."}
        manifest_bytes = json_bytes(manifest)
        (stage / "package-manifest.json").write_bytes(manifest_bytes)
        manifest_sha = sha256(manifest_bytes)
        (stage / "package-manifest.json.sha256").write_bytes((manifest_sha + "  package-manifest.json\n").encode("ascii"))
        readme = f"""# 冻结台账交接包

完整冻结输出保存在 `{ARCHIVE_FILE}`。其中包含原始 `module-ledger.json` 的全部字段和输入目录内全部文件；没有重写 JSON、删去类型或丢弃证据。归档内统一以相对目录 `{archive_root}/` 为根，不含外部绝对路径的归档成员。

三份主要 Markdown 已直接提供。`ledger-index.json` 是精简导航索引，并非完整台账替代品；完整类型及证据仍可从归档还原。Lean 源副本只留在完整归档原有目录内，没有复制到仓库默认生产根。

## 精确身份

- 原始 `module-ledger.json` SHA256：`{sha256(original_bytes)}`
- `package-manifest.json` SHA256：`{manifest_sha}`
- 解码后 gzip SHA256：`{manifest['archive']['gzip_sha256']}`
- base64 文本 SHA256：`{manifest['archive']['base64_sha256']}`
- 完整输入：{manifest['input_file_count']} 个文件，{manifest['input_total_bytes']} 字节。

`package-manifest.json` 列出每个原始相对路径、字节数、SHA256 和还原权限，以及直接可读文件/索引的哈希。`SHA256SUMS` 包含交接包所有其他文件的校验值。

## 还原

使用 Python 3.9 或更新版本的标准库。在本交接包目录中运行：

```bash
sha256sum -c SHA256SUMS
python3 unpack_ledger.py --destination /chosen/restore-directory
```

脚本先核对 manifest、base64 和 gzip 哈希，再按清单校验并还原每个文件到 `/chosen/restore-directory/{archive_root}/`。它拒绝覆盖已有同名目录，拒绝链接及越界归档成员。原始完整台账为 `{archive_root}/module-ledger.json`。

## 可复现与验证边界

归档按路径排序，规范化 tar 时间/所有者和权限，gzip 不写当前时间或来源文件名。相同输入内容、执行位、归档根目录名及 Python/zlib 实现产生相同归档。打包时前后重新核对输入清单；源目录变化则拒绝发布。

本工具只封装已冻结结果。它不运行 Lean、Lake、内核重放、公理审计或 Actions，不提升台账中的任何验证状态。
"""
        (stage / "PACKAGE_README.md").write_bytes(readme.encode("utf-8"))
        checksums = "".join(hash_file(p) + "  " + p.name + "\n" for p in sorted(stage.iterdir()))
        (stage / "SHA256SUMS").write_bytes(checksums.encode("utf-8"))
        if inventory(source) != before:
            raise ValueError("input directory changed; package was not published")
        if target.exists():
            if not target.is_dir() or any(target.iterdir()):
                raise ValueError("target became nonempty; package was not published")
            target.rmdir()
        stage.rename(target)
    return {"target": str(target), "input_files": manifest["input_file_count"],
            "gzip_bytes": manifest["archive"]["gzip_bytes"],
            "base64_bytes": manifest["archive"]["base64_bytes"],
            "manifest_sha256": manifest_sha,
            "archive_sha256": manifest["archive"]["gzip_sha256"],
            "Lean_started": False}


def self_check():
    """Small in-memory schema checks; do not read/package any actual ledger."""
    fixture = {"schema": "fixture", "module_count": 1,
               "accepted_integration": {"commit": "1" * 40,
                                        "full_project_build_on_this_SHA_passed": False},
               "modules": [{"module": "Example.Leaf", "path": "Example/Leaf.lean",
                            "current_source": {"source_sha256": "2" * 64},
                            "types": {"source_extracted_count": 1,
                                      "full_source_declaration_heads": ["DO_NOT_INLINE_TYPES"]},
                            "validation": {"compile": {"status": "NOT_RECORDED_CURRENT_SOURCE"}},
                            "integration_acceptance": {"accepted": False}}]}
    original = json_bytes(fixture)
    index = build_index(fixture, sha256(original))
    checks = []
    def check(name, condition):
        if not condition:
            raise AssertionError(name)
        checks.append(name)
    check("canonical JSON deterministic", json_bytes(index) == json_bytes(build_index(fixture, sha256(original))))
    check("input fields untouched", json_bytes(fixture) == original)
    check("large type arrays not duplicated in index", b"DO_NOT_INLINE_TYPES" not in json_bytes(index))
    check("false validation flags preserved", index["accepted_integration"]["full_project_build_on_this_SHA_passed"] is False
          and index["modules"][0]["integration_acceptance"]["accepted"] is False)
    check("relative member accepted", str(safe_relative("evidence/logs/sample.log")) == "evidence/logs/sample.log")
    for bad in ("../outside", "/absolute", "a/../b", "a\\b", "", ".", "a//b"):
        try:
            safe_relative(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("unsafe relative path accepted: " + repr(bad))
    checks.append("unsafe relative members rejected")
    info = tar_info("ledger/file.json", size=42)
    check("tar metadata normalized", info.uid == info.gid == info.mtime == 0 and info.mode == 0o644)
    ast.parse(UNPACK_SOURCE)
    checks.append("standalone unpacker syntax")
    return {"schema": SCHEMA, "checks_passed": checks, "actual_ledger_read": False,
            "actual_package_created": False, "writes": 0, "Lean_started": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("ledger_output_dir", type=Path, nargs="?")
    parser.add_argument("repo_target_dir", type=Path, nargs="?")
    parser.add_argument("--archive-root", help="safe relative root; defaults to input directory basename")
    parser.add_argument("--self-check", action="store_true", help="in-memory schema checks only")
    args = parser.parse_args()
    if args.self_check:
        if args.ledger_output_dir or args.repo_target_dir or args.archive_root:
            parser.error("--self-check must not be combined with packaging arguments")
        result = self_check()
    else:
        if args.ledger_output_dir is None or args.repo_target_dir is None:
            parser.error("both frozen ledger output directory and explicit repo target directory are required")
        archive_root = validate_archive_root(args.archive_root or args.ledger_output_dir.resolve().name)
        result = package(args.ledger_output_dir, args.repo_target_dir, archive_root)
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
