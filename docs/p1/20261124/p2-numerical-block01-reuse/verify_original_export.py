#!/usr/bin/env python3
"""Losslessly repackage an existing private-evidence export, without running Lean.

Only verified project source payloads can become SHA/size-bound repository
references. All other original members, including complete audit types and
logs, remain byte-for-byte present. Original gzip packages are never changed.
Run `verify` against the publication repository after downloading the xz file.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import io
import json
import math
from pathlib import Path, PurePosixPath
import subprocess
import tarfile


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def file_sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def encoded(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n").encode()


def safe_name(name: str) -> str:
    path = PurePosixPath(name)
    require(name and not path.is_absolute() and ".." not in path.parts
            and str(path) == name and "\\" not in name and "\x00" not in name,
            "Unsafe relative name: " + name)
    return name


def repo_source(name: str) -> bool:
    safe_name(name)
    return name.endswith(".lean") and name.startswith(("ImbalancedChen/", "docs/source-only/"))


def write_new(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)


def path_info(path: Path) -> dict:
    size = path.stat().st_size
    return {"path": str(path), "bytes": size, "sha256": file_sha(path)}


def catalog(repo: Path, output: Path) -> dict:
    repo = repo.resolve()
    top = subprocess.check_output(["git", "rev-parse", "--show-toplevel"], cwd=repo, text=True).strip()
    require(Path(top).resolve() == repo, "Expected the repository root")
    head = subprocess.run(["git", "rev-parse", "--verify", "HEAD"], cwd=repo, capture_output=True, text=True)
    paths = subprocess.check_output(["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z",
                                     "--", "ImbalancedChen", "docs/source-only"], cwd=repo).split(b"\0")
    blobs = {}
    for raw_path in sorted(set(paths)):
        if not raw_path:
            continue
        name = raw_path.decode()
        path = repo / name
        if not repo_source(name) or not path.is_file() or path.is_symlink():
            continue
        require(path.resolve().is_relative_to(repo), "Source resolves outside repository")
        raw = path.read_bytes()
        key = sha(raw)
        item = blobs.setdefault(key, {"sha256": key, "bytes": len(raw), "repository_paths": []})
        require(item["bytes"] == len(raw), "Source hash/size collision")
        item["repository_paths"].append(name)
    result = {"catalog_schema": 1, "repository": str(repo),
              "git_head_at_capture": head.stdout.strip() if head.returncode == 0 else None,
              "created_utc": datetime.now(timezone.utc).isoformat(), "blobs": blobs,
              "boundary": "Working-tree source bytes; uncommitted files may be included. Verify references against the publication repository or final Git tree before release."}
    write_new(output, encoded(result))
    return dict(path_info(output), unique_source_blobs=len(blobs),
                repository_paths=sum(len(item["repository_paths"]) for item in blobs.values()))


class Export:
    def __init__(self, directory: Path, expected_manifest: str | None) -> None:
        self.directory = directory.resolve()
        self.path = self.directory / "manifest.json"
        self.raw = self.path.read_bytes()
        require(expected_manifest is None or sha(self.raw) == expected_manifest, "Original manifest SHA mismatch")
        self.manifest = json.loads(self.raw)
        require(self.manifest.get("export_schema") == 1, "Unsupported original export schema")
        self.packages = self.manifest["packages"]
        names = [Path(item["path"]).name for item in self.packages]
        require(len(names) == len(set(names)), "Original package basenames are not unique")
        require(all(name.endswith(".tar.gz") and safe_name(name) for name in names), "Unexpected package name")

    def walk(self, visit) -> None:
        covered = set()
        for package in self.packages:
            label = Path(package["path"]).name
            path = self.directory / label
            require(path.stat().st_size == package["bytes"] and file_sha(path) == package["sha256"],
                    "Original package hash/size mismatch: " + label)
            seen = set()
            index = None
            with tarfile.open(path, "r|gz") as archive:
                for member in archive:
                    name = safe_name(member.name)
                    require(member.isfile() and name not in seen and ".olean" not in PurePosixPath(name).suffixes,
                            "Unexpected/duplicate/non-text archive member: " + name)
                    seen.add(name)
                    stream = archive.extractfile(member)
                    require(stream is not None, "Missing payload: " + name)
                    raw = stream.read()
                    require(len(raw) == member.size, "Truncated member: " + name)
                    if name == "PACKAGE_MANIFEST.json":
                        require(index is None and len(seen) == 1, "Package manifest must be first and unique")
                        index = json.loads(raw)
                        require(index["package"] == label and index["modules"] == package["modules"],
                                "Original package manifest disagrees with export metadata")
                        for item_name, item in index["files"].items():
                            require(self.manifest["files"].get(item_name) == item,
                                    "Original package/export file map mismatch: " + item_name)
                        info = {"sha256": sha(raw), "bytes": len(raw), "origin": str(path) + "!" + name,
                                "role": "unchanged original package manifest"}
                    else:
                        require(index is not None and name in index["files"], "Unlisted member: " + name)
                        info = index["files"][name]
                        require(info["bytes"] == len(raw) and info["sha256"] == sha(raw), "Member hash/size mismatch: " + name)
                        covered.add(name)
                    visit(label, name, raw, info)
            require(index is not None and seen == set(index["files"]) | {"PACKAGE_MANIFEST.json"},
                    "Missing original package members: " + label)
            require(file_sha(path) == package["sha256"], "Original package changed during reading: " + label)
        require(covered == set(self.manifest["files"]), "Original export file inventory is incomplete")
        require(file_sha(self.path) == sha(self.raw), "Original export manifest changed during reading")


def inventory(export: Export, output: Path) -> dict:
    files, sizes = {}, Counter()

    def visit(package, name, raw, info):
        files[package + "/" + name] = info
        sizes["project_sources" if name.startswith("sources/") and info["role"] == "verified project source" else "other_evidence"] += len(raw)

    export.walk(visit)
    result = {"inventory_schema": 1, "original_manifest": str(export.path), "manifest_sha256": sha(export.raw),
              "packages": export.packages, "members": files, "uncompressed_bytes": dict(sizes),
              "accepted_module_count": export.manifest["accepted_module_count"],
              "owned_declaration_count": export.manifest["owned_declaration_count"]}
    write_new(output, encoded(result))
    return dict(path_info(output), members=len(files), uncompressed_bytes=dict(sizes), packages=export.packages)


def add_member(archive, name: str, raw: bytes) -> None:
    info = tarfile.TarInfo(safe_name(name))
    info.size, info.mode, info.mtime = len(raw), 0o644, 0
    archive.addfile(info, io.BytesIO(raw))


def repack(export: Export, catalog_path: Path, output: Path, preset: int) -> dict:
    require(not output.exists(), "Do not overwrite an existing package")
    catalog_raw = catalog_path.read_bytes()
    source_catalog = json.loads(catalog_raw)
    require(source_catalog.get("catalog_schema") == 1, "Unsupported repository source catalog")
    for key, item in source_catalog["blobs"].items():
        require(item["sha256"] == key and item["repository_paths"] and all(repo_source(name) for name in item["repository_paths"]),
                "Invalid repository source catalog entry")
    script_raw = Path(__file__).read_bytes()
    references, embedded = {}, {}
    omitted_bytes = 0
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + ".partial")
    require(not temporary.exists(), "Temporary output already exists")
    try:
        with temporary.open("xb") as raw_output:
            with tarfile.open(fileobj=raw_output, mode="w:xz", preset=preset) as archive:
                def keep(name, raw, info):
                    add_member(archive, name, raw)
                    embedded[name] = dict(info, sha256=sha(raw), bytes=len(raw))

                keep("ORIGINAL_EXPORT_MANIFEST.json", export.raw, {"origin": str(export.path), "role": "unchanged original export manifest"})
                keep("REPOSITORY_SOURCE_CATALOG.json", catalog_raw, {"origin": str(catalog_path), "role": "publication repository source catalog"})
                keep("REPACK_IMPLEMENTATION.py", script_raw, {"origin": str(Path(__file__).resolve()), "role": "exact packaging implementation"})

                def visit(package, name, raw, info):
                    nonlocal omitted_bytes
                    destination = "packages/" + package + "/" + name
                    match = source_catalog["blobs"].get(info["sha256"])
                    if (name.startswith("sources/") and info["role"] == "verified project source"
                            and match is not None and match["bytes"] == len(raw)):
                        references[destination] = dict(info, original_package=package, original_member=name,
                                                       repository_paths=match["repository_paths"])
                        omitted_bytes += len(raw)
                    else:
                        keep(destination, raw, info)

                export.walk(visit)
                manifest = {
                    "slim_schema": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
                    "original_manifest_path": str(export.path), "original_manifest_sha256": sha(export.raw),
                    "original_packages": export.packages, "source_catalog_sha256": sha(catalog_raw),
                    "repack_implementation_sha256": sha(script_raw), "embedded": embedded,
                    "source_references": references, "source_payload_bytes_omitted": omitted_bytes,
                    "accepted_module_count": export.manifest["accepted_module_count"],
                    "owned_declaration_count": export.manifest["owned_declaration_count"],
                    "coverage": export.manifest["coverage"], "full_p2_complete": False,
                    "boundary": "Packaging only; acceptance counts are copied unchanged from the original verified export. Every original non-source member is retained. Source references require final repository verification; no Lean task was run."}
                add_member(archive, "SLIM_MANIFEST.json", encoded(manifest))
        require(file_sha(catalog_path) == sha(catalog_raw), "Source catalog changed during repack")
        temporary.replace(output)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise
    size = output.stat().st_size
    return dict(path_info(output), source_references=len(references), source_payload_bytes_omitted=omitted_bytes,
                embedded_members=len(embedded), base64_bytes=4 * math.ceil(size / 3),
                suggested_raw_page_bytes=1000000, suggested_page_count=math.ceil(size / 1000000),
                original_manifest_sha256=sha(export.raw), accepted_module_count=manifest["accepted_module_count"],
                owned_declaration_count=manifest["owned_declaration_count"], full_p2_complete=False)


def verify(path: Path, repo: Path, git_tree: str | None, output: Path | None) -> dict:
    seen, contents, slim = {}, {}, None
    with tarfile.open(path, "r|xz") as archive:
        for member in archive:
            name = safe_name(member.name)
            require(member.isfile() and name not in seen, "Unexpected/duplicate slim member")
            raw = archive.extractfile(member).read()
            seen[name] = {"sha256": sha(raw), "bytes": len(raw)}
            if name == "SLIM_MANIFEST.json":
                slim = json.loads(raw)
            elif name.endswith("PACKAGE_MANIFEST.json") or name in ("ORIGINAL_EXPORT_MANIFEST.json", "REPOSITORY_SOURCE_CATALOG.json"):
                contents[name] = json.loads(raw)
    require(slim is not None and slim["slim_schema"] == 1, "Missing slim manifest")
    require(set(seen) == set(slim["embedded"]) | {"SLIM_MANIFEST.json"}, "Slim member inventory differs")
    for name, item in slim["embedded"].items():
        require(all(seen[name][key] == item[key] for key in ("sha256", "bytes")), "Embedded evidence changed: " + name)
    original = contents["ORIGINAL_EXPORT_MANIFEST.json"]
    source_catalog = contents["REPOSITORY_SOURCE_CATALOG.json"]
    require(seen["ORIGINAL_EXPORT_MANIFEST.json"]["sha256"] == slim["original_manifest_sha256"]
            and seen["REPOSITORY_SOURCE_CATALOG.json"]["sha256"] == slim["source_catalog_sha256"]
            and seen["REPACK_IMPLEMENTATION.py"]["sha256"] == slim["repack_implementation_sha256"]
            and original["packages"] == slim["original_packages"], "Slim/original provenance binding differs")
    require(all(slim[key] == original[key] for key in ("accepted_module_count", "owned_declaration_count", "coverage")),
            "Repack changed original acceptance metadata")
    expected, covered = set(), set()
    for package in original["packages"]:
        label = Path(package["path"]).name
        prefix = "packages/" + label + "/"
        index_name = prefix + "PACKAGE_MANIFEST.json"
        index = contents[index_name]
        require(index["package"] == label and index["modules"] == package["modules"], "Package provenance differs")
        expected.add(index_name)
        for name, item in index["files"].items():
            require(original["files"].get(name) == item, "Original source/file maps disagree")
            key = prefix + safe_name(name)
            expected.add(key)
            covered.add(name)
            if key in slim["source_references"]:
                ref = slim["source_references"][key]
                require(key not in seen and name.startswith("sources/") and item["role"] == "verified project source"
                        and all(ref[field] == item[field] for field in item)
                        and ref["original_package"] == label and ref["original_member"] == name,
                        "Only unchanged project-source payloads may be omitted")
            else:
                require(key in seen and all(seen[key][field] == item[field] for field in ("sha256", "bytes")),
                        "An original evidence member is missing or changed: " + key)
    require(covered == set(original["files"]) and expected == {name for name in seen if name.startswith("packages/")} | set(slim["source_references"]),
            "Original member coverage differs")
    repo = repo.resolve()
    revision = None
    if git_tree:
        revision = subprocess.check_output(["git", "rev-parse", "--verify", git_tree + "^{tree}"], cwd=repo, text=True).strip()
    verified = {}
    for name, ref in slim["source_references"].items():
        blob = source_catalog["blobs"][ref["sha256"]]
        require(blob["bytes"] == ref["bytes"] and blob["repository_paths"] == ref["repository_paths"], "Source reference/catalog mismatch")
        matches = []
        for relative in ref["repository_paths"]:
            require(repo_source(relative), "Source reference is outside approved repository directories")
            if revision:
                command = subprocess.run(["git", "show", revision + ":" + relative], cwd=repo, capture_output=True)
                raw = command.stdout if command.returncode == 0 else None
            else:
                candidate = repo / relative
                require(candidate.resolve().is_relative_to(repo), "Repository source escapes worktree")
                raw = candidate.read_bytes() if candidate.is_file() and not candidate.is_symlink() else None
            if raw is not None and len(raw) == ref["bytes"] and sha(raw) == ref["sha256"]:
                matches.append(relative)
        require(matches, "No exact publication-repository source remains for " + name)
        verified[name] = {"sha256": ref["sha256"], "bytes": ref["bytes"], "matched_repository_paths": matches}
    report = {"verification_schema": 1, "archive": path_info(path), "repository": str(repo), "git_tree": revision,
              "verified_source_references": len(verified), "source_references": verified,
              "verified_original_members": len(expected), "accepted_module_count": slim["accepted_module_count"],
              "owned_declaration_count": slim["owned_declaration_count"], "full_p2_complete": False,
              "boundary": "Byte-preservation and source-availability verification only; no Lean compilation, replay or new proof credit."}
    if output:
        write_new(output, encoded(report))
    return {key: value for key, value in report.items() if key != "source_references"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    cat = commands.add_parser("catalog", help="Run locally in the publication repository")
    cat.add_argument("--repo", type=Path, default=Path.cwd())
    cat.add_argument("--output", type=Path, required=True)
    inv = commands.add_parser("inventory", help="Read original packages and print compact inventory metadata")
    rep = commands.add_parser("repack", help="Read original packages and write a separate lossless xz package")
    for sub in (inv, rep):
        sub.add_argument("export_directory", type=Path)
        sub.add_argument("--manifest-sha256")
        sub.add_argument("--output", type=Path, required=True)
    rep.add_argument("--catalog", type=Path, required=True)
    rep.add_argument("--preset", type=int, choices=range(10), default=6)
    check = commands.add_parser("verify", help="Verify downloaded payloads and final repository source references")
    check.add_argument("archive", type=Path)
    check.add_argument("--repo", type=Path, default=Path.cwd())
    check.add_argument("--git-tree", help="Use a committed Git tree instead of working-tree files")
    check.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.command == "catalog":
        result = catalog(args.repo, args.output)
    elif args.command == "verify":
        result = verify(args.archive, args.repo, args.git_tree, args.output)
    else:
        source = Export(args.export_directory, args.manifest_sha256)
        result = inventory(source, args.output) if args.command == "inventory" else repack(source, args.catalog, args.output, args.preset)
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
