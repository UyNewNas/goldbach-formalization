#!/usr/bin/env python3
"""P2.7-only lossless text-evidence delta; no compilation, replay or proof credit.

The original exporter remains authoritative. Only its exact project sources
and already published native-context bytes may become references. The receiver
hashes the actual fixed Git parts and every old archive member in one streaming
pass, without unpacking the 4.3 GB donor to disk. New audits stay embedded.
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import lzma
import math
import os
from pathlib import Path
import subprocess
import tarfile

import repack_winner9_private_evidence as original
from repack_winner9_private_evidence import require, safe_name, sha, encoded


SCHEMA = "p27-text-evidence-delta-v1"
FINAL_MODULE = "ImbalancedChen.P2PairedCertificateCompletion"
CHUNK = 1024 * 1024
SCOPE_DIR = Path(__file__).resolve().parents[2] / "docs/p2/20261125/p27"
SCOPE_HASHES = {
    "audit-targets.txt": "df8c1c35a7829476f95eb84212626270b5d68e25126d34704848f80b653e0cdf",
    "project-closure.json": "2499c7d548c8d4bb0dcb327bd6139e0034240a7bb1ef0577215627589179a514",
}
PRIOR = {
    "history_commit": "77db7b4250077ba9bd2cafb14dfa51b5a2e6e549",
    "index_path": "docs/verification/20261125-p2-resume/MAIN_ARCHIVE_PARTS.json",
    "index_sha256": "f6e9c37881bf6055aaea3e420d32aa9c8b0c539dcb192d573b6bbc2733e58f47",
    "index_bytes": 15727,
    "archive_sha256": "92c1067a1694ea74af4d15ee841199ab72094f2147b7651e77cf21f60e68faf4",
    "archive_bytes": 44304524,
    "part_count": 37,
    "slim_manifest_sha256": "be5d5b57751756fa1d1b443a9f4a7cb00fab80accae41ee2c31ca401bc955bb7",
    "original_manifest_sha256": "81ebdb646b96d21bd6cc8c0c4da79d5915896e9a1506adb26b53f115bdb07bc9",
}
CONTEXT_ARCHIVES = [
    {"path": "docs/p2/20261125/p27/native-inputs.tar.xz", "bytes": 1849264,
     "sha256": "25a5b45cf649c8b97df57e6a1dcac71c7f22d5ccd5ab2bf92eda399aeff9ffba",
     "git_blob_sha1": "d7f85b89e54a4f3e343ee8338a30e47c00bb035b"},
    {"path": "docs/p2/20261125/p27/currentchen-inputs.tar.xz", "bytes": 330520,
     "sha256": "7308d5b143841734f94b95c7d4499f71110a206ffacf4374f101ef8633ab04eb",
     "git_blob_sha1": "902aeebb599e5ac7e7f870d886ac581b5c55fea2"},
]
TEXT_SUFFIXES = {".json", ".jsonl", ".log", ".txt", ".md", ".lean", ".py", ".patch"}
_STAGING = "original-metadata/ImbalancedChen.CurrentChenBuchstabRefinement/.lake/build/"
_CURRENTCHEN = "ImbalancedChen/CurrentChenBuchstabRefinement"
CURRENTCHEN_STAGING = {
    _STAGING + "lib/lean/" + _CURRENTCHEN + suffix: {"sha256": digest, "bytes": size}
    for suffix, digest, size in (
        (".olean", "4eb6075c0bcda6ee6d8773fa93c97347b3d727146c944315c1f0d89de498f652", 570136),
        (".olean.hash", "64e793af61b1ea917eb8e89998e2b26737577aef66dcca6f6d67714a7b90b17c", 16),
        (".ilean", "241cadafa97bf9807bafd6c76d12bb7e7990a807ebb88c0cfb22e6b3094d722e", 16004),
        (".ilean.hash", "24d309f81c1a9ffd3aa3ab38bef9d72c0e4edf682645b07aa7cdb58f938d0a08", 16),
        (".trace", "2ce3d7230b7bf383610f42847fbd29ddac3125a91ee32d40090d687ba99ff969", 3690),
    )
}
CURRENTCHEN_STAGING.update({
    _STAGING + "ir/" + _CURRENTCHEN + suffix: {"sha256": digest, "bytes": size}
    for suffix, digest, size in (
        (".c", "aef2e9b10398a0f5bbb28a6e8a19ed538f61d4aefc2ac736e953393ca4c40947", 2699),
        (".c.hash", "490804ff1c4bea3119307b8e2fb42f311c5570da7a7db3910c2533379d9d6b5e", 16),
        (".setup.json", "ee18d92f20b1426a098f2e4bb4a29dfeed27a90d3e9db111a649438ef6ad844a", 2278499),
    )
})
STAGING_DIRECTORIES = {p.as_posix() for name in CURRENTCHEN_STAGING for p in Path(name).parents if str(p) != "."}


def scope_bytes() -> tuple[bytes, bytes]:
    values = []
    for name, expected in SCOPE_HASHES.items():
        raw = (SCOPE_DIR / name).read_bytes()
        require(sha(raw) == expected, "P2.7 fixed scope changed: " + name)
        values.append(raw)
    return tuple(values)


def check_scope(manifest: dict, targets_raw: bytes, closure_raw: bytes) -> None:
    require(sha(targets_raw) == SCOPE_HASHES["audit-targets.txt"]
            and sha(closure_raw) == SCOPE_HASHES["project-closure.json"], "P2.7 scope byte mismatch")
    targets, closure = targets_raw.decode().splitlines(), json.loads(closure_raw)
    require(len(targets) == len(set(targets)) == 26 and manifest["accepted_module_count"] == 26
            and set(manifest["accepted_modules"]) == set(targets), "Exactly the 26 P2.7 audit targets must be accepted")
    require(manifest["unselected_modules"] == [] and manifest["duplicate_owned_declarations"] == {}
            and manifest["owned_declaration_count"] == manifest["unique_owned_declaration_count"],
            "Unselected or duplicate owned declarations remain")
    require(len(closure) == 81 and FINAL_MODULE in closure
            and set(manifest["object_manifest"]) == set(closure), "The exact 81-module project closure is required")
    union = set()
    for row in manifest["accepted_modules"].values():
        require(set(row["project_modules"]) <= set(closure), "Audit has an unexpected project dependency")
        union.update(row["project_modules"])
    require(union == set(closure), "Audit contexts do not cover the 81-module closure")
    # Winner9 coverage and full_p2_complete are original metadata, not P2.7 gates.


def prior_identity() -> dict:
    return dict(PRIOR)


def git_tree(repo: Path, value: str) -> str:
    return subprocess.check_output(["git", "rev-parse", "--verify", value + "^{tree}"],
                                   cwd=repo, text=True).strip()


def git_bytes(repo: Path, tree: str, name: str) -> bytes:
    safe_name(name)
    return subprocess.check_output(["git", "show", tree + ":" + name], cwd=repo)


def git_sha(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


class GitParts(io.RawIOBase):
    """Read only fixed-index Git blobs, keeping at most one compressed part."""
    def __init__(self, repo: Path, tree: str):
        self.repo, self.tree = repo, tree
        raw = git_bytes(repo, tree, PRIOR["index_path"])
        require(len(raw) == PRIOR["index_bytes"] and sha(raw) == PRIOR["index_sha256"], "Prior parts index differs")
        index = json.loads(raw)
        self.parts = index["parts"]
        require(index["schema"] == "p2-main-evidence-raw-parts/v1"
                and index["part_count"] == len(self.parts) == PRIOR["part_count"]
                and index["full_archive"]["bytes"] == PRIOR["archive_bytes"]
                and index["full_archive"]["sha256"] == PRIOR["archive_sha256"], "Prior archive/index identity differs")
        self.number, self.position, self.count = 0, 0, 0
        self.buffer, self.digest = b"", hashlib.sha256()

    def readable(self):
        return True

    def readinto(self, destination):
        if self.position == len(self.buffer):
            if self.number == len(self.parts):
                return 0
            row = self.parts[self.number]
            require(row["index"] == self.number, "Prior part order differs")
            self.buffer = git_bytes(self.repo, self.tree, row["path"])
            require(len(self.buffer) == row["bytes"] and sha(self.buffer) == row["sha256"]
                    and git_sha(self.buffer) == row["git_blob_sha"], "Prior part bytes/blob differ: " + row["path"])
            self.position = 0
            self.number += 1
        size = min(len(destination), len(self.buffer) - self.position)
        raw = self.buffer[self.position:self.position + size]
        destination[:size] = raw
        self.position += size
        self.count += size
        self.digest.update(raw)
        return size

    def complete(self):
        require(self.number == len(self.parts) and self.position == len(self.buffer)
                and self.count == PRIOR["archive_bytes"]
                and self.digest.hexdigest() == PRIOR["archive_sha256"], "Prior compressed stream was incomplete or changed")


def parse_prior_slim(raw: bytes) -> dict:
    require(sha(raw) == PRIOR["slim_manifest_sha256"], "Original prior SLIM catalog SHA differs")
    slim = json.loads(raw)
    require(slim["slim_schema"] == 1 and slim["original_manifest_sha256"] == PRIOR["original_manifest_sha256"],
            "Original prior SLIM provenance differs")
    return slim


def scan_prior(repo: Path, tree: str) -> tuple[bytes, dict]:
    reader = GitParts(repo, tree)
    seen, slim_raw = {}, None
    compressed = io.BufferedReader(reader)
    with lzma.LZMAFile(compressed, "rb") as decoded:
        with tarfile.open(fileobj=decoded, mode="r|", bufsize=CHUNK) as archive:
            for member in archive:
                name = safe_name(member.name)
                require(member.isfile() and name not in seen, "Invalid/duplicate prior archive member")
                digest, size, capture = hashlib.sha256(), 0, []
                stream = archive.extractfile(member)
                require(stream is not None, "Missing prior member payload")
                while raw := stream.read(CHUNK):
                    digest.update(raw)
                    size += len(raw)
                    if name == "SLIM_MANIFEST.json":
                        require(size <= 64 * CHUNK, "Prior SLIM catalog is unexpectedly large")
                        capture.append(raw)
                require(size == member.size, "Truncated prior member")
                seen[name] = {"sha256": digest.hexdigest(), "bytes": size}
                if name == "SLIM_MANIFEST.json":
                    slim_raw = b"".join(capture)
        # Tar stops at its end marker before the underlying xz stream need end.
        while decoded.read(CHUNK):
            pass
    while compressed.read(CHUNK):
        pass
    reader.complete()
    require(slim_raw is not None, "Missing original prior SLIM manifest")
    slim = parse_prior_slim(slim_raw)
    require(set(seen) == set(slim["embedded"]) | {"SLIM_MANIFEST.json"}, "Prior member inventory differs")
    for name, item in slim["embedded"].items():
        require(all(seen[name][key] == item[key] for key in ("sha256", "bytes")),
                "Actual prior member hash/size differs: " + name)
    require(seen["ORIGINAL_EXPORT_MANIFEST.json"]["sha256"] == PRIOR["original_manifest_sha256"],
            "Prior original export manifest changed")
    return slim_raw, seen


def publish(path: Path, raw: bytes) -> None:
    require(not os.path.lexists(path), "Output already exists")
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".partial")
    require(not os.path.lexists(temporary), "Partial output already exists")
    try:
        with temporary.open("xb") as output:
            output.write(raw)
        os.link(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def catalog(repo: Path, tree: str, output: Path) -> dict:
    revision = git_tree(repo, tree)
    raw, seen = scan_prior(repo, revision)
    publish(output, lzma.compress(raw, preset=6))
    return {**original.path_info(output), "original_slim_sha256": sha(raw), "git_tree_read": revision,
            "verified_prior_members": len(seen), "proof_credit": False}


def source_catalog(raw: bytes) -> dict:
    value = json.loads(raw)
    require(value.get("catalog_schema") == 1, "Unsupported repository source catalog")
    for key, row in value["blobs"].items():
        require(row["sha256"] == key and row["repository_paths"]
                and all(original.repo_source(p) for p in row["repository_paths"]), "Invalid source catalog entry")
    return value


def check_new_text(name: str, raw: bytes, manifest: dict, receipts: set, metadata: list, records: list) -> None:
    if name == "EXPORT_METADATA.json":
        require(json.loads(raw) == {k: v for k, v in manifest.items() if k not in {"files", "packages"}},
                "Original EXPORT_METADATA and export manifest differ")
        metadata.append(name)
    elif name == "context/selected-compile-records.json":
        require(set(json.loads(raw)) == set(manifest["object_manifest"]), "Selected compile records do not cover the 81 contexts")
        records.append(name)
    elif name.startswith("audits/") and name.endswith("/selected-receipt.json"):
        row = json.loads(raw)
        target = name[len("audits/"):-len("/selected-receipt.json")]
        require(target in manifest["accepted_modules"] and row.get("accepted") is True
                and row.get("module") == target, "Nonaccepted or unexpected original selected receipt")
        meta = manifest["accepted_modules"][target]
        require(sha(raw) == meta["receipt_sha256"]
                and all(row[k] == meta[k] for k in ("source_sha256", "object_sha256", "compile_closure_signature")),
                "Original selected receipt binding differs")
        require(target not in receipts, "Duplicate selected receipt")
        receipts.add(target)


def check_new_text_coverage(receipts, metadata, records, manifest):
    require(receipts == set(manifest["accepted_modules"]) and len(metadata) == len(records) == 1,
            "Missing selected receipts, original metadata, or 81-module compile context")


def supplemental_text_name(relative: str) -> bool:
    safe_name(relative)
    path = Path(relative)
    return (relative != "original-metadata" and not relative.startswith("original-metadata/")
            and path.suffix in TEXT_SUFFIXES and ".olean" not in path.suffixes)


def pack(export_directory: Path, source_catalog_path: Path, prior_catalog_path: Path,
         adoption: Path, output: Path, expected_manifest: str) -> dict:
    export = original.Export(export_directory, expected_manifest)
    targets_raw, closure_raw = scope_bytes()
    check_scope(export.manifest, targets_raw, closure_raw)
    catalog_raw = source_catalog_path.read_bytes()
    sources = source_catalog(catalog_raw)
    with lzma.open(prior_catalog_path, "rb") as stream:
        prior_raw = stream.read(64 * CHUNK + 1)
    prior = parse_prior_slim(prior_raw)
    matches = {}
    for name, row in sorted(prior["embedded"].items()):
        if name.startswith("packages/all.tar.gz/context/native/"):
            matches.setdefault((row["sha256"], row["bytes"]), name)
    require(adoption.is_dir() and not adoption.is_symlink(), "CurrentChen adoption directory must exist")
    require(not os.path.lexists(output), "Output already exists")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + ".partial")
    require(not os.path.lexists(temporary), "Partial output already exists")
    embedded, refs, source_refs, supplements, staging = {}, {}, {}, {}, {}
    receipts, metadata, records = set(), [], []
    try:
        with temporary.open("xb") as raw_output, tarfile.open(fileobj=raw_output, mode="w:xz", preset=6) as archive:
            def keep(name, raw, info):
                require(name not in embedded, "Duplicate delta member")
                original.add_member(archive, name, raw)
                embedded[name] = dict(info, sha256=sha(raw), bytes=len(raw))

            for name, raw in (("ORIGINAL_EXPORT_MANIFEST.json", export.raw), ("REPOSITORY_SOURCE_CATALOG.json", catalog_raw),
                              ("PRIOR_SLIM_MANIFEST.json", prior_raw), ("P27_AUDIT_TARGETS.txt", targets_raw),
                              ("P27_PROJECT_CLOSURE.json", closure_raw), ("P27_PACK_IMPLEMENTATION.py", Path(__file__).read_bytes())):
                keep(name, raw, {"role": "unchanged manifest, scope or implementation"})

            def visit(package, name, raw, info):
                key = "packages/" + package + "/" + name
                check_new_text(name, raw, export.manifest, receipts, metadata, records)
                source = sources["blobs"].get(info["sha256"])
                if (name.startswith("sources/") and info["role"] == "verified project source"
                        and source is not None and source["bytes"] == len(raw)):
                    source_refs[key] = dict(info, original_package=package, original_member=name,
                                            repository_paths=source["repository_paths"])
                elif name.startswith("context/native/") and (info["sha256"], len(raw)) in matches:
                    refs[key] = dict(info, archive_id="p2-resume-main", member=matches[(info["sha256"], len(raw))])
                else:
                    keep(key, raw, info)

            export.walk(visit)
            check_new_text_coverage(receipts, metadata, records, export.manifest)
            for path in sorted(adoption.rglob("*")):
                relative = safe_name(path.relative_to(adoption).as_posix())
                if path.is_symlink():
                    require(relative in CURRENTCHEN_STAGING, "Unknown CurrentChen staging/symlink")
                    identity = {"sha256": original.file_sha(path), "bytes": path.stat().st_size}
                    require(identity == CURRENTCHEN_STAGING[relative], "Known CurrentChen staging facet SHA/bytes differ")
                    staging[relative] = {"link_target": os.readlink(path), "transported": False,
                                         **identity,
                                         "reason": "Known metadata staging alias; original bytes remain in fixed repository input archives"}
                    continue
                require(relative not in CURRENTCHEN_STAGING, "Expected a known CurrentChen metadata staging symlink")
                if path.is_dir():
                    require(not relative.startswith("original-metadata") or relative in STAGING_DIRECTORIES,
                            "Unknown CurrentChen staging directory")
                    continue
                require(not relative.startswith("original-metadata/"), "Unknown CurrentChen staging payload")
                require(path.is_file() and supplemental_text_name(relative),
                        "Unexpected nontext CurrentChen supplemental file")
                key = "supplemental/currentchen-adoption/" + relative
                raw = path.read_bytes()
                info = {"origin": str(path.resolve()), "role": "CurrentChen adoption provenance; no acceptance credit"}
                keep(key, raw, info)
                supplements[key] = embedded[key]
            require(supplements, "CurrentChen adoption supplemental evidence is empty")
            require(not (adoption / "original-metadata").exists() or set(staging) == set(CURRENTCHEN_STAGING),
                    "Incomplete known CurrentChen metadata staging inventory")
            manifest = {"schema": SCHEMA, "original_manifest_sha256": sha(export.raw),
                        "original_packages": export.packages, "source_catalog_sha256": sha(catalog_raw),
                        "prior_archive": prior_identity(), "repository_context_archives": CONTEXT_ARCHIVES,
                        "embedded": embedded, "prior_references": refs, "source_references": source_refs,
                        "supplemental": supplements, "omitted_staging": staging,
                        "accepted_module_count": 26, "project_context_count": 81,
                        "owned_declaration_count": export.manifest["owned_declaration_count"],
                        "proof_credit": False, "boundary": "Byte transport only; original acceptance metadata is unchanged."}
            original.add_member(archive, "P27_DELTA_MANIFEST.json", encoded(manifest))
        require(source_catalog_path.read_bytes() == catalog_raw, "Source catalog changed during packing")
        require(original.file_sha(export.path) == sha(export.raw), "Original manifest changed during packing")
        os.link(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)
    size = output.stat().st_size
    return {**original.path_info(output), "original_manifest_sha256": sha(export.raw),
            "prior_references": len(refs), "source_references": len(source_refs), "supplemental_files": len(supplements),
            "omitted_staging_aliases": len(staging),
            "accepted_module_count": 26, "project_context_count": 81,
            "base64_bytes": 4 * math.ceil(size / 3), "raw_transfer_page_bytes": 1000000,
            "transfer_pages": math.ceil(size / 1000000), "proof_credit": False}


def verify(path: Path, repo: Path, tree: str, output: Path | None, expected_manifest: str) -> dict:
    revision = git_tree(repo, tree)
    before = original.path_info(path)
    seen, captured = {}, {}
    with tarfile.open(path, "r|xz") as archive:
        for member in archive:
            name = safe_name(member.name)
            require(member.isfile() and name not in seen, "Invalid/duplicate delta member")
            raw = archive.extractfile(member).read()
            require(len(raw) == member.size, "Truncated delta member")
            seen[name] = {"sha256": sha(raw), "bytes": len(raw)}
            if (name in {"P27_DELTA_MANIFEST.json", "ORIGINAL_EXPORT_MANIFEST.json", "REPOSITORY_SOURCE_CATALOG.json",
                         "PRIOR_SLIM_MANIFEST.json", "P27_AUDIT_TARGETS.txt", "P27_PROJECT_CLOSURE.json"}
                    or name.endswith(("/PACKAGE_MANIFEST.json", "/EXPORT_METADATA.json", "/selected-receipt.json",
                                      "/context/selected-compile-records.json"))):
                captured[name] = raw
    delta = json.loads(captured["P27_DELTA_MANIFEST.json"])
    require(delta["schema"] == SCHEMA and delta["proof_credit"] is False, "Wrong delta schema/credit")
    require(delta["prior_archive"] == prior_identity() and delta["repository_context_archives"] == CONTEXT_ARCHIVES,
            "Fixed prior/context archive identity changed")
    embedded, refs, source_refs = delta["embedded"], delta["prior_references"], delta["source_references"]
    sets = [set(embedded), set(refs), set(source_refs)]
    require(not (sets[0] & sets[1] or sets[0] & sets[2] or sets[1] & sets[2]), "Delta member classes overlap")
    require(set(seen) == set(embedded) | {"P27_DELTA_MANIFEST.json"}, "Extra or missing delta member")
    for name, row in embedded.items():
        require(all(seen[name][k] == row[k] for k in ("sha256", "bytes")), "Embedded member hash/size differs: " + name)
    original_raw = captured["ORIGINAL_EXPORT_MANIFEST.json"]
    require(sha(original_raw) == expected_manifest == delta["original_manifest_sha256"],
            "Original export manifest differs from the independent exporter SHA")
    manifest = json.loads(original_raw)
    require(manifest["export_schema"] == 1 and manifest["packages"] == delta["original_packages"], "Original package provenance differs")
    check_scope(manifest, captured["P27_AUDIT_TARGETS.txt"], captured["P27_PROJECT_CLOSURE.json"])
    require(delta["accepted_module_count"] == 26 and delta["project_context_count"] == 81
            and delta["owned_declaration_count"] == manifest["owned_declaration_count"], "Delta acceptance metadata differs")
    sources_raw = captured["REPOSITORY_SOURCE_CATALOG.json"]
    require(sha(sources_raw) == delta["source_catalog_sha256"], "Source catalog SHA differs")
    sources = source_catalog(sources_raw)
    prior = parse_prior_slim(captured["PRIOR_SLIM_MANIFEST.json"])
    expected, covered, receipts, metadata, records = set(), set(), set(), [], []
    labels = [Path(p["path"]).name for p in manifest["packages"]]
    require(len(labels) == len(set(labels)), "Duplicate original package basename")
    for package, label in zip(manifest["packages"], labels):
        safe_name(label)
        prefix = "packages/" + label + "/"
        index_name = prefix + "PACKAGE_MANIFEST.json"
        require(index_name in embedded, "Original package manifest must remain embedded")
        index = json.loads(captured[index_name])
        require(index["package"] == label and index["modules"] == package["modules"], "Package manifest identity differs")
        expected.add(index_name)
        for name, item in index["files"].items():
            require(manifest["files"].get(name) == item, "Original package/export file map differs")
            key = prefix + safe_name(name)
            expected.add(key)
            covered.add(name)
            require(sum(key in s for s in sets) == 1, "Original member coverage is not exact: " + key)
            row = embedded.get(key, refs.get(key, source_refs.get(key)))
            require(all(row[k] == v for k, v in item.items()), "Original member metadata changed: " + key)
            if key in refs:
                require(name.startswith("context/native/") and row["archive_id"] == "p2-resume-main"
                        and row["member"].startswith("packages/all.tar.gz/context/native/")
                        and row["member"] in prior["embedded"], "Invalid prior regular-member reference")
                require(all(prior["embedded"][row["member"]][k] == row[k] for k in ("sha256", "bytes")),
                        "Prior reference member hash/size differs")
            elif key in source_refs:
                require(name.startswith("sources/") and item["role"] == "verified project source"
                        and row["original_package"] == label and row["original_member"] == name,
                        "Only exact verified project sources can use repository references")
                match = sources["blobs"][row["sha256"]]
                require(match["bytes"] == row["bytes"] and match["repository_paths"] == row["repository_paths"],
                        "Source reference/catalog differs")
                valid = False
                for relative in row["repository_paths"]:
                    require(original.repo_source(relative), "Source reference path is not permitted")
                    try:
                        raw = git_bytes(repo, revision, relative)
                    except subprocess.CalledProcessError:
                        continue
                    valid |= len(raw) == row["bytes"] and sha(raw) == row["sha256"]
                require(valid, "No exact repository source in the selected Git tree: " + key)
            else:
                if key in captured:
                    check_new_text(name, captured[key], manifest, receipts, metadata, records)
    require(covered == set(manifest["files"])
            and expected == {n for s in sets for n in s if n.startswith("packages/")}, "Original member inventory/coverage differs")
    check_new_text_coverage(receipts, metadata, records, manifest)
    supplements = delta["supplemental"]
    supplemental_prefix = "supplemental/currentchen-adoption/"
    require(supplements and all(n.startswith(supplemental_prefix) and supplemental_text_name(n[len(supplemental_prefix):])
                               and embedded.get(n) == row
                               for n, row in supplements.items()), "Supplemental namespace/inventory differs")
    staging = delta["omitted_staging"]
    require((not staging or set(staging) == set(CURRENTCHEN_STAGING))
            and all(row["transported"] is False and isinstance(row["link_target"], str)
                    and all(row[k] == CURRENTCHEN_STAGING[name][k] for k in ("sha256", "bytes"))
                    for name, row in staging.items()),
            "Unknown or incomplete omitted CurrentChen staging inventory")
    headers = {"ORIGINAL_EXPORT_MANIFEST.json", "REPOSITORY_SOURCE_CATALOG.json", "PRIOR_SLIM_MANIFEST.json",
               "P27_AUDIT_TARGETS.txt", "P27_PROJECT_CLOSURE.json", "P27_PACK_IMPLEMENTATION.py"}
    require(set(embedded) == (expected - set(refs) - set(source_refs)) | headers | set(supplements)
            and set(refs) | set(source_refs) <= expected, "Extra delta members/references outside the original inventory")
    # Neither the prior catalog nor a claimed archive SHA substitutes for bytes.
    actual_prior_raw, actual = scan_prior(repo, revision)
    require(actual_prior_raw == captured["PRIOR_SLIM_MANIFEST.json"], "Actual prior catalog differs")
    for row in refs.values():
        require(row["member"] in actual and all(actual[row["member"]][k] == row[k] for k in ("sha256", "bytes")),
                "Referenced actual prior member is absent or changed")
    for item in CONTEXT_ARCHIVES:
        raw = git_bytes(repo, revision, item["path"])
        require(len(raw) == item["bytes"] and sha(raw) == item["sha256"]
                and git_sha(raw) == item["git_blob_sha1"], "CurrentChen/native context Git archive changed")
    require(original.path_info(path) == before, "Delta archive changed during verification")
    report = {"schema": SCHEMA + "-verification", "archive": before, "git_tree": revision,
              "original_manifest_sha256": expected_manifest, "manifest_anchor": "caller-supplied original exporter SHA-256",
              "verified_original_members": len(expected), "prior_archive": prior_identity(),
              "actual_prior_members_hashed": len(actual), "prior_references": len(refs),
              "source_references": len(source_refs), "supplemental_files": len(supplements),
              "omitted_staging_aliases": len(staging),
              "repository_context_archives_verified": len(CONTEXT_ARCHIVES),
              "accepted_module_count": 26, "project_context_count": 81,
              "owned_declaration_count": manifest["owned_declaration_count"], "proof_credit": False}
    if output:
        publish(output, encoded(report))
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    cat = subs.add_parser("prior-catalog")
    cat.add_argument("--repo", type=Path, required=True)
    cat.add_argument("--git-tree", required=True)
    cat.add_argument("--output", type=Path, required=True)
    make = subs.add_parser("pack")
    make.add_argument("export_directory", type=Path)
    make.add_argument("--source-catalog", type=Path, required=True)
    make.add_argument("--prior-catalog", type=Path, required=True)
    make.add_argument("--currentchen-adoption-dir", type=Path, required=True)
    make.add_argument("--manifest-sha256", required=True)
    make.add_argument("--output", type=Path, required=True)
    check = subs.add_parser("verify")
    check.add_argument("archive", type=Path)
    check.add_argument("--repo", type=Path, required=True)
    check.add_argument("--git-tree", required=True)
    check.add_argument("--manifest-sha256", required=True)
    check.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "prior-catalog":
            result = catalog(args.repo, args.git_tree, args.output)
        elif args.command == "pack":
            result = pack(args.export_directory, args.source_catalog, args.prior_catalog,
                          args.currentchen_adoption_dir, args.output, args.manifest_sha256)
        else:
            result = verify(args.archive, args.repo, args.git_tree, args.output, args.manifest_sha256)
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, lzma.LZMAError,
            subprocess.CalledProcessError) as error:
        parser.exit(2, "P2.7 evidence delta failed: " + str(error) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
