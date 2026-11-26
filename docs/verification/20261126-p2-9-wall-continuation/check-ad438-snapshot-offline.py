#!/usr/bin/env python3
"""Inspect only fixed ad438 metadata once; no Lean, network, or provider-file reads."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import resource
import time

RAW_BYTES = 20904189
RAW_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
P1_SUMMARY_BLOB = "4f6f1d9059d9b1831b81ef4c6e8094a3ce07b8ca"
FACETS = (".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir")
FIELD_NAMES = {"actualmodules", "moduleheaders", "headers", "header", "moduledata",
               "ismodule", "directimports", "parts", "facet", "facets", "importgraph"}
BASE = Path("/workspace/scratch/005887317b49/p29-current/nonunit-p3-facet-delta")

def oid(b):
    return hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()

def stamp(p):
    s = Path(p).stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]

def canonical_hash(value):
    h = hashlib.sha256()
    encoder = json.JSONEncoder(sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    for chunk in encoder.iterencode(value):
        h.update(chunk.encode())
    return h.hexdigest()

def save(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as f:
        json.dump(value, f, indent=2, ensure_ascii=True)
        f.write("\n")

def line(f, value):
    f.write(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n")

def identity(path, row):
    assert isinstance(path, str) and PurePosixPath(path).is_absolute()
    assert isinstance(row["bytes"], int) and row["bytes"] >= 0
    assert isinstance(row["sha256"], str) and len(row["sha256"]) == 64
    return {"path": path, "bytes": row["bytes"], "sha256": row["sha256"]}

def file_identity(path):
    h, size = hashlib.sha256(), 0
    with Path(path).open("rb") as f:
        while b := f.read(1048576):
            h.update(b)
            size += len(b)
    return {"bytes": size, "sha256": h.hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    source, out = args.snapshot, args.output
    assert source.is_file() and not out.exists(), "Use the original input and a fresh output directory."
    before = stamp(source)
    assert before[2] == RAW_BYTES
    started = time.monotonic()
    raw_hash = hashlib.sha256()
    read_bytes = 0

    # json.load reads this text stream once. newline="" avoids changing CR/LF.
    class HashedReader:
        def __init__(self, f):
            self.f = f
        def read(self, n=-1):
            nonlocal read_bytes
            text = self.f.read(n)
            encoded = text.encode("utf-8")
            raw_hash.update(encoded)
            read_bytes += len(encoded)
            return text

    with source.open("r", encoding="utf-8", newline="") as f:
        value = json.load(HashedReader(f))
        s = os.fstat(f.fileno())
        assert [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns] == before
    assert stamp(source) == before and read_bytes == RAW_BYTES
    assert raw_hash.hexdigest() == RAW_SHA
    assert isinstance(value, dict)
    assert value["schema"] == "p2-winner9-qualified-native-environment-v1"
    assert value["status"] == "QUALIFIED_NATIVE_INPUTS_ONLY_NOT_PROOF_ACCEPTANCE"
    assert value["compile_credit"] is False and value["kernel_credit"] is False
    unsigned = {k: v for k, v in value.items() if k != "context_signature"}
    assert value["context_signature"] == canonical_hash(unsigned)
    del unsigned
    files, resolutions, modules = value["files"], value["resolutions"], value["modules"]
    assert all(isinstance(v, dict) for v in [files, resolutions, modules])
    assert set(modules) <= set(resolutions)
    out.mkdir(parents=True)
    counts = {"modules": len(modules), "files": len(files), "resolutions": len(resolutions)}
    prefixes, declared_facets, referenced_files = {}, {}, set()
    file_kinds = {f: 0 for f in FACETS}
    file_kinds["other"] = 0
    for path, rec in files.items():
        identity(path, rec)
        kind = next((f for f in sorted(FACETS, key=len, reverse=True) if path.endswith(f)), "other")
        file_kinds[kind] += 1

    attention = []
    with (out / "P2_DECLARED_FACETS.jsonl").open("x", encoding="utf-8") as f:
        for mod, path in sorted(resolutions.items()):
            assert isinstance(mod, str) and isinstance(path, str) and path in files
            prefix = mod.split(".", 1)[0]
            prefixes[prefix] = prefixes.get(prefix, 0) + 1
            if mod in modules:
                assert modules[mod]["object"] == path
            candidates = [(".olean", path, "original_resolutions_entry")]
            if path.endswith(".olean"):
                stem = path[:-len(".olean")]
                candidates += [(facet, stem + facet, "existing_exact_companion_path_in_files")
                               for facet in FACETS[1:] if stem + facet in files]
            else:
                attention.append({"module": mod, "path": path,
                                  "reason": "Base resolution path does not end in .olean; no companion suffix inference."})
            for facet, present, method in candidates:
                key = (mod, facet)
                assert key not in declared_facets
                rec = identity(present, files[present])
                declared_facets[key] = rec
                referenced_files.add(present)
                line(f, {"module": mod, "facet": facet, "identity": rec,
                         "association": method, "original_snapshot_sha256": RAW_SHA})
    unassociated_companions = 0
    with (out / "UNASSOCIATED_COMPANION_FILES.jsonl").open("x", encoding="utf-8") as f:
        for path, rec in sorted(files.items()):
            if path not in referenced_files and any(path.endswith(suffix) for suffix in FACETS[1:]):
                line(f, identity(path, rec))
                unassociated_companions += 1

    # Record actual extra structure and exact candidate fields; field names alone
    # do not certify that these are compiled headers or a complete import closure.
    structure_counts, header_candidate_count = {}, 0
    with (out / "EXTRA_STRUCTURE_LOCATORS.jsonl").open("x", encoding="utf-8") as loc, \
         (out / "HEADER_CANDIDATES.jsonl").open("x", encoding="utf-8") as candidates:
        def walk(node, pointer=""):
            nonlocal header_candidate_count
            if isinstance(node, dict):
                is_key = next((k for k in ["is_module", "isModule"] if isinstance(node.get(k), bool)), None)
                imports_key = next((k for k in ["direct_imports", "imports"] if isinstance(node.get(k), list)), None)
                if is_key is not None and imports_key is not None:
                    keep = [k for k in ["module", "name", "module_name", is_key, imports_key, "parts"] if k in node]
                    line(candidates, {"pointer": pointer, "fields": {k: node[k] for k in keep},
                                      "original_row_sha256": canonical_hash(node),
                                      "compiled_semantics_not_inferred_from_names": True})
                    header_candidate_count += 1
                for k, v in node.items():
                    p = pointer + "/" + k.replace("~", "~0").replace("/", "~1")
                    normalized = k.replace("_", "").lower()
                    if normalized in FIELD_NAMES:
                        structure_counts[k] = structure_counts.get(k, 0) + 1
                        line(loc, {"pointer": p, "field": k, "type": type(v).__name__,
                                   "length": len(v) if isinstance(v, (dict, list, str)) else None})
                    if isinstance(v, (dict, list)):
                        walk(v, p)
            elif isinstance(node, list):
                for i, v in enumerate(node):
                    if isinstance(v, (dict, list)):
                        walk(v, pointer + "/" + str(i))
        walk(value)
    native_source_edges = 0
    with (out / "NATIVE_SOURCE_IMPORTS.jsonl").open("x", encoding="utf-8") as f:
        for mod, rec in sorted(modules.items()):
            assert rec["source"] in files and rec["object"] in files
            assert isinstance(rec["imports"], list)
            native_source_edges += len(rec["imports"])
            line(f, {"module": mod, "source": identity(rec["source"], files[rec["source"]]),
                     "object": identity(rec["object"], files[rec["object"]]),
                     "source_imports": rec["imports"], "provider": rec["provider"],
                     "closure_signature": rec["closure_signature"],
                     "source_imports_are_not_asserted_compiled_headers": True})
    shape = {
        "schema": "p29_ad438_actual_snapshot_shape_v1",
        "status": "EXACT_RAW_AND_CONTEXT_VERIFIED_METADATA_EXTRACTED",
        "raw_source": {"path": str(source), "bytes": read_bytes, "sha256": RAW_SHA,
                       "before_after_stat": before, "read_and_parse_count": 1},
        "context_signature": value["context_signature"], "context_signature_verified": True,
        "top_level_keys": sorted(value), "counts": counts,
        "resolution_prefix_counts": dict(sorted(prefixes.items())),
        "physical_file_suffix_counts": file_kinds,
        "declared_module_facet_count": len(declared_facets),
        "unassociated_companion_file_count": unassociated_companions,
        "noncanonical_resolution_paths": attention,
        "observed_extra_structure_field_counts": structure_counts,
        "header_candidate_count": header_candidate_count,
        "header_candidates_are_not_automatically_verified_compiled_headers": True,
        "native_source_import_edges": native_source_edges,
        "runtime": value["runtime"], "qualification": value["qualification"],
        "source_schema_review_blob": "8be3c4d4354aef52fec076b22fd17e85da4b5f90",
        "current_P2_filesystem_or_complete_import_graph_attested": False,
        "no_companion_file_was_invented": True,
    }
    save(out / "SNAPSHOT_SHAPE.json", shape)
    # Keep only the useful small facet map while comparing the existing P1 index.
    del value, files, resolutions, modules

    summary_bytes = (BASE / "SUMMARY.json").read_bytes()
    assert oid(summary_bytes) == P1_SUMMARY_BLOB
    summary = json.loads(summary_bytes)
    assert summary["counts"]["same_key_different_bytes"] == 0
    required, seen = {}, set()
    index_inputs = []
    for category in ["same_bytes", "only_P1_reachable"]:
        item = summary["exact_lists"][category]
        path = BASE / (category + ".jsonl")
        old = stamp(path)
        h, size, rows = hashlib.sha256(), 0, 0
        with path.open("rb") as f:
            for b in f:
                h.update(b)
                size += len(b)
                row = json.loads(b)
                key = (row["module"], row["facet"])
                assert key not in seen
                seen.add(key)
                rows += 1
                if not row["module"].startswith("ImbalancedChen."):
                    required[key] = row["P1"]
        assert stamp(path) == old
        assert {"bytes": size, "sha256": h.hexdigest()} == {k: item[k] for k in ["bytes", "sha256"]}
        assert rows == summary["counts"][category]
        index_inputs.append({"category": category, "git_blob": item["git_blob"],
                             "bytes": size, "sha256": h.hexdigest(), "rows": rows})
    assert len(seen) == summary["P1"]["facets"]
    streams = {key: (out / filename).open("x", encoding="utf-8") for key, filename in [
        ("same", "P1_REQUIRED_SAME_BYTES.jsonl"),
        ("conflict", "P1_REQUIRED_BYTE_CONFLICTS.jsonl"),
        ("not_described", "P1_REQUIRED_NOT_DESCRIBED.jsonl")]}
    diff_counts = {key: 0 for key in streams}
    try:
        for key, wanted in sorted(required.items()):
            available = declared_facets.get(key)
            kind = ("not_described" if available is None else
                    "same" if (wanted["bytes"], wanted["sha256"]) == (available["bytes"], available["sha256"])
                    else "conflict")
            row = {"module": key[0], "facet": key[1], "P1_required": wanted}
            if available is not None:
                row["P2_original_descriptor"] = available
            line(streams[kind], row)
            diff_counts[kind] += 1
    finally:
        for f in streams.values():
            f.close()
    report = {
        "schema": "p29_ad438_vs_existing_P1_nonproject_identity_index_v1",
        "status": "ORIGINAL_DESCRIPTOR_SET_COMPARISON_ONLY_NOT_CURRENT_P2_QUALIFICATION",
        "snapshot_sha256": RAW_SHA, "snapshot_shape_member": "SNAPSHOT_SHAPE.json",
        "P1_original_graph_sha256": summary["P1"]["graph"]["sha256"],
        "P1_original_root_acceptance_blob": summary["P1"]["original_root_acceptance"]["git_blob"],
        "P1_derived_summary_git_blob": P1_SUMMARY_BLOB, "existing_derived_inputs": index_inputs,
        "Fibre_nonproject_subset_already_covered_by_P1_report_blob": "c1ed8abf36788cb5674d1ed230328cead8a6ab20",
        "required_nonproject_modules": len({m for m, f in required}),
        "required_nonproject_facets": len(required), "counts": diff_counts,
        "comparison_key": ["module", "facet"], "equality_fields": ["bytes", "sha256"],
        "paths_ignored_for_byte_equality": True,
        "not_described_means": "No associated module/facet row was recoverable from this descriptor's resolutions and exact companion paths. It is not a claim of physical absence on P2.",
        "complete_compiled_header_relationship_established": False,
        "new_formal_credit": 0,
    }
    save(out / "P1_NONPROJECT_DIFF.json", report)
    execution = {
        "schema": "p29_ad438_offline_checker_execution_v1", "status": "COMPLETED",
        "snapshot_read_and_parse_count": 1, "original_P1_graph_reads": 0,
        "original_P3_graph_reads": 0, "compiler_object_or_source_reads": 0,
        "remote_calls": 0, "Lean_calls": 0, "proof_replays": 0,
        "source_files_modified": 0, "elapsed_seconds": round(time.monotonic() - started, 3),
        "max_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "checker_sha256": file_identity(Path(__file__))["sha256"],
        "new_formal_credit": 0,
    }
    save(out / "EXECUTION.json", execution)
    manifest = {p.name: file_identity(p) for p in sorted(out.iterdir()) if p.is_file()}
    save(out / "MANIFEST.json", manifest)
    print(json.dumps({"shape_counts": counts, "declared_facets": len(declared_facets),
                      "header_candidates": header_candidate_count,
                      "P1_nonproject_diff_counts": diff_counts,
                      "execution": execution}, sort_keys=True))

if __name__ == "__main__":
    main()
