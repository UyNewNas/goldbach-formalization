#!/usr/bin/env python3
"""Derive one FibreCore-only original-P3 graph; never inspect P1 or run Lean."""
import ast
import collections
import hashlib
import io
import json
import lzma
import os
from pathlib import Path
import resource
import shutil
import tarfile
import time

ROOT = Path("/workspace/scratch/005887317b49")
GRAPH = ROOT / "p29-current/unit-tail-qualified/verification/borrowed-actual-imports-bindings.json"
QUALIFICATION = ROOT / "p29-current/unit-tail-qualified/verification/SUPPLY_QUALIFICATION.json"
AUTHORITY_INDEX = ROOT / "p29-current/fibre-frozen-reuse/FIBRE_FROZEN_ORIGINAL_ARCHIVE_INPUT_INDEX.json"
READER_SOURCE = ROOT / "p29-current/verify-nonunit002-complete-root.py"
PROJECTION_SOURCE = ROOT / "p29-current/omitted-prime-wall-p3-controller-projection-v2-draft.py"
OUT = Path("/tmp/p29-fibre-core-original-subgraph-1126")
LOCAL = ROOT / "p29-current/fibre-core-original-subgraph"
FIBRE = "ImbalancedChen.P2MarkedPrimeProductFibreCore"
FROZEN = "ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants"
GRAPH_BYTES = 27062843
GRAPH_SHA = "6b0e29d00cf57429278bb0416c62f8642c15738a80c61bd4e0dd0b31513c2659"
QUAL_SHA = "1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21"
AUTHORITY_SHA = "25792a0b27c5d9204a4b521e6b92bb690db9aead1890fb655c519bd4f7585554"
READER_SHA = "07200ca08452f61d0185371215e8644742d17e88ac9273cf536ba180d961b6d9"
PROJECTION_SHA = "3c91c59851ff9df46c55db4aa699159841590322707a106a8f230f729fde4f6f"
FACETS = {".olean", ".olean.server", ".olean.private", ".ir.sig", ".ir"}

def stat_record(path):
    st = Path(path).stat()
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]

def hash_file(path):
    h = hashlib.sha256()
    count = 0
    with Path(path).open("rb") as f:
        while block := f.read(1048576):
            h.update(block)
            count += len(block)
    return {"bytes": count, "sha256": h.hexdigest()}

def read_small(path, expected_sha, expected_bytes=None):
    before = stat_record(path)
    b = Path(path).read_bytes()
    assert stat_record(path) == before, ("Small input changed", str(path))
    assert hashlib.sha256(b).hexdigest() == expected_sha, str(path)
    if expected_bytes is not None:
        assert len(b) == expected_bytes
    return b, before

def save_json(path, value):
    with Path(path).open("x", encoding="utf-8", newline="\n") as f:
        json.dump(value, f, indent=2, ensure_ascii=False)
        f.write("\n")

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

def facet_from_path(module, path):
    leaf = module.rsplit(".", 1)[-1]
    name = Path(path).name
    assert name.startswith(leaf + "."), (module, path)
    facet = name[len(leaf):]
    assert facet in FACETS, (module, path, facet)
    return facet

started = time.monotonic()
assert not OUT.exists(), "Do not repeat extraction: inspect the existing derived output first."
assert not (LOCAL / "DELIVERY.json").exists(), "An existing delivery must be reused."
authority_bytes, authority_stat = read_small(AUTHORITY_INDEX, AUTHORITY_SHA, 11341)
qualification_bytes, qualification_stat = read_small(QUALIFICATION, QUAL_SHA, 40177)
reader_bytes, reader_stat = read_small(READER_SOURCE, READER_SHA, 24917)
projection_bytes, projection_stat = read_small(PROJECTION_SOURCE, PROJECTION_SHA, 61964)
authority = json.loads(authority_bytes)
qualification = json.loads(qualification_bytes)
assert authority["original_qualification"]["sha256"] == QUAL_SHA
assert authority["original_qualification"]["actual_input_graph"] == {
    "bytes": GRAPH_BYTES, "sha256": GRAPH_SHA
}
assert authority["manifest"]["sha256"] == "f6246295885137041434ed75c773e4e1d578345bdd552c1033caba016fe36ec3"
assert authority["manifest"]["members"] == 128
assert qualification["status"] == "PASS_CURRENT_P3_BOUND_IMPORTS_NAMED_KERNEL_FULL_OWNED"
assert qualification["actual_import_bindings_sha256"] == GRAPH_SHA
assert len(qualification["borrowed_modules"]) == 18 and FIBRE in qualification["borrowed_modules"]
assert qualification["owned_count"] == 394
fibre_rows = [row for row in authority["rows"] if row["module"] == FIBRE]
assert len(fibre_rows) == 1
fibre_origin = fibre_rows[0]
assert fibre_origin["selected_as_P3_original_project_provider"] is True
assert fibre_origin["object"] == {
    "bytes": 151912,
    "sha256": "7b54021ff39a596a2ab8085ee89c827c77f181e04acc7bb616d193b62b5e2cfa",
}
assert [row["module"] for row in authority["rows"] if row["selected_as_P3_original_project_provider"]] == [FIBRE]

# Extract exactly the already reviewed data-only reader and the unchanged
# reachable_headers definition. No source module's top-level code is executed.
reader_ast = ast.parse(reader_bytes)
reader_nodes = [node for node in reader_ast.body
                if isinstance(node, (ast.FunctionDef, ast.ClassDef))
                and node.name in {"JsonStream", "graph_events"}]
assert {node.name for node in reader_nodes} == {"JsonStream", "graph_events"}
projection_ast = ast.parse(projection_bytes)
reach_nodes = [node for node in projection_ast.body
               if isinstance(node, ast.FunctionDef) and node.name == "reachable_headers"]
assert len(reach_nodes) == 1
reach_namespace = {}
exec(compile(ast.Module(body=reach_nodes, type_ignores=[]),
             str(PROJECTION_SOURCE), "exec"), reach_namespace)
reachable_headers = reach_namespace["reachable_headers"]

graph_before = stat_record(GRAPH)
assert graph_before[2] == GRAPH_BYTES
tracker = {"opens": 0, "reads": 0, "bytes": 0, "sha256": hashlib.sha256()}

class TrackedTextSource:
    """Hash exact UTF-8 bytes while the unchanged reader consumes them once."""
    def __init__(self, path):
        self.file = Path(path).open("r", encoding="utf-8", newline="")
        self.fd_before = os.fstat(self.file.fileno())
        assert [self.fd_before.st_dev, self.fd_before.st_ino, self.fd_before.st_size,
                self.fd_before.st_mtime_ns, self.fd_before.st_ctime_ns] == graph_before

    def __enter__(self):
        return self

    def read(self, n):
        text = self.file.read(n)
        # newline="" preserves original CR/LF bytes; strict UTF-8 decoding and
        # re-encoding preserves every valid original UTF-8 sequence.
        b = text.encode("utf-8")
        tracker["sha256"].update(b)
        tracker["bytes"] += len(b)
        tracker["reads"] += 1
        return text

    def __exit__(self, typ, value, traceback):
        try:
            st = os.fstat(self.file.fileno())
            assert [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns] == graph_before
        finally:
            self.file.close()
        return False

class BoundGraphPath:
    def __init__(self, path):
        assert Path(path) == GRAPH
    def open(self):
        assert tracker["opens"] == 0, "Only one original graph read is allowed."
        tracker["opens"] += 1
        return TrackedTextSource(GRAPH)

reader_namespace = {"json": json, "Path": BoundGraphPath}
exec(compile(ast.Module(body=reader_nodes, type_ignores=[]),
             str(READER_SOURCE), "exec"), reader_namespace)

OUT.mkdir()
LOCAL.mkdir(parents=True, exist_ok=True)
spool = OUT / "selected-parts.jsonl"
headers = {}
metadata = {}
all_pairs = set()
all_authorities = collections.Counter()
selected = None
selected_headers = {}
selected_identities = {}
selected_header_parts = {}
selected_module_facets = collections.defaultdict(set)
selected_authorities = collections.Counter()
selected_prefixes = collections.defaultdict(lambda: {"modules": set(), "facets": 0, "bytes": 0})
parts_seen = 0
with spool.open("x", encoding="utf-8", newline="\n") as parts_out:
    for key, value in reader_namespace["graph_events"](GRAPH):
        if key == "actual_modules":
            assert selected is None, "Pinned graph header rows must precede its parts."
            mod = value["module"]
            assert mod not in headers
            headers[mod] = value
        elif key == "parts":
            if selected is None:
                assert len(headers) == metadata["module_count"]
                assert metadata["part_count"] == 21278
                assert metadata["roots"] == qualification["borrowed_modules"]
                selected = reachable_headers([FIBRE], headers)
                assert {m for m in selected if m.startswith("ImbalancedChen.")} == {FIBRE}
                assert FROZEN not in selected
                selected_headers = {m: headers[m] for m in sorted(selected)}
                for mod, row in selected_headers.items():
                    for part in row["parts"]:
                        k = (mod, facet_from_path(mod, part["resolved_path"]))
                        assert k not in selected_header_parts
                        selected_header_parts[k] = part
            mod, facet = value["module"], value["facet"]
            pair = (mod, facet)
            assert pair not in all_pairs and mod in headers and facet in FACETS
            all_pairs.add(pair)
            parts_seen += 1
            all_authorities[value["authority"]] += 1
            if mod not in selected:
                continue
            identity = value["identity"]
            assert facet_from_path(mod, identity["path"]) == facet
            header = selected_header_parts[pair]
            assert header["resolved_path"] == identity["path"]
            assert header["path"] == value["requested_path"]
            assert identity["bytes"] >= 0 and len(identity["sha256"]) == 64
            assert value["stat_snapshot"][2] == identity["bytes"]
            selected_identities[pair] = identity
            selected_module_facets[mod].add(facet)
            selected_authorities[value["authority"]] += 1
            prefix = mod.split(".", 1)[0]
            selected_prefixes[prefix]["modules"].add(mod)
            selected_prefixes[prefix]["facets"] += 1
            selected_prefixes[prefix]["bytes"] += identity["bytes"]
            parts_out.write(canonical(value) + "\n")
        else:
            assert key not in metadata
            metadata[key] = value

assert tracker["opens"] == 1 and tracker["bytes"] == GRAPH_BYTES
assert tracker["sha256"].hexdigest() == GRAPH_SHA
assert stat_record(GRAPH) == graph_before
assert selected is not None
assert parts_seen == len(all_pairs) == metadata["part_count"] == 21278
assert dict(all_authorities) == metadata["counts"]
assert len(headers) == metadata["module_count"]
assert set(selected_identities) == set(selected_header_parts)
assert {m for m, facet in selected_identities} == selected
assert all((m, ".olean") in selected_identities for m in selected)
for mod, row in selected_headers.items():
    assert set(row["direct_imports"]) <= selected
    present = selected_module_facets[mod]
    if row["is_module"]:
        assert {".olean", ".olean.server", ".olean.private"} <= present
    else:
        assert ".olean.server" not in present and ".olean.private" not in present
    assert (".ir.sig" in present) == (".ir" in present)
assert selected_identities[(FIBRE, ".olean")]["bytes"] == fibre_origin["object"]["bytes"]
assert selected_identities[(FIBRE, ".olean")]["sha256"] == fibre_origin["object"]["sha256"]
for path, original in [(AUTHORITY_INDEX, authority_stat), (QUALIFICATION, qualification_stat),
                       (READER_SOURCE, reader_stat), (PROJECTION_SOURCE, projection_stat)]:
    assert stat_record(path) == original, ("Pinned small input changed", str(path))

pair_hash = hashlib.sha256()
for (mod, facet), identity in sorted(selected_identities.items()):
    pair_hash.update((canonical({"module": mod, "facet": facet, "identity": identity}) + "\n").encode())
pair_sha = pair_hash.hexdigest()
provenance = {
    "authority_index_git_blob": "5ef6ca4bd4e2cb969eed630edeb48f5553ab4946",
    "authority_index_sha256": AUTHORITY_SHA,
    "original_graph": {"member": "verification/borrowed-actual-imports-bindings.json",
                       "bytes": GRAPH_BYTES, "sha256": GRAPH_SHA},
    "original_qualification": {"member": "verification/SUPPLY_QUALIFICATION.json",
                               "bytes": 40177, "sha256": QUAL_SHA},
    "original_manifest": authority["manifest"],
    "original_archive_xz": authority["original_archive"]["archive"]["transport_xz"],
    "original_archive_parts": authority["original_archive"]["parts"],
    "root_acceptance": {"commit": authority["authority_head"],
                        "path": authority["root_acceptance_path"]},
}
derived = OUT / "FIBRE_CORE_ORIGINAL_SUBGRAPH.json"
prefix = {
    "schema": "p29_fibre_core_original_P3_qualified_subgraph_v1",
    "status": "DERIVED_EXACT_ORIGINAL_P3_HEADER_REACHABLE_SUBSET_NOT_P2_RECEPTION",
    "roots": [FIBRE],
    "module_count": len(selected),
    "part_count": len(selected_identities),
    "counts": dict(sorted(selected_authorities.items())),
    "selected_project_modules": [FIBRE],
    "original_provenance": provenance,
    "canonical_selected_pair_identity_sha256": pair_sha,
    "P2_current_paths_or_qualification_claimed": False,
    "new_proof_credit": 0,
}
with derived.open("x", encoding="utf-8", newline="\n") as f:
    f.write("{\n")
    for key, value in prefix.items():
        f.write(json.dumps(key) + ":" + canonical(value) + ",\n")
    f.write('"actual_modules":' + canonical(list(selected_headers.values())) + ',\n"parts":[\n')
    emitted = 0
    with spool.open(encoding="utf-8", newline="") as inp:
        for line in inp:
            if emitted:
                f.write(",\n")
            f.write(line.rstrip("\n"))
            emitted += 1
    assert emitted == len(selected_identities)
    f.write("\n]}\n")
derived_identity = hash_file(derived)

helper_hashes = {
    node.name: hashlib.sha256(ast.dump(node, include_attributes=False).encode()).hexdigest()
    for node in [*reader_nodes, *reach_nodes]
}
(OUT / "ORIGINAL_SUPPLY_QUALIFICATION.json").write_bytes(qualification_bytes)
(OUT / "SOURCE_AUTHORITY_INDEX.json").write_bytes(authority_bytes)
script_bytes = Path(__file__).read_bytes()
(OUT / "EXTRACT_FIBRE_SUBGRAPH.py").write_bytes(script_bytes)
record = {
    "schema": "p29_single_pass_fibre_original_graph_extraction_record_v1",
    "original_graph_open_count": tracker["opens"],
    "original_graph_parse_count": 1,
    "original_graph_read_calls": tracker["reads"],
    "original_graph_bytes_hashed_in_same_read_stream": tracker["bytes"],
    "original_graph_sha256": tracker["sha256"].hexdigest(),
    "original_graph_before_after_stat": graph_before,
    "stream_reader": {"source": str(READER_SOURCE), "sha256": READER_SHA,
                      "definitions": ["JsonStream", "graph_events"],
                      "AST_bodies_unchanged": True,
                      "IO_binding": "Only Path.open is bound to the one original UTF-8 hashing stream; no reader AST body changes."},
    "reachability": {"source": str(PROJECTION_SOURCE), "git_blob": "32f34beec48801d22e540e19963f0ee71cc04eb7",
                     "sha256": PROJECTION_SHA, "definition": "reachable_headers",
                     "AST_body_unchanged": True, "root": FIBRE},
    "helper_AST_sha256": helper_hashes,
    "original_modules": metadata["module_count"],
    "original_parts": metadata["part_count"],
    "selected_modules": len(selected),
    "selected_parts": len(selected_identities),
    "all_original_pair_keys_unique": True,
    "all_selected_header_part_rows_equal_selected_part_identity_rows": True,
    "every_selected_header_import_remains_selected": True,
    "selected_project_modules": [FIBRE],
    "Frozen_selected": False,
    "canonical_selected_pair_identity_sha256": pair_sha,
    "derived_graph": derived_identity,
    "no_P1_graph_read": True,
    "no_P1_P3_comparison_repeated": True,
    "no_Lean_or_remote_calls": True,
    "no_supplier_objects_read_or_copied": True,
    "no_proof_replay": True,
    "existing_artifact_check": {
        "scope": "Filename candidates only within p29-current and p29-atlas-1126, then schemas of these two existing projections.",
        "candidates": [
            {"path": "p29-atlas-1126/P3_EXISTING_UNIT18_EXACT_JOIN_PROJECTION.json",
             "schema": "p29_p3_existing_unit18_join_projection_v1", "has_actual_modules_or_parts": False},
            {"path": "p29-atlas-1126/OMITTED_SELECTIVE_58_PROJECT_SUPPLIER_PROJECTION.json",
             "schema": "p29_omitted_exact_selected_project_source_object_projection_v1", "has_actual_modules_or_parts": False}
        ],
        "same_single_root_actual_facet_subgraph_found_in_this_scope": False,
        "global_absence_claim": False
    },
    "elapsed_seconds_before_packaging": round(time.monotonic() - started, 3),
    "max_rss_kib_before_packaging": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
}
save_json(OUT / "EXTRACTION_RECORD.json", record)
prefixes = {name: {"modules": len(value["modules"]), "facets": value["facets"], "bytes": value["bytes"]}
            for name, value in sorted(selected_prefixes.items())}
index = {
    "schema": "p29_fibre_core_original_P3_subgraph_index_v1",
    "status": prefix["status"],
    "roots": [FIBRE],
    "selected_project_modules": [FIBRE],
    "selected_module_count": len(selected),
    "selected_part_count": len(selected_identities),
    "selected_raw_facet_bytes_sum": sum(v["bytes"] for v in selected_identities.values()),
    "raw_facet_bytes_sum_is_not_P2_missing_transfer_size": True,
    "prefix_counts": prefixes,
    "derived_graph": {"member": derived.name, **derived_identity},
    "canonical_selected_pair_identity_sha256": pair_sha,
    "canonical_pair_digest_format": "SHA256 of concatenated ASCII JSON lines sorted by (module, facet); each line is json.dumps({module,facet,identity}, sort_keys=True, separators=(',',':'), ensure_ascii=True)+'\\n'.",
    "source_authority": provenance,
    "fibre_origin": fibre_origin,
    "Frozen_scope": {
        "module": FROZEN, "in_selected_subgraph": False,
        "authority": "P1 Nonunit accepted dependency",
        "transport": "Unit package bytes may be reused only because their source/object bytes equal that P1 authority. They do not add a P3 selected project."
    },
    "qualification_boundary": {
        "original_18_module_394_owned_qualification_retained": True,
        "original_Fibre_owned_count_from_accepted_index": fibre_origin["original_qualified_owned_count"],
        "owned_or_kernel_checks_repeated": 0,
        "P2_reception_or_current_stat_attested": False,
        "P2_combined_qualification_attested": False,
        "new_proof_credit": 0
    },
    "extraction_record": {"member": "EXTRACTION_RECORD.json", **hash_file(OUT / "EXTRACTION_RECORD.json")},
    "extractor": {"member": "EXTRACT_FIBRE_SUBGRAPH.py", **hash_file(OUT / "EXTRACT_FIBRE_SUBGRAPH.py")},
}
save_json(OUT / "INDEX.json", index)
spool.unlink()  # Derived staging rows are now represented exactly by the final graph.
member_names = ["FIBRE_CORE_ORIGINAL_SUBGRAPH.json", "INDEX.json", "EXTRACTION_RECORD.json",
                "EXTRACT_FIBRE_SUBGRAPH.py", "ORIGINAL_SUPPLY_QUALIFICATION.json", "SOURCE_AUTHORITY_INDEX.json"]
manifest = {name: hash_file(OUT / name) for name in member_names}
save_json(OUT / "MANIFEST.json", manifest)
member_names.append("MANIFEST.json")
archive = OUT / "FIBRE_CORE_ORIGINAL_SUBGRAPH.tar.xz"
with lzma.open(archive, "wb", preset=3) as compressed:
    with tarfile.open(fileobj=compressed, mode="w|", format=tarfile.USTAR_FORMAT) as tar:
        for name in sorted(member_names):
            p = OUT / name
            info = tarfile.TarInfo(name)
            info.size = p.stat().st_size
            info.mode = 0o644
            info.uid = info.gid = info.mtime = 0
            info.uname = info.gname = ""
            with p.open("rb") as f:
                tar.addfile(info, f)
archive_identity = hash_file(archive)
# Verify only the new derived archive, not the original graph a second time.
with tarfile.open(archive, mode="r:xz") as tar:
    members = tar.getmembers()
    assert sorted(m.name for m in members) == sorted(member_names)
    assert all(m.isfile() for m in members)
    for member in members:
        expected = hash_file(OUT / member.name)
        with tar.extractfile(member) as content:
            h = hashlib.sha256()
            size = 0
            while block := content.read(1048576):
                h.update(block)
                size += len(block)
        assert {"bytes": size, "sha256": h.hexdigest()} == expected
for name in ["INDEX.json", "EXTRACTION_RECORD.json", "MANIFEST.json"]:
    shutil.copyfile(OUT / name, LOCAL / name)
shutil.copyfile(archive, LOCAL / archive.name)
delivery = {
    "schema": "p29_fibre_core_original_subgraph_delivery_v1",
    "status": prefix["status"],
    "expanded_directory": str(OUT),
    "local_archive": str(LOCAL / archive.name),
    "archive": archive_identity,
    "archive_members": len(member_names),
    "all_derived_archive_members_byte_verified": True,
    "index": hash_file(OUT / "INDEX.json"),
    "manifest": hash_file(OUT / "MANIFEST.json"),
    "derived_graph": derived_identity,
    "selected_modules": len(selected), "selected_parts": len(selected_identities),
    "selected_project_modules": [FIBRE],
    "graph_read_and_parse_count": 1,
    "elapsed_seconds": round(time.monotonic() - started, 3),
    "max_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    "git_blob_pending_upload": True,
    "P2_current_paths_or_qualification_claimed": False,
    "new_proof_credit": 0,
}
save_json(LOCAL / "DELIVERY.json", delivery)
print(json.dumps(delivery, sort_keys=True))
