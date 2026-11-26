#!/usr/bin/env python3
"""Compare only the new Fibre nonproject subset with an existing accepted JSONL index."""
import ast
import hashlib
import json
import os
from pathlib import Path
import resource
import time

ROOT = Path("/workspace/scratch/005887317b49")
OUT = ROOT / "p29-current/fibre-core-original-subgraph"
GRAPH = Path("/tmp/p29-fibre-core-original-subgraph-1126/FIBRE_CORE_ORIGINAL_SUBGRAPH.json")
BASE = ROOT / "p29-current/nonunit-p3-facet-delta"
READER = ROOT / "p29-current/verify-nonunit002-complete-root.py"
EXTRACTOR = OUT / "EXTRACT_FIBRE_SUBGRAPH.py"
FIBRE = "ImbalancedChen.P2MarkedPrimeProductFibreCore"

def git_oid(b):
    return hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()

def stat_record(path):
    st = Path(path).stat()
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]

def save_json(path, value):
    with Path(path).open("x", encoding="utf-8") as f:
        json.dump(value, f, indent=2)
        f.write("\n")

started = time.monotonic()
report_path = OUT / "FIBRE_NONPROJECT_IN_EXISTING_P1_INDEX.json"
assert not report_path.exists(), "Reuse the existing comparison rather than repeat it."
summary_bytes = (BASE / "SUMMARY.json").read_bytes()
assert git_oid(summary_bytes) == "4f6f1d9059d9b1831b81ef4c6e8094a3ce07b8ca"
summary = json.loads(summary_bytes)
index_bytes = (OUT / "INDEX.json").read_bytes()
assert git_oid(index_bytes) == "c2b59eb93ebff3aad919b519f2af2dc2cdb895e5"
index = json.loads(index_bytes)
assert index["roots"] == index["selected_project_modules"] == [FIBRE]
assert index["source_authority"]["original_graph"]["sha256"] == summary["P3"]["graph"]["sha256"]
assert summary["counts"]["same_key_different_bytes"] == 0
assert summary["exact_lists"]["same_key_different_bytes"]["bytes"] == 0
assert summary["exact_lists"]["same_key_different_bytes"]["sha256"] == hashlib.sha256(b"").hexdigest()

reader_bytes = READER.read_bytes()
assert hashlib.sha256(reader_bytes).hexdigest() == "07200ca08452f61d0185371215e8644742d17e88ac9273cf536ba180d961b6d9"
extractor_bytes = EXTRACTOR.read_bytes()
assert git_oid(extractor_bytes) == "cfa097b555171b0a9f7b08b778d9da37fcc77e01"
reader_nodes = [node for node in ast.parse(reader_bytes).body
                if isinstance(node, (ast.FunctionDef, ast.ClassDef))
                and node.name in {"JsonStream", "graph_events"}]
wrapper_nodes = [node for node in ast.parse(extractor_bytes).body
                 if isinstance(node, ast.ClassDef)
                 and node.name in {"TrackedTextSource", "BoundGraphPath"}]
assert len(reader_nodes) == len(wrapper_nodes) == 2
graph_before = stat_record(GRAPH)
tracker = {"opens": 0, "reads": 0, "bytes": 0, "sha256": hashlib.sha256()}
wrapper_ns = {"Path": Path, "os": os, "GRAPH": GRAPH, "graph_before": graph_before, "tracker": tracker}
exec(compile(ast.Module(body=wrapper_nodes, type_ignores=[]), str(EXTRACTOR), "exec"), wrapper_ns)
reader_ns = {"Path": wrapper_ns["BoundGraphPath"], "json": json}
exec(compile(ast.Module(body=reader_nodes, type_ignores=[]), str(READER), "exec"), reader_ns)

selected = {}
project = []
for key, value in reader_ns["graph_events"](GRAPH):
    if key != "parts":
        continue
    pair = (value["module"], value["facet"])
    if pair[0].startswith("ImbalancedChen."):
        project.append(pair)
    else:
        assert pair not in selected
        selected[pair] = value["identity"]
assert tracker["opens"] == 1
assert {"bytes": tracker["bytes"], "sha256": tracker["sha256"].hexdigest()} == {
    key: index["derived_graph"][key] for key in ["bytes", "sha256"]
}
assert stat_record(GRAPH) == graph_before
assert project == [(FIBRE, ".olean")]
assert len(selected) == 11625 and len({module for module, facet in selected}) == 2325

def read_jsonl_index(kind, visit):
    item = summary["exact_lists"][kind]
    path = BASE / (kind + ".jsonl")
    before = stat_record(path)
    h = hashlib.sha256()
    size = 0
    seen = set()
    with path.open("rb") as f:
        for line in f:
            h.update(line)
            size += len(line)
            row = json.loads(line)
            pair = (row["module"], row["facet"])
            assert pair not in seen
            seen.add(pair)
            visit(pair, row)
    assert stat_record(path) == before
    assert {"bytes": size, "sha256": h.hexdigest()} == {k: item[k] for k in ["bytes", "sha256"]}
    assert len(seen) == summary["counts"][kind]
    return {"path": str(path), "bytes": size, "sha256": h.hexdigest(),
            "git_blob": item["git_blob"], "rows": len(seen)}

found = {}
conflicts = []
different_paths = 0

def same_visit(pair, row):
    global different_paths
    assert (row["P1"]["bytes"], row["P1"]["sha256"]) == (row["P3"]["bytes"], row["P3"]["sha256"])
    if pair not in selected:
        return
    # This is an original-origin identity check, not a current-host path test.
    assert row["P3"] == selected[pair], ("Same pinned P3 graph row differs", pair)
    found[pair] = row["P1"]
    different_paths += row["P1"]["path"] != selected[pair]["path"]

same_input = read_jsonl_index("same_bytes", same_visit)
only_input = None
if set(selected) != set(found):
    def only_visit(pair, row):
        if pair not in selected:
            return
        identity = selected[pair]
        if (row["P1"]["bytes"], row["P1"]["sha256"]) == (identity["bytes"], identity["sha256"]):
            found[pair] = row["P1"]
        else:
            conflicts.append({"module": pair[0], "facet": pair[1],
                              "Fibre_original_P3": identity, "P1": row["P1"]})
    only_input = read_jsonl_index("only_P1_reachable", only_visit)

conflict_pairs = {(row["module"], row["facet"]) for row in conflicts}
extra = [{"module": module, "facet": facet, "Fibre_original_P3": selected[(module, facet)]}
         for module, facet in sorted(set(selected) - set(found) - conflict_pairs)]
all_same = len(found) == len(selected) and not extra and not conflicts
assert len(found) + len(extra) + len(conflicts) == len(selected)
save_json(OUT / "EXTRA_RELATIVE_TO_EXISTING_P1.json", extra)
save_json(OUT / "BYTE_CONFLICTS_WITH_EXISTING_P1.json", conflicts)
pair_digest = hashlib.sha256()
for (module, facet), identity in sorted(selected.items()):
    row = {"module": module, "facet": facet, "bytes": identity["bytes"], "sha256": identity["sha256"]}
    pair_digest.update((json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n").encode())
report = {
    "schema": "p29_fibre_nonproject_subset_of_existing_P1_same_bytes_index_v1",
    "status": "ALL_FIBRE_NONPROJECT_FACETS_ALREADY_IN_P1_SAME_BYTES_INDEX" if all_same
              else "EXACT_EXTRA_OR_CONFLICT_ROWS_RECORDED",
    "question": "Whether only FibreCore's 2325 nonproject modules / 11625 facets add any byte identities beyond the existing accepted P1 Nonunit graph.",
    "Fibre_subgraph_index_git_blob": "c2b59eb93ebff3aad919b519f2af2dc2cdb895e5",
    "Fibre_subgraph": index["derived_graph"],
    "Fibre_original_P3_graph_sha256": summary["P3"]["graph"]["sha256"],
    "P1_original_graph_sha256": summary["P1"]["graph"]["sha256"],
    "P1_original_root_acceptance": summary["P1"]["original_root_acceptance"]["git_blob"],
    "P1_original_root_acceptance_commit": summary["P1"]["root_acceptance_commit"],
    "existing_comparison_summary_git_blob": "4f6f1d9059d9b1831b81ef4c6e8094a3ce07b8ca",
    "existing_same_bytes_index": same_input,
    "existing_only_P1_index_read": only_input,
    "empty_conflict_index_reused_from_fixed_summary_without_reparse": True,
    "selected_nonproject_modules": len({module for module, facet in selected}),
    "selected_nonproject_facets": len(selected),
    "same_bytes_facets": len(found),
    "extra_relative_to_P1_facets": len(extra),
    "conflicting_facets": len(conflicts),
    "all_selected_nonproject_bytes_already_in_P1": all_same,
    "different_recorded_P1_P3_paths_ignored_for_byte_equality": different_paths,
    "selected_nonproject_facet_bytes_sum": sum(v["bytes"] for v in selected.values()),
    "canonical_selected_nonproject_module_facet_bytes_sha256_digest": pair_digest.hexdigest(),
    "comparison_key": ["module", "facet"],
    "byte_equality_fields": ["bytes", "sha256"],
    "extra_rows": extra,
    "conflict_rows": conflicts,
    "work": {
        "original_P1_graph_reads": 0, "original_P3_graph_reads": 0,
        "derived_Fibre_graph_reads_and_parses": 1,
        "existing_same_bytes_jsonl_reads_and_parses": 1,
        "existing_only_P1_jsonl_reads": 0 if only_input is None else 1,
        "original_compiler_object_or_source_files_read": 0,
        "remote_calls": 0, "Lean_calls": 0, "proof_replays": 0,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "max_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    },
    "interpretation": {
        "new_Fibre_standard_facet_demand_beyond_P1_snapshot": not all_same,
        "if_all_same": "Fibre adds no nonproject byte identity beyond the already accepted P1 Nonunit input set. This is an original-evidence set comparison only.",
        "P2_current_availability": "Not checked or established. This does not establish that the 14 MathlibNt modules are the only missing P2 inputs; other P1 facets still require the chosen P2 current input binding.",
        "physical_paths": "Old P1/P3 path inequality is not a byte conflict and neither old path is asserted to exist on P2.",
    },
    "P2_current_paths_or_combined_qualification_claimed": False,
    "new_proof_credit": 0,
}
save_json(report_path, report)
print(json.dumps({key: report[key] for key in [
    "status", "selected_nonproject_modules", "selected_nonproject_facets", "same_bytes_facets",
    "extra_relative_to_P1_facets", "conflicting_facets",
    "different_recorded_P1_P3_paths_ignored_for_byte_equality", "work"
]}, sort_keys=True))
