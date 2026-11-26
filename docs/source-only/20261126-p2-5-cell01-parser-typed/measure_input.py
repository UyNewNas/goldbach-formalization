#!/usr/bin/env python3
"""Measure the exact Cell01 witness using the unchanged existing host planner.

This supplies untrusted source-generation parameters, never a parse certificate.
Only canonical index/source id 1 is in scope. No Lean or remote task is started.
"""
import argparse
import ast
from collections import Counter
import dataclasses
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
INPUT_NAME = "eighth-prefix-family-20261009-cell-01.witness.json"
INPUT_BYTES = 344873
INPUT_SHA = "d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f"
CANONICAL_INDEX = 1
REFERENCE_DIRECT = REPO / "docs/source-only/20261126-p2-5-cell00-segmented/generate_direct.py"
REFERENCE_DIRECT_SHA = "4a60cc5195373c03f141a36e04023243a2008f0f14edbb9ade436e1347fc995b"
REFERENCE_TYPED = REPO / "docs/source-only/20261126-p2-5-cell00-decoded/generate_typed_payload.py"
REFERENCE_TYPED_SHA = "02117d243a8dd43f62bd663fd1d1a655f58d407befa05d836da797c83f98f4b8"
DONOR = REFERENCE_DIRECT.parent / "donor/generate.py"
DONOR_SHA = "3114c68369ad3a6e3f7e3171aedadb40830917cf1592cc09e99932afdf71703d"
DONOR_NAMES = {"Node", "Field", "RawPlanner", "quote_char", "quote_list", "lean_node"}
MEASUREMENTS = ROOT / "INPUT_MEASUREMENTS.json"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def checked_bytes(path, expected):
    data = Path(path).read_bytes()
    if sha(data) != expected:
        raise RuntimeError("Pinned original bytes differ: " + str(path))
    return data


def immutable(path, data):
    if path.exists():
        assert path.read_bytes() == data, f'Generated output drift: {path}'
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def donor_namespace():
    donor = checked_bytes(DONOR, DONOR_SHA)
    checked_bytes(REFERENCE_DIRECT, REFERENCE_DIRECT_SHA)
    typed = ast.parse(checked_bytes(REFERENCE_TYPED, REFERENCE_TYPED_SHA))
    schemas = {node.targets[0].id: ast.literal_eval(node.value) for node in typed.body
               if isinstance(node, ast.Assign) and len(node.targets) == 1
               and isinstance(node.targets[0], ast.Name)
               and node.targets[0].id in {"FIELDS", "SIMPLEX_FIELDS"}}
    body = [node for node in ast.parse(donor).body
            if isinstance(node, (ast.ClassDef, ast.FunctionDef)) and node.name in DONOR_NAMES]
    assert {node.name for node in body} == DONOR_NAMES
    ns = {"dataclass": dataclasses.dataclass, "field": dataclasses.field,
          "WHITE": b" \r\n\t", "__name__": "__main__"}
    exec(compile(ast.Module(body=body, type_ignores=[]), "<unchanged donor AST quotation>", "exec"), ns)
    return ns, schemas


def load_input(path):
    """Return pinned raw bytes, original planner output, schemas and measured facts."""
    raw = checked_bytes(path, INPUT_SHA)
    assert len(raw) == INPUT_BYTES and raw.isascii()
    ns, schemas = donor_namespace()
    planner = ns["RawPlanner"](raw)
    node = planner.value(0)
    obj = json.loads(raw)
    fields, simplex_fields = schemas["FIELDS"], schemas["SIMPLEX_FIELDS"]
    assert node.kind == "obj" and len(fields) == 17 and len(simplex_fields) == 10
    assert list(obj) == [key for key, _ in fields] == [field.key.scalar for field in node.fields]
    assert obj["cell_id"] == CANONICAL_INDEX and obj["dimension"] == 8 and obj["physical_jacobian"] == 1
    assert len(obj["simplices"]) == 81
    assert len(obj["all_original_constraint_minima"]) == 96
    assert all(len(row) == 8 for row in obj["vertices"])
    assert all(list(row) == [key for key, _ in simplex_fields] for row in obj["simplices"])
    assert all(len(row["vertex_ids"]) == 9 and len(row["factor_maxima"]) == 10
               and len(row["gap_weighted_means"]) == 10 for row in obj["simplices"])
    assert all(c in ns["WHITE"] for c in raw[node.end:])
    rationals, integers = [], []
    rationals.extend(obj["positive_normal_balance"])
    rationals.extend(value for vertex in obj["vertices"] for value in vertex)
    rationals.extend(obj["all_original_constraint_minima"])
    for simplex in obj["simplices"]:
        rationals.extend(simplex[key] for key in ["physical_volume", "mean_gap", "max_bound", "jensen_bound"])
        rationals.extend(simplex["factor_maxima"])
        rationals.extend(simplex["gap_weighted_means"])
        integers.extend(simplex[key] for key in ["max_floor_Q96", "jensen_floor_Q96"])
    rationals.extend([obj["physical_volume"], obj["integral_gap"]])
    assert all(isinstance(s, str) and re.fullmatch(r"-?[0-9]+(?:/-?[0-9]+)?", s) for s in rationals)
    assert all(isinstance(s, str) and re.fullmatch(r"-?[0-9]+", s) for s in integers)
    node_kinds = Counter()

    def visit(item):
        node_kinds[item.kind] += 1
        for child in item.children:
            visit(child)
        for field in item.fields:
            visit(field.key)
            visit(field.value)

    visit(node)
    counts = {"top_fields": len(fields), "simplex_fields": len(simplex_fields),
              "active8": len(obj["active8_enumeration"]), "vertices": len(obj["vertices"]),
              "vertex_dimension": 8, "vertex_values": len(obj["vertex_values"]),
              "all_original_minima": len(obj["all_original_constraint_minima"]),
              "facet_vertices": len(obj["facet_vertices"]), "face_ledger": len(obj["face_ledger"]),
              "simplices": len(obj["simplices"]), "rational_occurrences": len(rationals),
              "unique_rational_strings": len(set(rationals)), "integer_occurrences": len(integers),
              "unique_integer_strings": len(set(integers))}
    measurement = {
        "schema": "p25-cell01-original-input-host-measurements-v1",
        "status": "EXACT_BYTES_MEASURED_NO_LEAN_ACCEPTANCE",
        "canonical_index": CANONICAL_INDEX, "canonical_source_id": CANONICAL_INDEX,
        "input": {"install_path": "../goldbach-research/" + INPUT_NAME, "bytes": len(raw), "sha256": INPUT_SHA},
        "references": {
            "direct_generator": {"path": str(REFERENCE_DIRECT.relative_to(REPO)), "sha256": REFERENCE_DIRECT_SHA},
            "typed_generator": {"path": str(REFERENCE_TYPED.relative_to(REPO)), "sha256": REFERENCE_TYPED_SHA},
            "donor": {"path": str(DONOR.relative_to(REPO)), "sha256": DONOR_SHA,
                      "unchanged_definitions": sorted(DONOR_NAMES)}},
        "parser": {"candidate_fuel": node.need, "value_end": node.end,
                   "tail_bytes": list(raw[node.end:]), "tail_lean": ns["quote_list"](raw[node.end:].decode("ascii")),
                   "original_length_plus_one_fuel": len(raw) + 1,
                   "farthest_scanned": planner.farthest_scanned,
                   "quoted_complete_ast_bytes": len(ns["lean_node"](node).encode()),
                   "node_kinds": dict(sorted(node_kinds.items()))},
        "fields": [{"key": field.key.scalar, "kind": field.value.kind,
                    "value_span": [field.value.start, field.value.end], "candidate_fuel": field.value.need}
                   for field in node.fields],
        "simplex_field_order": [key for key, _ in simplex_fields], "counts": counts,
        "scalar_strings": {"rational_max_length": max(map(len, rationals)),
                           "integer_max_length": max(map(len, integers)), "normalization_performed": False},
        "parse_proved": False, "typed_decode_proved": False, "finite_guards_proved": False,
        "proof_credit_from_host": False, "Lean_executed": False, "Q96_proved": False, "P2_5_proved": False}
    return raw, node, obj, ns, schemas, measurement


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True, help="Existing exact original Cell01 witness")
    args = parser.parse_args()
    *_, measurement = load_input(args.input)
    immutable(MEASUREMENTS, (json.dumps(measurement, ensure_ascii=False, indent=2) + "\n").encode())
    print(json.dumps({"measurement": str(MEASUREMENTS.relative_to(REPO)),
                      "sha256": sha(MEASUREMENTS.read_bytes()), "parser": measurement["parser"],
                      "counts": measurement["counts"], "proof_credit_from_host": False}))


if __name__ == "__main__":
    main()
