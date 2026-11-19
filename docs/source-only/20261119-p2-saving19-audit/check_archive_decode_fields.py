#!/usr/bin/env python3
"""Check the original saving19 files against the declared JSON field fragment.

Python preflight only: it does not execute Lean's parser, reduction, or kernel.
"""
import argparse
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

MANIFEST_SHA = "fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f"
PARSER_SHA = "ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424"
ARCHIVE_SHA = "b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6"
GEOMETRY = "eighth-third-minorant-extension-20261009-a23-s23_low-{:02}-cell.witness.json"
MOMENT = "eighth-third-moment-refinement-20261009-a23-low-{:02}.witness.json"


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def object_unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate key {key}")
        result[key] = value
    return result


def reject_number(token):
    raise ValueError(f"non-integer JSON token {token}")


def nat(x):
    require(type(x) is int and x >= 0, "expected JSON natural")


def integer_string(s):
    require(type(s) is str and re.fullmatch(r"-?[0-9]+", s) is not None,
            "expected integer string")
    return int(s)


def rat(s):
    require(type(s) is str and re.fullmatch(r"-?[0-9]+(?:/-?[0-9]+)?", s) is not None,
            "expected rational string")
    parts = s.split("/")
    numerator = integer_string(parts[0])
    denominator = integer_string(parts[1]) if len(parts) == 2 else 1
    require(denominator != 0, "zero denominator")
    return Fraction(numerator, denominator)


def array(xs, element):
    require(type(xs) is list, "expected JSON array")
    for x in xs:
        element(x)


def object_(x):
    require(type(x) is dict, "expected JSON object")


def vertex_values(x):
    object_(x)
    rat(x["gap"])
    array(x["factors"], rat)


def geo_row(x):
    object_(x)
    nat(x["simplex_id"])
    array(x["vertex_ids"], nat)
    for key in ("physical_volume", "mean_gap", "jensen_bound"):
        rat(x[key])
    for key in ("factor_maxima", "gap_weighted_means"):
        array(x[key], rat)
    integer_string(x["jensen_floor_Q96"])


def face(x):
    object_(x)
    array(x["vertices"], nat)
    for key in ("dimension", "pivot", "simplices"):
        nat(x[key])
    array(x["facet_sets"], lambda row: array(row, nat))


def geometry(x):
    object_(x)
    nat(x["dimension"])
    nat(x["physical_jacobian"])
    array(x["vertices"], lambda row: array(row, rat))
    array(x["vertex_values"], vertex_values)
    array(x["simplices"], geo_row)
    array(x["facet_original_indices"], nat)
    array(x["facet_vertices"], lambda row: array(row, nat))
    array(x["face_ledger"], face)


def moment_row(x):
    object_(x)
    nat(x["simplex_id"])
    array(x["log_gap_factor_floors_Q80"], integer_string)
    integer_string(x["old_floor_Q96"])
    integer_string(x["new_floor_Q96"])


def moment(x):
    object_(x)
    for key in ("cell_id", "dimension", "vertices_per_simplex", "factor_count", "log_degree", "exp_degree"):
        nat(x[key])
    require(type(x["source_witness"]) is str, "source_witness is not a string")
    integer_string(x["log_floor_denominator"])
    integer_string(x["final_floor_denominator"])
    array(x["records"], moment_row)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for x in ("manifest", "parser-source", "archive-source", "witness-dir"):
        parser.add_argument("--" + x, type=Path, required=True)
    a = parser.parse_args()
    for path, expected in ((a.manifest, MANIFEST_SHA), (a.parser_source, PARSER_SHA),
                           (a.archive_source, ARCHIVE_SHA)):
        require(sha(path) == expected, f"source digest {path}")
    manifest = json.loads(a.manifest.read_text())
    entries = {Path(x["upstream_relative_path"]).name: x for x in
               manifest["original_eighth_compile_input_release"]["individual_inputs"]}
    rows = 0
    for i in range(13):
        for name, check in ((GEOMETRY.format(i), geometry), (MOMENT.format(i), moment)):
            raw = (a.witness_dir / name).read_bytes()
            entry = entries[name]
            require(len(raw) == entry["bytes"] and hashlib.sha256(raw).hexdigest() == entry["sha256"],
                    f"file digest {name}")
            # Conservative fragment: all original bytes are ASCII and no
            # Unicode escape is present, so the Lean quoted decoder's
            # unsupported-escape branch is not silently crossed.
            require(raw.isascii() and b"\\u" not in raw, f"unsupported text {name}")
            obj = json.loads(raw, object_pairs_hook=object_unique,
                             parse_float=reject_number, parse_constant=reject_number)
            check(obj)
            if check is moment:
                rows += len(obj["records"])
        print(f"PASS cell={i:02} geometry_and_moment_fields=2", flush=True)
    require(rows == 28918, "moment record count")
    print(f"PASS files=26 moment_records={rows}")
    print("SCOPE: Python JSON and field preflight; Lean parser and kernel UNEVALUATED")


if __name__ == "__main__":
    main()
