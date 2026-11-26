#!/usr/bin/env python3
"""Read-only Cell01 generation consistency audit, with no Lean proof credit."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re

from measure_input import (ROOT, REPO, INPUT_SHA, MEASUREMENTS, REFERENCE_TYPED,
                           REFERENCE_TYPED_SHA, load_input, checked_bytes)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def nested_helpers(path):
    tree = ast.parse(path.read_text())
    return {node.name: ast.dump(node, include_attributes=False)
            for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)
            and node.name in {"immutable", "emit", "integer_token", "rat", "integer", "nat", "array", "rats", "naturals"}}


def location_value(obj, location):
    value = obj
    for key in location.removeprefix("/").split("/"):
        value = value[int(key)] if isinstance(value, list) else value[key]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    args = parser.parse_args()
    raw, node, obj, ns, schemas, measurements = load_input(args.input)
    assert json.loads(MEASUREMENTS.read_text()) == measurements
    checked_bytes(REFERENCE_TYPED, REFERENCE_TYPED_SHA)
    original_helpers = nested_helpers(REFERENCE_TYPED)
    actual_helpers = nested_helpers(ROOT / "generate_typed_payload.py")
    assert original_helpers == actual_helpers and len(actual_helpers) == 9
    typed = json.loads((ROOT / "TYPED_PAYLOAD_MANIFEST.json").read_text())
    parser_manifest = json.loads((ROOT / "PARSER_CANDIDATE_MANIFEST.json").read_text())
    assert typed["input"]["sha256"] == parser_manifest["input_sha256"] == INPUT_SHA
    assert typed["measurements"]["sha256"] == parser_manifest["measurement_sha256"] == digest(MEASUREMENTS.read_bytes())
    assert typed["generator_sha256"] == digest((ROOT / "generate_typed_payload.py").read_bytes())
    assert parser_manifest["generator_sha256"] == digest((ROOT / "generate_direct.py").read_bytes())
    assert typed["typed_decode_proved"] is False and typed["proof_credit_from_generator"] is False
    assert parser_manifest["parse_proved"] is False and parser_manifest["Lean_executed"] is False
    assert parser_manifest["candidate_fuel"] == 532 and parser_manifest["value_end"] == 344871
    assert parser_manifest["tail_bytes"] == [13, 10]
    for key, value in typed["counts"].items():
        assert measurements["counts"][key] == value, key
    assert [row["json_key"] for row in typed["raw_fields"]] == [key for key, _ in schemas["FIELDS"]]
    assert [row["byte_span"] for row in typed["raw_fields"]] == [[field.value.start, field.value.end] for field in node.fields]
    source = checked_bytes(REPO / typed["source"], typed["source_sha256"]).decode()
    assert len(source.encode()) == typed["source_bytes"]
    definitions = re.findall(r"(?m)^def ([A-Za-z0-9_]+) :", source)
    # The unchanged generator records emission order but serializes scalar
    # definitions before data definitions. Ownership is the complete name set.
    assert set(definitions) == set(typed["candidate_declarations"])
    assert len(typed["candidate_declarations"]) == len(set(typed["candidate_declarations"]))
    assert len(definitions) == len(set(definitions)) == typed["candidate_declaration_count"] == 3098
    assert not re.search(r"(?m)^(?:private\s+)?(?:theorem|axiom|opaque|instance)\s+", source)
    all_locations = []
    for kind in ["rational_candidates", "integer_candidates"]:
        for row in typed[kind]:
            token = row["original_string"]
            assert all(location_value(obj, site) == token for site in row["locations"])
            all_locations.extend(row["locations"])
            chars = f"def {row['chars_name']} : List Char :=\n  {ns['quote_list'](token)}\n"
            assert source.count(chars) == 1
            if kind == "rational_candidates":
                parts = token.split("/")
                assert row["numerator_string"] == parts[0]
                assert row["denominator_string"] == (parts[1] if len(parts) == 2 else None)
                assert source.count(f"def {row['name']} : ℚ :=\n  {row['lean_expression']}\n") == 1
            else:
                assert source.count(f"def {row['name']} : ℤ :=\n  {token}\n") == 1
    assert len(all_locations) == len(set(all_locations)) == 2496
    assert all(f"def rawSimplex{i:02} : SourceJson :=" in source and
               f"def simplex{i:02} : SimplexRecord :=" in source for i in range(81))
    assert "def simplex81 :" not in source and "def rawSimplex81 :" not in source
    source_rows = [{"source": typed["source"], "bytes": typed["source_bytes"], "sha256": typed["source_sha256"]}]
    for row in parser_manifest["sources"]:
        data = checked_bytes(REPO / row["source"], row["sha256"])
        assert len(data) == row["bytes"]
        if "derived_from" in row:
            original = checked_bytes(REPO / row["derived_from"]["path"], row["derived_from"]["sha256"]).decode()
            for replacement in row["parameter_substitutions"]:
                assert original.count(replacement["old"]) == replacement["count"]
                original = original.replace(replacement["old"], replacement["new"])
            assert data.decode() == "/- SOURCE ONLY / UNCOMPILED. Cell01 instance of the unchanged thin proof pattern. -/\n" + original
        else:
            assert "def rootValue : SourceJson :=\n  " + ns["lean_node"](node) + "\n" in data.decode()
            assert "theorem cell01_value532 :" in data.decode()
        assert not re.search(rb"(?m)^(?:private\s+)?(?:axiom|opaque)\s+", data)
        source_rows.append({key: row[key] for key in ["source", "bytes", "sha256"]})
    result = {"schema": "p25-cell01-source-candidate-consistency-v1", "status": "HOST_SOURCE_CONSISTENCY_PASSED",
              "checker_sha256": digest(Path(__file__).read_bytes()), "input_sha256": INPUT_SHA,
              "measurement_sha256": digest(MEASUREMENTS.read_bytes()), "unchanged_typed_helpers": sorted(actual_helpers),
              "original_fields_preserved": 17, "simplex_fields_preserved": 10, "simplex_rows_preserved": 81,
              "all_scalar_occurrences_checked_against_original_strings": len(all_locations),
              "explicit_typed_definitions": len(definitions), "complete_Lean_owned_count_known": False,
              "sources": source_rows, "Lean_executed": False, "parse_proved": False,
              "typed_decode_proved": False, "finite_guards_proved": False, "Q96_proved": False,
              "P2_5_proved": False, "proof_credit_from_host": False}
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
