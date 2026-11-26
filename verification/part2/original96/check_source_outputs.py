"""Compare Lean's integer outputs with the frozen Python log_interval.

Use `inputs` for evaluator input, `generate-lean` for the evaluator, and
`compare` with its output. `generate` records the original Python expectations.
The finite comparison is evidence about those executions.
"""

import argparse
import ast
import hashlib
import json
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


SOURCE_SHA256 = "6e47caa91bd5e47678bcd8e2a1dc35659d25d44481c41dc437002be92d8b83dc"
SOURCE_GIT_BLOB = "ad918b5084fb83ff58d7cbb8cb23fa3e4e47ddce"
SOURCE_SIZE = 14016
DEFAULT_SOURCE = (
    Path(__file__).resolve().parents[3]
    / "docs/verification/20261126-p2-1-original96/source"
    / "corpus-renewal-paired-certificate-v2-20261010.py"
)

LEAN_EVALUATOR = """import Lean
import ImbalancedChen.Certificates.P2OriginalLog96

open ImbalancedChen.Certificates.P2OriginalLog96

def main (args : List String) : IO Unit := do
  let [inputPath] := args | throw (IO.userError "expected an input JSON path")
  let input ← IO.FS.readFile inputPath
  let parsed : Except String (Array (Array Int)) := Lean.Json.parse input >>= Lean.fromJson?
  let .ok rows := parsed | throw (IO.userError "invalid input JSON")
  let mut output : Array (Array Int) := #[]
  for row in rows do
    if row.size != 2 then
      throw (IO.userError "expected a numerator and denominator")
    let numerator := row[0]!
    let denominator := row[1]!
    if denominator <= 0 then
      throw (IO.userError "expected a positive denominator")
    let (lower, upper) := logInterval ((numerator : ℚ) / (denominator : ℚ))
    output := output.push #[numerator, denominator, lower, upper]
  IO.println (Lean.toJson output).compress
"""


def select_statement(body, kind, identifier):
    """Select exactly one named definition or assignment from a source body."""
    matches = []
    for node in body:
        if not isinstance(node, kind):
            continue
        if kind is ast.Assign:
            targets = node.targets[0]
            if isinstance(targets, ast.Tuple):
                name = tuple(element.id for element in targets.elts)
            elif isinstance(targets, ast.Name):
                name = targets.id
            else:
                continue
            if len(node.targets) != 1:
                continue
        else:
            name = node.name
        if name == identifier:
            matches.append(node)
    if len(matches) != 1:
        raise ValueError(f"expected one original {kind.__name__} for {identifier}")
    return matches[0]


def load_source(path):
    source = path.read_bytes()
    digest = hashlib.sha256(source).hexdigest()
    if len(source) != SOURCE_SIZE or digest != SOURCE_SHA256:
        raise ValueError(f"source SHA-256 mismatch: {digest} ({len(source)} bytes)")

    parsed = ast.parse(source, filename=str(path))
    oracle_statements = [
        select_statement(parsed.body, ast.Assign, "P"),
        select_statement(parsed.body, ast.Assign, "W"),
        select_statement(parsed.body, ast.FunctionDef, "floor"),
        select_statement(parsed.body, ast.FunctionDef, "ceil"),
        select_statement(parsed.body, ast.ClassDef, "Interval"),
        select_statement(parsed.body, ast.Assign, "TAIL"),
        select_statement(parsed.body, ast.FunctionDef, "log_interval"),
    ]
    builtins = {
        "__build_class__": __build_class__,
        "int": int,
        "isinstance": isinstance,
        "max": max,
        "min": min,
        "range": range,
        "str": str,
    }
    oracle = {
        "__name__": "frozen_paired_certificate",
        "__builtins__": builtins,
        "F": Fraction,
        "lru_cache": lru_cache,
    }
    exec(compile(ast.Module(oracle_statements, []), str(path), "exec", optimize=0), oracle)

    main_body = select_statement(parsed.body, ast.FunctionDef, "main").body
    grid_statements = [
        select_statement(parsed.body, ast.Assign, ("a", "h", "d", "mu", "C", "K")),
        *(select_statement(main_body, ast.Assign, name) for name in ("dt", "du", "ts", "us")),
    ]
    grid = {"__builtins__": {"range": range}, "F": Fraction}
    exec(compile(ast.Module(grid_statements, []), str(path), "exec", optimize=0), grid)
    return oracle, grid


def build_inputs(grid, suite):
    a, ts, us = (grid[key] for key in ("a", "ts", "us"))
    counts = {}
    distinct = set()

    def include(label, arguments):
        unique = set()
        occurrences = 0
        for q in arguments:
            if not 1 <= q <= 2:
                raise ValueError(f"{label} has an argument outside the original domain: {q}")
            occurrences += 1
            unique.add(q)
        counts[label] = {
            "occurrences": occurrences,
            "distinct": len(unique),
            "added": len(unique - distinct),
        }
        distinct.update(unique)

    include("boundary", (Fraction(1), Fraction(2)))
    near_boundaries = tuple(
        q for bits in (160, 224, 225) for q in (1 + Fraction(1, 2**bits), 2 - Fraction(1, 2**bits))
    )
    include("representative", (Fraction(4, 3), Fraction(3, 2), Fraction(7, 4), *near_boundaries))
    include("ts_successive_ratios", (right / left for left, right in zip(ts, ts[1:])))
    include("us_successive_ratios", (right / left for left, right in zip(us, us[1:])))
    include("us_over_a", (u / a for u in us))

    if suite == "full":
        def grid_arguments():
            # The original masks depend on external files. This geometric
            # superset uses every cell satisfying the original Z/a guards.
            for tr in ts[1:]:
                for ul, ur in zip(us, us[1:]):
                    z = min(ul, Fraction(3, 13) * (1 - tr - ur))
                    if a < z <= ul and 1 - tr - ur - Fraction(13, 3) * z >= 0:
                        yield z / a

        include("grid_Z_over_a_superset", grid_arguments())
    return sorted(distinct), counts


def expected_rows(oracle, inputs):
    log_interval = oracle["log_interval"]
    for q in inputs:
        interval = log_interval(q)
        yield [q.numerator, q.denominator, interval.lo, interval.hi]


def compare_outputs(oracle, inputs, output):
    if not isinstance(output, list) or len(output) != len(inputs):
        raise ValueError(f"Lean output mismatch: expected {len(inputs)} rows in one JSON array")
    for index, (actual, expected) in enumerate(zip(output, expected_rows(oracle, inputs))):
        if not isinstance(actual, list) or any(type(value) is not int for value in actual):
            raise ValueError(f"Lean output mismatch at row {index}: expected four JSON integers")
        if actual != expected:
            raise ValueError(f"Lean output mismatch at row {index}: expected {expected}, got {actual}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--suite", choices=("base", "full"), default="full")
    parser.add_argument("action", choices=("inputs", "generate", "generate-lean", "compare"))
    parser.add_argument("lean_output", nargs="?", type=Path, help="JSON stdout from the Lean evaluator")
    options = parser.parse_args()
    if (options.lean_output is not None) != (options.action == "compare"):
        parser.error("compare takes a Lean output path. Other actions take no path.")

    try:
        oracle, grid = load_source(options.source)
        if options.action == "generate-lean":
            print(LEAN_EVALUATOR, end="")
            return

        inputs, counts = build_inputs(grid, options.suite)
        if options.action == "inputs":
            result = [[q.numerator, q.denominator] for q in inputs]
        elif options.action == "compare":
            output_bytes = options.lean_output.read_bytes()
            compare_outputs(oracle, inputs, json.loads(output_bytes))
            result = {
                "source_sha256": SOURCE_SHA256,
                "suite": options.suite,
                "compared": len(inputs),
                "lean_output_sha256": hashlib.sha256(output_bytes).hexdigest(),
            }
        else:
            result = {
                "source_git_blob": SOURCE_GIT_BLOB,
                "source_sha256": SOURCE_SHA256,
                "source_bytes": SOURCE_SIZE,
                "suite": options.suite,
                "working_scale": oracle["W"],
                "output_scale": oracle["P"],
                "tail": oracle["TAIL"],
                "groups": counts,
                "rows": list(expected_rows(oracle, inputs)),
            }
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1

    print(json.dumps(result, separators=(",", ":")))


if __name__ == "__main__":
    sys.exit(main())
