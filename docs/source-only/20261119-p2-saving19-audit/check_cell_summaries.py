#!/usr/bin/env python3
"""Compare frozen saving19 cell summaries; this does not replay witnesses."""

import argparse
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path


PINS = {
    "manifest": "fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f",
    "stage": "1629234868c4bf7becaf9836b7fff328b63f9d3559c11d9d1b40ee6b5f5ccbf0",
    "consumer": "71cb35db43b7ccfe0340a60223e080407607869c11bf75b06542bf4c5c0a1d2d",
    "review": "e3241b43644f708a37bd83ad8177ea6e3f8adcd6f44fa5f0c931964027a3e84e",
}


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in PINS:
        parser.add_argument("--" + name, required=True, type=Path)
    args = parser.parse_args()
    for name, digest in PINS.items():
        actual = hashlib.sha256(getattr(args, name).read_bytes()).hexdigest()
        require(actual == digest, f"{name} source hash {actual} != {digest}")

    manifest = json.loads(args.manifest.read_text())
    review = json.loads(args.review.read_text())
    stage = args.stage.read_text()
    consumer = args.consumer.read_text()
    match = re.search(r"def thirdRows : List MomentArchiveRow := \[(.*?)\n\]", stage, re.S)
    require(match is not None, "thirdRows definition missing")
    lines = [line for line in match.group(1).splitlines() if '⟨"t' in line]
    require(len(lines) == 13, f"expected 13 stage rows, got {len(lines)}")
    cm = re.search(r"def originalRowCount[\s\S]*?!\[([^\]]+)\]", consumer)
    require(cm is not None, "originalRowCount definition missing")
    counts = [int(part.strip()) for part in cm.group(1).split(",")]
    require(len(counts) == len(review["cells"]) == 13, "cell count")
    totals = [Fraction(0), Fraction(0), Fraction(0)]
    for i, (line, cell) in enumerate(zip(lines, review["cells"])):
        label = re.search(r'"t(\d\d)"', line)
        values = re.findall(r"\(\((\d+) : ℚ\) / (\d+)\)", line)
        require(label is not None and int(label.group(1)) == cell["cell_id"] == i,
                f"cell {i}: index mismatch")
        require(len(values) == 3 and counts[i] == cell["simplices"],
                f"cell {i}: shape or recorded count mismatch")
        values = [Fraction(int(a), int(b)) for a, b in values]
        for j, key in enumerate(("previous_gain", "new_gain", "increment")):
            require(values[j] == Fraction(cell[key]), f"cell {i}: {key} mismatch")
            totals[j] += values[j]
        require(values[0] + values[2] == values[1], f"cell {i}: replacement delta")

    names = set()
    for i in range(13):
        suffix = f"{i:02}"
        names.add(f"eighth-third-minorant-extension-20261009-a23-s23_low-{suffix}-cell.witness.json")
        names.add(f"eighth-third-moment-refinement-20261009-a23-low-{suffix}.witness.json")
    records = manifest["original_eighth_compile_input_release"]["individual_inputs"]
    selected = [r for r in records if Path(r["upstream_relative_path"]).name in names]
    require(len(selected) == 26, "26 distinct witness records required")
    found = {Path(r["upstream_relative_path"]).name: r["sha256"] for r in selected}
    require(set(found) == names, "witness names duplicate or missing")
    for name, digest in found.items():
        require(review["bindings_sha256"].get(name) == digest, f"binding {name}")

    require(sum(counts) == review["simplex_count"] == 28918, "recorded row total")
    require(review["factor_floor_count"] == 10 * sum(counts), "recorded factor total")
    for actual, key in zip(totals, ("previous_gain", "new_gain", "increment")):
        require(actual == Fraction(review[key]), f"recorded aggregate {key}")
    require(totals[0] + totals[2] == totals[1], "aggregate replacement delta")
    q96 = 2 ** 96
    require(all(q96 % value.denominator == 0 for value in totals), "Q96 denominator")
    print("PASS: 13 ordered cell counts, 39 exact rationals, 13 replacement deltas")
    print("PASS: 26 recorded witness hash bindings, 28918 recorded rows, 289180 factors")
    print("Q96 old/new/increment:", *(value.numerator * (q96 // value.denominator) for value in totals))
    print("SCOPE: summary metadata only; no witness bytes, row replay, Lean or kernel validation")


if __name__ == "__main__":
    main()
