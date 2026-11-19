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

INDEX_PINS = {
    "fourteen": "e5e7c88c94e3debd43ad523ecdcafcf3878852414f473037328761b0d73e5aaa",
    "dictionary": "dbfadaa879e08c2c3ecb270f699b84f3f9ac7b0b044ba96be8046da4a73c501c",
    "sourceindex": "a003919a12b213dd2a979fe07e7376ec3e619d24f704faacf5c5430b3ed009f1",
}


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def check_source_indices(stage, fourteen, dictionary, sourceindex):
    """Check the literal frozen archive layout, not N-dependent occurrences."""
    ids_match = re.search(r"def originalId : Fin 14 → ℕ := !\[([^\]]+)\]", fourteen)
    require(ids_match is not None, "originalId definition missing")
    ids = [int(x.strip()) for x in ids_match.group(1).split(",")]
    require(len(ids) == len(set(ids)) == 14, "fourteen ID cardinality")
    require(set(ids) == (set(range(15)) - {7}), "fourteen/radial ID partition")

    dictionary_flat = "".join(dictionary.split())
    for code in (
        "|.remaining(.ascendingi)=>⟨P4AOriginalAscendingFourteenAffineSource.originalIdi,byfin_casesi<;>decide⟩",
        "|.remaining.seed=>7",
        "|.ascendingPairi=>⟨45+i.val,byomega⟩",
    ):
        require(code in dictionary_flat, "globalIndex definition changed")
    index_flat = "".join(sourceindex.split())
    require("defunequalSourceOrder:ListMomentArchiveRow:="
            "((unequalRows.drop1).take11)++(unequalRows.take1)++(unequalRows.drop12)" in index_flat,
            "unequal source order changed")
    require("defsourceIndexedRecords:List(String×ℚ):="
            "(ascendingRows.take7)++[(\"a07-radial-whole\",radialWhole)]++"
            "(ascendingRows.drop7)++descendingRows++"
            "(unequalSourceOrder.map(funr=>(r.label,r.final)))++"
            "(thirdRows.map(funr=>(r.label,r.final)))++"
            "(historyRows.map(funr=>(r.label,r.final)))" in index_flat,
            "source-index archive layout changed")

    def labels(name):
        match = re.search(r"def " + name + r"[^\n]*:= \[(.*?)\n\]", stage, re.S)
        require(match is not None, f"{name} definition missing")
        return re.findall(r'"([^\"]+)"', match.group(1))

    ascending, descending, unequal, third, history = (
        labels(name) for name in
        ("ascendingRows", "descendingRows", "unequalRows", "thirdRows", "historyRows")
    )
    require(list(map(len, (ascending, descending, unequal, third, history))) ==
            [14, 15, 15, 13, 29], "stage label counts changed")
    records = (ascending[:7] + ["a07-radial-whole"] + ascending[7:] + descending +
               unequal[1:12] + unequal[:1] + unequal[12:] + third + history)
    require(len(records) == len(set(records)) == 87, "archive label multiplicity")
    for i, index in enumerate(ids):
        require(records[index] == f"a{index:02}", f"fourteen original index {i}")
    require(records[7] == "a07-radial-whole", "radial position")
    for i in range(13):
        require(records[45 + i] == f"t{i:02}", f"thirteen original index {i}")
    print("PASS: original fourteen indices, single radial index 7, thirteen indices 45–57")
    print("SCOPE: 87 archive labels only; no policy order, prime occurrences or simplex rows")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in PINS:
        parser.add_argument("--" + name, required=True, type=Path)
    for name in INDEX_PINS:
        parser.add_argument("--" + name, type=Path)
    args = parser.parse_args()
    chosen = [getattr(args, name) is not None for name in INDEX_PINS]
    require(not any(chosen) or all(chosen), "supply all three source-index inputs or none")
    pins = PINS | (INDEX_PINS if all(chosen) else {})
    for name, digest in pins.items():
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
    if all(chosen):
        check_source_indices(stage, args.fourteen.read_text(), args.dictionary.read_text(),
                             args.sourceindex.read_text())


if __name__ == "__main__":
    main()
