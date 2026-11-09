#!/usr/bin/env python3
"""Replay ORIGINAL descending15 + ascendingPair13 literal coefficients and
new centre points. Exact Fraction arithmetic, not a Lean/kernel/saved87 check.
Run from repository root, with pins unchanged.
"""
from fractions import Fraction as F
from pathlib import Path
import re
import subprocess

DIR = Path("docs/source-only/20261109-full87-desc15-ascpair13-original-interiors")
NEW = DIR / "P4AOriginalFull87DescAscPairInteriors.lean"
ORIGINALS = [
    ("ImbalancedChen/OriginalDescendingFifteenLiteralAffineRows.lean",
     "817b4c8c98ff24864a2eb414721b5e7390d7b459", 15, 96,
     "originalDescPointQ", "originalDescPoint"),
    ("ImbalancedChen/OriginalAscendingThirteenLiteralAffineRows.lean",
     "48b4f14ec8baf09b9760289f65a7385bf6595e9e", 13, 97,
     "originalPairPointQ", "originalPairPoint"),
]
rx = re.compile(r"!\[([^\[\]]+)\]")
def parse_matrix(block):
    return [[F(s.strip()) for s in match.group(1).split(",")]
            for match in rx.finditer(block)]

source = NEW.read_text()
total, minimum, at, slope = 0, None, None, F(0)
for family, (path, expected, ni, nr, begin, end) in enumerate(ORIGINALS):
    original = Path(path)
    observed = subprocess.run(["git", "hash-object", str(original)],
                              capture_output=True, text=True, check=True).stdout.strip()
    assert observed == expected, (path, observed)
    raw = original.read_text()
    pool = parse_matrix(raw.split("def literalPool", 1)[1].split("def literalIndex", 1)[0])
    index = parse_matrix(raw.split("def literalIndex", 1)[1].split("def exportedCoefficients", 1)[0])
    point = parse_matrix(source.split("def "+begin, 1)[1].split("def "+end, 1)[0])
    assert len(index) == len(point) == ni
    for i, (ix, t) in enumerate(zip(index, point)):
        assert len(ix) == nr and len(t) == 8
        for j, r in enumerate(ix):
            a = pool[int(r)]
            assert len(a) == 9
            z = a[0] + sum((a[k+1]*t[k] for k in range(8)), F(0))
            assert z >= F(9, 1000000), (family, i, j, z)
            slope = max(slope, *(abs(v) for v in a[1:]))
            if minimum is None or z < minimum:
                minimum, at = z, (family, i, j)
            total += 1
assert total == 2701 and minimum == F(289, 25000000) and at == (1, 0, 19)
assert slope == F(11, 2)
print("PASS: original 15*96 + 13*97 = 2701 strict rows")
print("minimum", minimum, "at (family,cell,row)", at, "max slope", slope)
print("centre >= 9/1000000, radius 1/100000000, retained slack 1/125000")
print("SOURCE_ONLY / UNEVALUATED / UNCOMPILED; no saved87 arithmetic witness")
