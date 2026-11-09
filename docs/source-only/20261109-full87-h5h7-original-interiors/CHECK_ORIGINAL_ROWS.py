#!/usr/bin/env python3
"""Recheck the exact original H5/H7 literal rows in a repository checkout.
No Lean kernel check, saved87 archive replay, or arithmetic prime supply.
"""
from fractions import Fraction as F
from pathlib import Path
import re
import subprocess

ORIG = Path("docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalFirstFailureH5H7Literal.lean")
NEW = Path("docs/source-only/20261109-full87-h5h7-original-interiors/P4AOriginalFull87H5H7Interiors.lean")
EXPECTED_ORIG = "8a727a9f5c9d6de6389a821808f7d3828574ad43"
assert subprocess.run(["git", "hash-object", str(ORIG)], capture_output=True,
                      text=True, check=True).stdout.strip() == EXPECTED_ORIG
orig, new = ORIG.read_text(), NEW.read_text()
rx = r'\("[^"]*",\s*!\[([^\]]+)\]\)'
def rows(chunk):
    return [[F(x.strip()) for x in match.group(1).split(",")]
            for match in re.finditer(rx, chunk)]
h5 = rows(orig.split("def h5AffineRows", 1)[1].split("def h7AffineRows", 1)[0])
h7 = rows(orig.split("def h7AffineRows", 1)[1].split("def H5AffineGuard", 1)[0])
assert len(h5) == 700 and len(h7) == 1010
cells = [h5[i*100:(i+1)*100] for i in range(7)] + [
    h7[i*101:(i+1)*101] for i in range(10)]
part = new.split("def originalPointQ", 1)[1].split("def originalPoint", 1)[0]
point_rows = re.findall(r"!\[([^\[\]]+)\]", part)
assert len(point_rows) == 17
points = [[F(x.strip()) for x in row.split(",")] for row in point_rows]
assert all(len(pt) == 8 for pt in points)
count, minimum, at, max_slope = 0, None, None, F(0)
for i, (rs, pt) in enumerate(zip(cells, points)):
    for k, row in enumerate(rs):
        assert len(row) == 9
        v = row[0] + sum((row[j+1]*pt[j] for j in range(8)), F(0))
        assert v >= F(9,100000), (i, k, v)
        count += 1
        if minimum is None or v < minimum:
            minimum, at = v, (i, k)
        max_slope = max(max_slope, *(abs(q) for q in row[1:]))
assert count == 1710 and minimum == F(3999, 40000000) and at == (2,18)
assert max_slope == F(9,2)
print("PASS: original H5 7*100 + H7 10*101 = 1710 affine rows")
print("minimum", minimum, "at", at, "max coefficient", max_slope)
print("radius 1/1000000, conservative slope 5, box slack >= 1/20000")
print("SOURCE_ONLY, UNEVALUATED, UNCOMPILED; not original saved87/prime tuples")
