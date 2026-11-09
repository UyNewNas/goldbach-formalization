#!/usr/bin/env python3
"""Exact replay of original H3 sourceAffineRows vs new rational centre table.
Not an original saved87 witness archive or Lean/kernel check.
Run in a complete pinned repository checkout.
"""
from pathlib import Path
from fractions import Fraction as F
import re
import subprocess

OLD = Path("docs/source-only/20261102-resume-30p/adopted87_policy/P4AOriginalFirstFailureH3Literal.lean")
NEW = Path("docs/source-only/20261109-full87-h3-original-interiors/P4AOriginalFull87H3Interiors.lean")
EXPECTED = "99fe9a071e52ff46e31a12b02bcf3d4bf9c39a85"
observed = subprocess.run(["git", "hash-object", str(OLD)],
                          text=True, capture_output=True, check=True).stdout.strip()
assert observed == EXPECTED, (observed, EXPECTED)
raw = OLD.read_text()
block = raw.split("def sourceAffineRows", 1)[1].split("def evalAffine", 1)[0]
rows = [[F(s.strip()) for s in match.group(1).split(",")]
        for match in re.finditer(r'\("[^"]+",\s*!\[([^\]]+)\]\)', block)]
assert len(rows) == 12*99 and all(len(row) == 9 for row in rows)
new = NEW.read_text()
point_block = new.split("def originalH3PointQ", 1)[1].split("def originalH3Point", 1)[0]
points = [[F(s.strip()) for s in match.group(1).split(",")]
          for match in re.finditer(r'!\[([^\[\]]+)\]', point_block)]
assert len(points) == 12 and all(len(p) == 8 for p in points)
minimum, which, slope, count = None, None, F(0), 0
for i in range(12):
    for k in range(99):
        a, t = rows[i*99+k], points[i]
        val = a[0] + sum((a[j+1]*t[j] for j in range(8)), F(0))
        assert val >= F(9, 1000000), (i, k, val)
        slope = max(slope, *(abs(x) for x in a[1:]))
        if minimum is None or val < minimum:
            minimum, which = val, (i, k)
        count += 1
assert count == 1188 and minimum == F(477,50000000) and which == (0,20)
assert slope == F(9,2)
print("PASS H3:", count, "actual strict rows; min", minimum, "at", which, "slope", slope)
print("centre 9/1000000; radius 1/100000000; box row slack 1/125000")
print("SOURCE_ONLY UNEVALUATED UNCOMPILED; no original prime witness")
