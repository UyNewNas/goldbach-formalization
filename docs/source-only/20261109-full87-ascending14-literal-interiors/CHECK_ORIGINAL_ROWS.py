#!/usr/bin/env python3
"""Exact audit of the ORIGINAL 104 Lean literalPool and 14x96 literalIndex.

Run at repository root after checkout. This checks finite rational
geometry only, NOT Lean elaboration or saved87 numerical integration.
"""
from fractions import Fraction as F
from pathlib import Path
import re
import subprocess

SOURCE = Path("docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalAscendingFourteenAffineSource.lean")
EXPECTED_SHA = "36d9e058f2c0f8ff444413ab298608fd8125a790"
POINTS = [[1664897,984502,975844,318538,309880,301222,292564,283899],[1679079,1142733,831214,361475,336497,311519,286541,261557],[1691944,1013031,973251,400421,360640,320859,281078,241291],[1699539,1179830,788592,409587,391238,281116,262767,244411],[1723782,1075322,901893,475030,446130,272700,243800,214893],[1745789,1007937,973714,532488,498265,258677,224454,190224],[1698151,1224248,750344,473903,319362,293610,267857,242098],[1695927,1340985,649118,412480,368116,323751,279387,235016],[1707845,1217298,781253,490547,436045,381543,272531,218029],[1763838,1097340,885246,666498,454404,242310,206966,171615],[1726216,1096358,882258,573664,543082,359564,242200,211618],[1740667,1019840,972632,720827,377695,330486,236062,188854],[1812508,1110422,868746,702086,460409,429166,156239,124995],[1814286,995244,974868,534979,514602,494226,149027,128651]]
DEN = 10000000
text = SOURCE.read_text(encoding="utf-8")
actual_sha = subprocess.run(["git", "hash-object", str(SOURCE)],
    capture_output=True, text=True, check=True).stdout.strip()
assert actual_sha == EXPECTED_SHA, (actual_sha, EXPECTED_SHA)
pool_text = text.split("def literalPool", 1)[1].split("def literalIndex", 1)[0]
index_text = text.split("def literalIndex", 1)[1].split("def rows", 1)[0]
pool = [[F(z.strip()) for z in row.split(",")]
        for row in re.findall(r"!\[([^\[\]]+)\]", pool_text)]
indices = [[int(z.strip()) for z in row.split(",")]
           for row in re.findall(r"!\[([^\[\]]+)\]", index_text)]
assert len(pool) == 104 and all(len(row) == 9 for row in pool)
assert len(indices) == 14 and all(len(row) == 96 for row in indices)
assert len(POINTS) == 14 and all(len(point) == 8 for point in POINTS)
global_min, global_arg = None, None
for i, selected in enumerate(indices):
    minimum = None
    for k, pool_id in enumerate(selected):
        a = pool[pool_id]
        value = a[0] + sum((a[j + 1] * F(POINTS[i][j], DEN)
                            for j in range(8)), F(0))
        assert value >= F(1, 2000), (i, k, value)
        assert all(abs(a[j + 1]) <= F(5) for j in range(8))
        if minimum is None or value < minimum:
            minimum = value
        if global_min is None or value < global_min:
            global_min, global_arg = value, (i, k)
    print(f"ascending index={i}, original_id={i if i < 7 else i+1}, min_slack={minimum}")
assert global_min == F(1731, 2000000), (global_min,global_arg)
assert global_arg == (0, 33), global_arg
print(f"PASS: 14 x 96 = 1344 exact original affine rows; global min={global_min} at {global_arg}; radius 1/100000")
