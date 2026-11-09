#!/usr/bin/env python3
"""Exact replay of original seed7, 13 winner9, fiftyAsc, fiftyDesc rows.
Run at repository root; original and new source blobs must match Git pins.
This does NOT compile Lean or replay saved87 numerical integral/gain.
"""
from fractions import Fraction as F
from pathlib import Path
import re
import subprocess

ORIG = Path("docs/source-only/20261102-resume-30r/full87_source_history/P4AOriginalSeed7Unequal15Literal.lean")
NEW = Path("docs/source-only/20261109-full87-seed-nine-fifty-original-interiors/P4AOriginalFull87SeedNineFiftyInteriors.lean")
ORIG_BLOB = "6f95442b613438fa10ac16d5ee13606f9dd3f4dc"
def git_hash(path):
    return subprocess.run(["git","hash-object",str(path)],capture_output=True,text=True,check=True).stdout.strip()
assert git_hash(ORIG) == ORIG_BLOB
orig, new = ORIG.read_text(), NEW.read_text()
def rational_rows(start,stop):
    chunk=orig.split(start,1)[1].split(stop,1)[0]
    return [[F(v.strip()) for v in m.group(1).split(",")]
            for m in re.finditer(r"!\[([^\[\]]+)\]",chunk)]
seed=rational_rows("def seed7Rows","def nineRows")
nine=rational_rows("def nineRows","def fiftyAscRows")
asc=rational_rows("def fiftyAscRows","def fiftyDescRows")
desc=rational_rows("def fiftyDescRows","\nend\nend")
cells=[seed]+[nine[97*i:97*(i+1)] for i in range(13)]+[asc,desc]
assert list(map(len,cells)) == [96]+[97]*13+[95,96]
fragment=new.split("def originalPointQ",1)[1].split("def originalPoint",1)[0]
rows=re.findall(r"!\[([^\[\]]+)\]",fragment)
assert len(rows)==16
points=[]
for row in rows:
    vals=[F(v.strip()) for v in row.split(",")]
    assert len(vals)==8 and all(x.denominator>0 for x in vals)
    points.append(vals)
minval=None;loc=None;mx=F(0);count=0
for i,(pt,rows) in enumerate(zip(points,cells)):
    for k,row in enumerate(rows):
        assert len(row)==9
        val=row[0]+sum((row[j+1]*pt[j] for j in range(8)),F(0))
        assert val>=F(7,10000),(i,k,val)
        assert all(abs(c)<=6 for c in row[1:])
        count+=1
        mx=max(mx,*(abs(c) for c in row[1:]))
        if minval is None or val<minval: minval,loc=val,(i,k)
assert count==1548 and minval==F(36321,50000000) and loc==(6,34)
assert mx==F(11,2)
print("PASS: 16 genuine original Cells / 1548 strict affine rows; original SHA matched")
print("minimum:",minval,"at",loc,"max absolute slope:",mx)
print("uniform slack >=7/10000; box radius 1/100000 leaves >=11/50000")
print("SOURCE_ONLY: NOT saved87 replay, NOT Lean compilation, NOT prime occurrence")
