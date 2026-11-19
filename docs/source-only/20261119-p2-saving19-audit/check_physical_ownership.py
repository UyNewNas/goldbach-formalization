#!/usr/bin/env python3
"""Check source-pinned 13-cell physical, gate, and pulling ledger data.

Exact arithmetic data check only; it is not Lean, kernel replay, a proof of
strict membership, null overlap, polynomial lifting, or prime chronology.
"""
import argparse
import hashlib
import json
import re
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

MANIFEST_SHA = "fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f"
COEFFICIENTS_SHA = "129e18e8683582b2e0f8438e9baca31bec1e4b3551273ee079b35007fb55e592"
NAME = "eighth-third-minorant-extension-20261009-a23-s23_low-{:02}-cell.witness.json"


def require(condition, reason):
    if not condition:
        raise SystemExit("FAIL: " + reason)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def vectors(source, start, end, count, width, pattern):
    segment = source.split(start, 1)[1].split(end, 1)[0]
    raw = re.findall(r"!\[([^\[\]]+)\]", segment)
    require(len(raw) == count, f"{start} vector count")
    output = []
    for row in raw:
        fields = [x.strip() for x in row.split(",")]
        require(len(fields) == width and all(re.fullmatch(pattern, x) for x in fields),
                f"{start} field shape")
        output.append(fields)
    return output


def physical(t):
    third = (1 + t[1] + t[2]) / 2
    old = (1 + t[0] + t[3]) / 2
    new = (1 + t[1] + t[3] + t[7]) / 2 - Q(1, 1000000)
    return (all(t[i] >= t[j] for i in range(8) for j in range(i, 8)) and
            t[7] >= Q(53, 13824) and t[2] >= Q(1, 100) and t[0] <= Q(25, 128) and
            t[1] + t[2] <= Q(25, 128) and t[0] + t[3] <= Q(25, 128) and
            t[1] + t[3] + t[7] <= Q(25, 128) and 3*t[0] <= third and
            t[0] + t[1] + 3*t[2] <= third and
            t[0] + t[1] + t[2] + t[3] + 3*t[4] <= third and
            sum(t[:6]) + 3*t[6] <= third and third <= old <= new and
            new - sum(t) <= 3*t[7])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for x in ("manifest", "coefficients", "witness-dir"):
        p.add_argument("--" + x, type=Path, required=True)
    a = p.parse_args()
    require(sha(a.manifest) == MANIFEST_SHA and sha(a.coefficients) == COEFFICIENTS_SHA,
            "manifest / source digest")
    manifest = json.loads(a.manifest.read_text())
    records = {Path(x["upstream_relative_path"]).name: x for x in
               manifest["original_eighth_compile_input_release"]["individual_inputs"]}
    src = a.coefficients.read_text()
    pool = [[Q(x) for x in row] for row in vectors(src, "def literalPool", "def literalIndex",
            103, 9, r"-?\d+(?:/\d+)?")]
    index = [[int(x) for x in row] for row in vectors(src, "def literalIndex",
             "def exportedCoefficients", 13, 97, r"\d+")]
    require(all(0 <= i < 103 for row in index for i in row), "coefficient index range")
    require("literalPool (literalIndex i r)" in src, "exported coefficient definition")
    totals = [0, 0, 0, 0]
    for cid in range(13):
        name = NAME.format(cid)
        witness = a.witness_dir / name
        rec = records[name]
        require(witness.stat().st_size == rec["bytes"] and sha(witness) == rec["sha256"],
                f"cell {cid} geometry digest")
        data = json.loads(witness.read_text())
        points = [tuple(map(Q, v)) for v in data["vertices"]]
        rows = data["simplices"]
        require(all(len(v) == 8 and physical(v) for v in points), f"cell {cid} physical")
        slacks = []
        for k, ix in enumerate(index[cid]):
            coeff = pool[ix]
            require(any(coeff[1:]), f"cell {cid} gate {k}: proper")
            vals = [coeff[0] + sum((coeff[j+1] * v[j] for j in range(8)), Q())
                    for v in points]
            require(all(x >= 0 for x in vals), f"cell {cid} gate {k}: nonnegative")
            slacks.append(vals)
        facets = data["facet_vertices"]
        for f, ids in enumerate(facets):
            require(len(ids) == len(set(ids)) and all(0 <= x < len(points) for x in ids),
                    f"cell {cid} facet {f}: vertex IDs")
            target = set(ids)
            require(any({v for v, value in enumerate(vals) if value == 0} == target
                        for vals in slacks), f"cell {cid} facet {f}: gate")
        faces = data["face_ledger"]
        fmap = {tuple(f["vertices"]): f for f in faces}
        require(len(fmap) == len(faces), f"cell {cid}: duplicate face")
        @lru_cache(None)
        def pulling(n, face):
            if n == 0:
                return ()
            if len(face) == 1:
                return (face,)
            if face not in fmap:
                return ()
            f = fmap[face]
            return tuple((f["pivot"],) + row for s in f["facet_sets"]
                         if f["pivot"] not in s for row in pulling(n-1, tuple(s)))
        for fi, face in enumerate(faces):
            verts = face["vertices"]
            vs = set(verts)
            pivot = face["pivot"]
            require(len(vs) == len(verts) > 1 and pivot in vs and pivot == max(vs),
                    f"cell {cid} face {fi}: pivot")
            intersections = {frozenset(vs.intersection(f)) for f in facets}
            intersections.discard(frozenset())
            intersections.discard(frozenset(vs))
            maximal = {x for x in intersections if not any(x < y for y in intersections)}
            require({frozenset(s) for s in face["facet_sets"]} == maximal,
                    f"cell {cid} face {fi}: maximal facets")
            require(len(pulling(face["dimension"] + 1, tuple(verts))) == face["simplices"],
                    f"cell {cid} face {fi}: simplex count")
        actual = tuple(tuple(r["vertex_ids"]) for r in rows)
        require(pulling(9, tuple(range(len(points)))) == actual, f"cell {cid}: pulling order")
        require(len({frozenset(r) for r in actual}) == len(rows), f"cell {cid}: distinct sets")
        totals = [totals[0] + len(points), totals[1] + len(points)*97,
                  totals[2] + len(rows), totals[3] + len(faces)]
        print(f"PASS cell={cid:02} vertices={len(points)} gate_evals={len(points)*97} "
              f"faces={len(faces)} facets={len(facets)} rows={len(rows)}", flush=True)
    require(totals[2] == 28918, "row count")
    print(f"PASS total vertices={totals[0]} gate_evals={totals[1]} faces={totals[3]} rows={totals[2]}")
    print("SCOPE: exact data check; no Lean, kernel, strict membership, null overlap, or prime history")


if __name__ == "__main__":
    main()
