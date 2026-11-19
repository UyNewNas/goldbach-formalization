#!/usr/bin/env python3
"""Exact arithmetic check of the source's original_polynomial_faces data.

Uses source-bound homogeneous points and the negative monomial -X^vertex_id.
This is not Lean compilation, kernel replay, or a proof of the consumer.
"""
import argparse
import hashlib
import json
from fractions import Fraction
from math import lcm
from pathlib import Path
from sympy.polys.domains import ZZ
from sympy.polys.matrices import DomainMatrix

MANIFEST_SHA = "fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f"
SOURCE_SHA = "87fd625fc864128a001ba49deab415fd82eb944ee3c23bda036762c199f94dde"
NAME = "eighth-third-minorant-extension-20261009-a23-s23_low-{:02}-cell.witness.json"


def require(condition, reason):
    if not condition:
        raise SystemExit("FAIL: " + reason)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for x in ("manifest", "source", "witness-dir"):
        ap.add_argument("--" + x, type=Path, required=True)
    ap.add_argument("--cell", type=int, choices=range(13))
    ap.add_argument("--limit", type=int)
    args = ap.parse_args()
    require(digest(args.manifest) == MANIFEST_SHA, "manifest SHA-256")
    require(digest(args.source) == SOURCE_SHA, "Lean source SHA-256")
    manifest = json.loads(args.manifest.read_text())
    records = {Path(x["upstream_relative_path"]).name: x for x in
               manifest["original_eighth_compile_input_release"]["individual_inputs"]}
    cells = range(13) if args.cell is None else [args.cell]
    total_rows = total_off = 0
    for cell in cells:
        name = NAME.format(cell)
        path = args.witness_dir / name
        rec = records[name]
        require(path.stat().st_size == rec["bytes"] and digest(path) == rec["sha256"],
                f"cell {cell}: geometry source")
        obj = json.loads(path.read_text())
        vertices = [list(map(Fraction, v)) for v in obj["vertices"]]
        require(all(len(v) == 8 for v in vertices), f"cell {cell}: vertex dimension")
        scales = [lcm(*(v[j].denominator for v in vertices)) for j in range(8)]
        coords = [[1] + [v[j].numerator * (scales[j] // v[j].denominator)
                         for j in range(8)] for v in vertices]
        n = 0
        off = 0
        for sid, row in enumerate(obj["simplices"]):
            if args.limit is not None and sid >= args.limit:
                break
            ids = row["vertex_ids"]
            require(row["simplex_id"] == sid and len(ids) == len(set(ids)) == 9 and
                    all(0 <= k < len(vertices) for k in ids), f"cell {cell} row {sid}: shape")
            matrix = [coords[k] for k in ids]
            inv, den = DomainMatrix.from_list(matrix, ZZ).inv_den()
            inverse = [[int(v) for v in line] for line in inv.to_list()]
            den = int(den)
            require(den != 0, f"cell {cell} row {sid}: determinant")
            if den < 0:
                inverse = [[-x for x in line] for line in inverse]
                den = -den
            # Check the full inverse identity, giving the own-vertex polynomial
            # identities independently of the matrix inversion implementation.
            for i in range(9):
                for k in range(9):
                    require(sum(matrix[i][j] * inverse[j][k] for j in range(9)) ==
                            (den if i == k else 0), f"cell {cell} row {sid}: inverse")
            present = set(ids)
            for v, point in enumerate(coords):
                if v in present:
                    continue
                # h(v)-plane(v) = sum_k lambda_k X^(ids[k]) - X^v.
                # Distinct exponents imply the leading coefficient is the
                # first nonzero value while scanning descending vertex IDs.
                terms = sorted([(vid, k) for k, vid in enumerate(ids)] + [(v, -1)], reverse=True)
                for exponent, k in terms:
                    coeff = -den if k == -1 else sum(point[j] * inverse[j][k] for j in range(9))
                    if coeff:
                        require(coeff > 0, f"cell {cell} row {sid} vertex {v}: "
                                f"negative leading coefficient at {exponent}")
                        break
                else:
                    require(False, f"cell {cell} row {sid} vertex {v}: zero polynomial")
                off += 1
            n += 1
        total_rows += n
        total_off += off
        print(f"PASS cell={cell:02} rows={n} own_identities={9*n} off_vertex_leading={off}", flush=True)
    if args.cell is None and args.limit is None:
        require(total_rows == 28918, "global row count")
        print(f"PASS total rows={total_rows} own_identities={9*total_rows} off_vertex_leading={total_off}")
    print("SCOPE: exact rational data only; no Lean, kernel, null-overlap or prime-history acceptance")


if __name__ == "__main__":
    main()
