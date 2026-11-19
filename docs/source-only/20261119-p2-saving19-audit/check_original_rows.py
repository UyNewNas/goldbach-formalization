#!/usr/bin/env python3
"""Replay saving19 witness row/factor arithmetic with the pinned independent engine.

This does not check polytope coverage, actual prime occurrences, Lean
elaboration, kernel replay, or any transitive axioms.
"""

import argparse
import hashlib
import importlib.util
import json
from fractions import Fraction
from math import factorial, lcm
from pathlib import Path


MANIFEST_SHA = "fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f"
REVIEW_SHA = "e3241b43644f708a37bd83ad8177ea6e3f8adcd6f44fa5f0c931964027a3e84e"
ENGINE_SHA = "5e778995582ddf49d87e023edf4558fe6cceeecaf5a823e94c7970367d53e520"
GEOMETRY = "eighth-third-minorant-extension-20261009-a23-s23_low-{:02}-cell.witness.json"
MOMENT = "eighth-third-moment-refinement-20261009-a23-low-{:02}.witness.json"


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def physical_simplex_volume(points):
    """Compute the eight-dimensional simplex volume by exact Bareiss elimination."""
    require(len(points) == 9 and all(len(p) == 8 for p in points), "simplex shape")
    base, columns, scale = points[0], [], 1
    for point in points[1:]:
        difference = [point[k] - base[k] for k in range(8)]
        denominator = lcm(*(x.denominator for x in difference))
        scale *= denominator
        columns.append([x.numerator * (denominator // x.denominator) for x in difference])
    matrix = [[columns[j][i] for j in range(8)] for i in range(8)]
    previous = 1
    for k in range(7):
        if matrix[k][k] == 0:
            row = next((r for r in range(k + 1, 8) if matrix[r][k]), None)
            if row is None:
                return Fraction(0)
            matrix[k], matrix[row] = matrix[row], matrix[k]
        pivot = matrix[k][k]
        for i in range(k + 1, 8):
            for j in range(k + 1, 8):
                numerator = matrix[i][j] * pivot - matrix[i][k] * matrix[k][j]
                quotient, remainder = divmod(numerator, previous)
                require(remainder == 0, "non-exact Bareiss division")
                matrix[i][j] = quotient
            matrix[i][k] = 0
        previous = pivot
    return Fraction(abs(matrix[7][7]), factorial(8) * scale)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("manifest", "review", "engine", "witness-dir"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    for path, expected in ((args.manifest, MANIFEST_SHA), (args.review, REVIEW_SHA),
                           (args.engine, ENGINE_SHA)):
        require(digest(path) == expected, f"source digest {path}")
    manifest = json.loads(args.manifest.read_text())
    review = json.loads(args.review.read_text())
    records = manifest["original_eighth_compile_input_release"]["individual_inputs"]
    expected = {Path(r["upstream_relative_path"]).name: r for r in records}
    names = [n for i in range(13) for n in (GEOMETRY.format(i), MOMENT.format(i))]
    require(len(set(names)) == 26, "witness naming")
    for n in names:
        r = expected[n]
        p = args.witness_dir / n
        require(p.stat().st_size == r["bytes"] and digest(p) == r["sha256"], f"witness {n}")
        require(review["bindings_sha256"][n] == r["sha256"], f"review binding {n}")

    spec = importlib.util.spec_from_file_location("pinned_moment_engine", args.engine)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    engine.beta_checks()
    require(len(review["cells"]) == 13, "review cell count")
    total_rows = 0
    total_old = total_new = 0
    all_stream = hashlib.sha256()
    for cid in range(13):
        geo = json.loads((args.witness_dir / GEOMETRY.format(cid)).read_text())
        mom = json.loads((args.witness_dir / MOMENT.format(cid)).read_text())
        cell = review["cells"][cid]
        require(cell["cell_id"] == mom["cell_id"] == cid, f"cell {cid}: id")
        require(mom["source_witness"] == GEOMETRY.format(cid), f"cell {cid}: source")
        require(geo["dimension"] == mom["dimension"] == 8 and
                geo["physical_jacobian"] == 1 and mom["vertices_per_simplex"] == 9 and
                mom["factor_count"] == 10 and mom["log_degree"] == 6 and
                mom["exp_degree"] == 3 and int(mom["log_floor_denominator"]) == 2**80 and
                int(mom["final_floor_denominator"]) == 2**96, f"cell {cid}: header")
        vertices = geo["vertices"]
        values = geo["vertex_values"]
        require(len(vertices) == len(values), f"cell {cid}: vertices")
        physical = []
        coordinates = []
        for vi, (coord, saved) in enumerate(zip(vertices, values)):
            require(len(coord) == 8 and len(saved["factors"]) == 10, f"cell {cid} vertex {vi}: shape")
            point = tuple(map(Fraction, coord))
            gap, factors = engine.density("nine_ascending", point)
            require(gap == Fraction(saved["gap"]) and list(factors) ==
                    list(map(Fraction, saved["factors"])), f"cell {cid} vertex {vi}: factors")
            physical.append((gap, factors))
            coordinates.append(point)
        grow, mrow = geo["simplices"], mom["records"]
        require(len(grow) == len(mrow) == cell["simplices"], f"cell {cid}: row count")
        old = new = 0
        stream = hashlib.sha256()
        for sid, (g, m) in enumerate(zip(grow, mrow)):
            tag = f"cell {cid} row {sid}"
            require(g["simplex_id"] == m["simplex_id"] == sid, f"{tag}: index")
            ids = g["vertex_ids"]
            require(len(ids) == len(set(ids)) == 9 and all(0 <= k < len(vertices) for k in ids),
                    f"{tag}: ordered vertex ids")
            require(len(g["factor_maxima"]) == len(g["gap_weighted_means"]) ==
                    len(m["log_gap_factor_floors_Q80"]) == 10, f"{tag}: factor shape")
            require(Fraction(g["mean_gap"]) == sum((physical[k][0] for k in ids), Fraction()) / 9,
                    f"{tag}: mean gap")
            for j in range(10):
                require(Fraction(g["factor_maxima"][j]) == max(physical[k][1][j] for k in ids),
                        f"{tag}: factor {j} maximum")
            volume = physical_simplex_volume([coordinates[k] for k in ids])
            require(volume > 0 and volume == Fraction(g["physical_volume"]), f"{tag}: physical volume")
            calculated = engine.simplex(physical, ids, volume)
            require(calculated["means"] == list(map(Fraction, g["gap_weighted_means"])),
                    f"{tag}: gap-weighted factor means")
            require(calculated["old_exact"] == Fraction(g["jensen_bound"]) and
                    calculated["old_floor"] == int(g["jensen_floor_Q96"]) == int(m["old_floor_Q96"]),
                    f"{tag}: old Q96")
            require(calculated["factor_floors"] == list(map(int, m["log_gap_factor_floors_Q80"])) and
                    calculated["new_floor"] == int(m["new_floor_Q96"]), f"{tag}: Q80/Q96")
            old += calculated["old_floor"]
            new += calculated["new_floor"]
            line = (str(sid) + ":" + ",".join(map(str, calculated["factor_floors"])) + ":" +
                    str(calculated["old_floor"]) + ":" + str(calculated["new_floor"]) + "\n")
            stream.update(line.encode())
            all_stream.update((str(cid) + ":" + line).encode())
        require(stream.hexdigest() == cell["stream_sha256"], f"cell {cid}: stream")
        require(Fraction(old, 2**96) == Fraction(cell["previous_gain"]) and
                Fraction(new, 2**96) == Fraction(cell["new_gain"]) and
                Fraction(new - old, 2**96) == Fraction(cell["increment"]), f"cell {cid}: totals")
        total_rows += len(grow)
        total_old += old
        total_new += new
        print(f"PASS cell={cid:02} rows={len(grow)} factors={10 * len(grow)}", flush=True)
    require(total_rows == review["simplex_count"] == 28918 and
            10 * total_rows == review["factor_floor_count"] == 289180, "global row count")
    require(all_stream.hexdigest() == review["stream_sha256"], "global stream")
    require(Fraction(total_old, 2**96) == Fraction(review["previous_gain"]) and
            Fraction(total_new, 2**96) == Fraction(review["new_gain"]) and
            Fraction(total_new - total_old, 2**96) == Fraction(review["increment"]), "global totals")
    print(f"PASS total rows={total_rows} factor_floors={10 * total_rows} stream={all_stream.hexdigest()}")
    print(f"Q96 old={total_old} new={total_new} increment={total_new - total_old}")
    print("SCOPE: exact data arithmetic only; no coverage, prime occurrence, Lean or kernel check")


if __name__ == "__main__":
    main()
