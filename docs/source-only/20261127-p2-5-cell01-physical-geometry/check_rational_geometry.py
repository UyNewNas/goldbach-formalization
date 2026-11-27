"""Check the four original Cell01 guards with exact rationals; print JSON."""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import re


def coefficients(text):
    return tuple(Fraction(component.strip()) for component in text.split(","))


def physical_rows(repo):
    base = (repo / "ImbalancedChen/P4AOriginalAscendingCell0Literal96.lean").read_text()
    branch = (repo / "ImbalancedChen/P4AOriginalAscendingCell1Affine.lean").read_text()
    block = base.split("def rows :", 1)[1].split("def sourceRows", 1)[0]
    rows = [coefficients(vector) for vector in re.findall(r'\("[^"]+", !\[([^\]]+)\]\)', block)]
    block = branch.split("def rows1 ", 1)[1].split("abbrev sourceRow", 1)[0]
    match = re.search(r'if k = (\d+) then\s*\("[^"]+", !\[([^\]]+)\]\)\s*else P4AOriginalAscendingCell0Literal96.rows k', block)
    assert match and int(match[1]) == 90 and len(rows) == 96
    old_row = rows[90]
    rows[90] = coefficients(match[2])
    assert rows[90] != old_row and all(len(row) == 9 for row in rows)
    return rows


def evaluate(row, point):
    return row[0] + sum(a * b for a, b in zip(row[1:], point, strict=True))


def check(repo, witness):
    data = witness.read_bytes()
    digest = sha256(data).hexdigest()
    assert digest == "d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f"
    w = json.loads(data)
    vertices = [tuple(map(Fraction, v)) for v in w["vertices"]]
    ids = w["facet_original_indices"]
    weights = list(map(Fraction, w["positive_normal_balance"]))
    faces = w["facet_vertices"]
    assert w["cell_id"] == 1 and w["dimension"] == 8 and w["physical_jacobian"] == 1
    assert len(w["simplices"]) == 81 and len(vertices) == 35 and all(len(v) == 8 for v in vertices)
    simplex = w["simplices"][0]["vertex_ids"]
    assert len(simplex) == 9 and all(0 <= v < len(vertices) for v in simplex)
    center = tuple(sum(vertices[v][j] for v in simplex) / 9 for j in range(8))
    rows = physical_rows(repo)
    margins = [evaluate(row, center) for row in rows]
    values = [[evaluate(row, vertex) for row in rows] for vertex in vertices]
    assert min(margins) > 0 and all(x >= 0 for v in values for x in v)
    assert len(weights) == len(faces) == len(ids) == 12 and all(0 <= k < 96 for k in ids)
    assert min(weights) > 0
    balances = [sum(weight * rows[k][j + 1] for k, weight in zip(ids, weights, strict=True))
                for j in range(8)]
    assert balances == [0] * 8
    for k, face in zip(ids, faces, strict=True):
        for i, vertex_values in enumerate(values):
            assert (i in face) == (vertex_values[k] == 0)
    return {"status": "PASS_HOST_EXACT_RATIONAL_ONLY", "witness_sha256": digest,
            "facet_ids": ids, "vertices": len(vertices), "simplices": len(w["simplices"]),
            "first_simplex_vertex_ids": simplex, "center_rows": len(margins),
            "center_minimum": str(min(margins)), "center_minimum_at_rows":
            [k for k,x in enumerate(margins) if x == min(margins)],
            "cell01_row90_center_slack": str(margins[90]), "vertex_row_checks": len(values)*len(rows),
            "vertex_row_zeros": sum(x == 0 for v in values for x in v), "vertex_row_negatives": 0,
            "positive_weights": len(weights), "minimum_weight": str(min(weights)),
            "normal_balance_components": list(map(str, balances)), "incidence_iff_checks": len(faces)*len(vertices),
            "incidence_disagreements": 0, "lean_executions": 0}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", type=Path)
    args = parser.parse_args()
    print(json.dumps(check(Path(__file__).resolve().parents[3], args.witness), indent=2))
