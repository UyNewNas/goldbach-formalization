"""Propose exact original Cell00 separators; no Lean proof credit.

Linear programming only locates candidate faces. Every returned form is
checked with exact fractions before it can enter a later Lean candidate.
"""
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parents[3]
SOURCE = Path('/workspace/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json')
OUT = Path('/workspace/p26-cell00-next-20261128/SEPARATION_PROPOSAL.json')
spec = importlib.util.spec_from_file_location('p26_exact_affine_helpers',
    ROOT / 'tools/p26/analytic-closure/preflight_separation05.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)


def main():
    started = time.monotonic()
    raw = SOURCE.read_bytes()
    assert len(raw) == 195134
    assert hashlib.sha256(raw).hexdigest() == '87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691'
    data = json.loads(raw)
    points = [[Q(1)] + list(map(Q, row)) for row in data['vertices']]
    rows = [row['vertex_ids'] for row in data['simplices']]
    assert len(points) == 28 and len(rows) == 56
    facets, values = [], {}

    def value(form):
        if form not in values:
            values[form] = [sum(c * x for c, x in zip(form, p)) for p in points]
        return values[form]

    def valid(form, r, s):
        return any(form[1:]) and all(value(form)[i] >= 0 for i in rows[r]) and all(
            value(form)[i] <= 0 for i in rows[s])

    for row in rows:
        inv = helpers.inverse([points[i] for i in row])
        forms = [helpers.primitive([inv[j][i] for j in range(9)]) for i in range(9)]
        facets.append(forms)
        for form in forms:
            value(form)

    def propose_by_lp(r, s):
        import numpy as np
        import sympy as sy
        from scipy.optimize import linprog
        indices = rows[r] + rows[s]
        coordinates = [[points[i][j] for i in indices] for j in range(1, 9)]
        spans = [max(v) - min(v) for v in coordinates]
        centers = [(max(v) + min(v)) / 2 for v in coordinates]
        assert all(x > 0 for x in spans)
        normalized = [[Q(1)] + [(points[i][j + 1] - centers[j]) / spans[j]
                                 for j in range(8)] for i in indices]
        matrix = np.array([[float(x) for x in row] for row in normalized])
        constraints = np.vstack([-matrix[:9], matrix[9:], [-sum(matrix[:9]) + sum(matrix[9:])]])
        solution = linprog(np.zeros(9), A_ub=constraints, b_ub=[0.] * 18 + [-1.],
                           bounds=[(None, None)] * 9, method='highs')
        if not solution.success:
            return None
        observed = matrix @ solution.x
        original = [float(solution.x[j + 1]) / float(spans[j]) for j in range(8)]
        original = [float(solution.x[0]) - sum(original[j] * float(centers[j]) for j in range(8)), *original]
        for tolerance in [1e-7, 1e-9, 1e-11]:
            active = [i for i, x in enumerate(observed) if abs(x) < tolerance]
            exact = sy.Matrix([[sy.Rational(x.numerator, x.denominator) for x in points[indices[i]]]
                               for i in active])
            basis = [list(map(lambda x: Q(str(x)), vector)) for vector in exact.nullspace()]
            for vector in basis:
                for sign in [1, -1]:
                    form = helpers.primitive([sign * x for x in vector])
                    if valid(form, r, s):
                        return form
            _, pivots = exact.rref()
            free = [i for i in range(9) if i not in pivots]
            if len(free) != len(basis):
                continue
            for denominator in [1000, 10**6, 10**9, 10**12, 10**18]:
                weights = [Q(original[i]).limit_denominator(denominator) for i in free]
                vector = [sum(weights[j] * basis[j][i] for j in range(len(basis))) for i in range(9)]
                if not any(vector):
                    continue
                form = helpers.primitive(vector)
                if valid(form, r, s):
                    return form
        return None

    forms, pairs, missing, lp_pairs = {}, [], [], []
    for r in range(56):
        for s in range(r + 1, 56):
            form = next((a for a in facets[r] if all(value(a)[i] <= 0 for i in rows[s])), None)
            if form is None:
                reverse = next((a for a in facets[s] if all(value(a)[i] <= 0 for i in rows[r])), None)
                if reverse is not None:
                    form = tuple(-x for x in reverse)
            if form is None:
                lp_pairs.append([r, s])
                form = propose_by_lp(r, s)
            if form is None:
                missing.append([r, s])
                continue
            assert valid(form, r, s)
            index = forms.setdefault(form, len(forms))
            pairs.append([r, s, index])
    result = {'schema': 'p26_original_cell00_separation_proposal_v1',
              'formal_acceptance': False, 'P2_6_complete': False,
              'source': {'path': str(SOURCE), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()},
              'rows': 56, 'vertices': 28, 'pair_count': len(pairs), 'missing': missing,
              'lp_proposed_pairs': lp_pairs, 'forms': [list(a) for a in forms], 'pairs': pairs,
              'seconds': time.monotonic() - started}
    OUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'pair_count': len(pairs), 'missing': missing, 'forms': len(forms),
                      'lp_pairs': len(lp_pairs), 'seconds': result['seconds'], 'formal_acceptance': False}))


if __name__ == '__main__':
    main()
