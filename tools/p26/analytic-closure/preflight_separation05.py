"""Find exact separating affine forms for original Cell05 simplex pairs.

This only proposes rational witnesses. It produces no Lean proof credit.
The eventual finite checker must prove every sign on the actual vertices.
"""
from fractions import Fraction as Q
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import time

SOURCE = Path('/workspace/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-05-cell.witness.json')
OUT = Path('/workspace/p26-separation05-20261128/PREFLIGHT.json')

# Proposed forms found by an advisory linear program and rational nullspace
# search. Their provenance is not trusted: all signs are checked below with
# exact fractions, and any later formal use needs its own closed Lean proof.
EXTRA_FORMS = {
    (11, 27): ['-75690173230200153/590277968787200000',
               '784053917153/184461865246', '-2720823031231/1475694921968',
               '-4196517953199/1475694921968', '0', '0', '0', '0', '1'],
    (11, 30): ['25303338067111704453323/77792329040265378000000',
               '583498586061797059/38896164520132689', '-768653014862/46119327469',
               '-50412986333703109/12965388173377563',
               '-371667008957875094/38896164520132689',
               '152710741602028802/12965388173377563', '0', '-1', '0'],
    (11, 31): ['-234355797007/2460475500000', '16358099/24604755', '1/7',
               '-4264661/8201585', '660974984917/8070384244755',
               '3280202/11480035', '-138357982407/2690128081585', '0', '1'],
}
EXTRA_FORMS[(11, 34)] = EXTRA_FORMS[(11, 31)]


def inverse(matrix):
    n = len(matrix)
    a = [list(row) + [Q(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        scale = a[j][j]
        a[j] = [x / scale for x in a[j]]
        for i in range(n):
            if i == j:
                continue
            scale = a[i][j]
            a[i] = [x - scale * y for x, y in zip(a[i], a[j])]
    return [row[n:] for row in a]


def primitive(form):
    denominator = lcm(*(x.denominator for x in form))
    values = [int(x * denominator) for x in form]
    divisor = gcd(*values)
    return tuple(x // divisor for x in values)


def main():
    started = time.monotonic()
    raw = SOURCE.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == 'e601ac9ceda569646f06a64f4baddcf9cd405cde1e377a323a238ad4e4681b82'
    data = json.loads(raw)
    points = [[Q(1)] + list(map(Q, row)) for row in data['vertices']]
    rows = [row['vertex_ids'] for row in data['simplices']]
    assert len(points) == 28 and len(rows) == 56
    facets, values = [], {}
    for row in rows:
        inv = inverse([points[i] for i in row])
        forms = [primitive([inv[j][i] for j in range(9)]) for i in range(9)]
        facets.append(forms)
        for form in forms:
            if form not in values:
                values[form] = [sum(c * x for c, x in zip(form, p)) for p in points]
    selected, pairs, missing = {}, [], []
    for r in range(56):
        for s in range(r + 1, 56):
            form = next((a for a in facets[r] if all(values[a][i] <= 0 for i in rows[s])), None)
            if form is None:
                reverse = next((a for a in facets[s] if all(values[a][i] <= 0 for i in rows[r])), None)
                if reverse is not None:
                    form = tuple(-x for x in reverse)
                    values[form] = [-x for x in values[reverse]]
            if form is None and (r, s) in EXTRA_FORMS:
                form = primitive(list(map(Q, EXTRA_FORMS[r, s])))
                values[form] = [sum(c * x for c, x in zip(form, p)) for p in points]
            if form is None:
                missing.append([r, s])
                continue
            assert any(form[1:])
            assert all(values[form][i] >= 0 for i in rows[r])
            assert all(values[form][i] <= 0 for i in rows[s])
            index = selected.setdefault(form, len(selected))
            pairs.append([r, s, index])
    result = {'schema': 'p26_cell05_separation_proposal_v1',
              'formal_acceptance': False, 'P2_6_complete': False,
              'source': {'path': str(SOURCE), 'bytes': len(raw), 'sha256': digest},
              'rows': len(rows), 'pair_count': len(pairs), 'missing': missing,
              'forms': [list(form) for form in selected], 'pairs': pairs,
              'seconds': time.monotonic() - started}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['rows', 'pair_count', 'missing', 'seconds', 'formal_acceptance']}))


if __name__ == '__main__':
    main()
