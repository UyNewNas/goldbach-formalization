"""Propose exact sibling-cone forms; every assertion here is advisory only."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import time

import sympy as S

ROOT = Path('/workspace/p26-proof-continuation-20261127')
STAGE = Path('/workspace/p26-cell00-next-20261128')


def primitive(coeffs):
    scale = lcm(*(x.denominator for x in coeffs))
    values = [int(x * scale) for x in coeffs]
    divisor = gcd(*values)
    assert divisor
    return tuple(x // divisor for x in values)


def propose(source):
    started = time.monotonic()
    raw = Path(source['resolved_actual_path']).read_bytes()
    assert len(raw) == source['bytes'] and hashlib.sha256(raw).hexdigest() == source['sha256']
    data = json.loads(raw)
    vertices = [(F(1), *(F(x) for x in v)) for v in data['vertices']]
    faces = {tuple(sorted(f['vertices'])): f for f in data['face_ledger']}
    rows = {tuple(sorted(r['vertex_ids'])): i for i, r in enumerate(data['simplices'])}
    assert len(rows) == len(data['simplices'])
    nodes, pool, pool_indices, selected = [], [], {}, []

    @lru_cache(None)
    def first_simplex(face):
        if len(face) == 1:
            return face
        record = faces[face]
        p = record['pivot']
        child = next(tuple(sorted(f)) for f in record['facet_sets'] if p not in f)
        return (p, *first_simplex(child))

    def eval_at(form, v):
        return sum(a * x for a, x in zip(form, vertices[v]))

    def walk(face, ancestors):
        if len(face) == 1:
            key = tuple(sorted((*ancestors, *face)))
            assert len(key) == len(set(key)) == 9
            row = rows[key]
            selected.append(row)
            return {'row': row}
        record = faces[face]
        p = record['pivot']
        children = [tuple(sorted(f)) for f in record['facet_sets'] if p not in f]
        assert children and record['dimension'] == 8 - len(ancestors)
        child_nodes = [walk(child, (*ancestors, p)) for child in children]
        if len(children) == 1:
            return child_nodes[0]
        normalized = []
        for child in children:
            basis = (*ancestors, p, *first_simplex(child))
            assert len(basis) == len(set(basis)) == 9
            matrix = S.Matrix([[S.Rational(x.numerator, x.denominator) for x in vertices[v]] for v in basis])
            values = S.zeros(9, 1)
            values[len(ancestors)] = 1
            solution = matrix.inv(method='DM') * values
            form = tuple(F(int(x.p), int(x.q)) for x in solution)
            assert all(eval_at(form, v) == 0 for v in (*ancestors, *child))
            assert eval_at(form, p) == 1
            assert all(eval_at(form, v) >= 0 for v in face)
            normalized.append(form)
        pairs = []
        for i, left in enumerate(children):
            for j in range(i + 1, len(children)):
                right = children[j]
                separator = primitive(tuple(b - a for a, b in zip(normalized[i], normalized[j])))
                assert any(separator[1:])
                assert all(eval_at(separator, v) >= 0 for v in (*ancestors, p, *left))
                assert all(eval_at(separator, v) <= 0 for v in (*ancestors, p, *right))
                if separator not in pool_indices:
                    pool_indices[separator] = len(pool)
                    pool.append(separator)
                pairs.append([i, j, pool_indices[separator]])
        index = len(nodes)
        nodes.append({'face': list(face), 'ancestors': list(ancestors), 'pivot': p,
                      'child_faces': [list(c) for c in children],
                      'children': child_nodes, 'separators': pairs})
        return {'node': index}

    root = walk(tuple(range(len(vertices))), ())
    assert len(selected) == len(rows) and sorted(selected) == list(range(len(rows)))
    result = {'schema': 'p26_pulling_sibling_cone_advisory_v1',
              'formal_acceptance': False, 'P2_6_complete': False,
              'source': source, 'rows': len(rows), 'vertices': len(vertices),
              'root': root, 'nodes': nodes, 'forms': pool,
              'root_leaf_order': selected, 'exact_original_leaf_cover': True,
              'exact_signs_on_original_faces_and_ancestors': True,
              'seconds': time.monotonic() - started}
    out = STAGE / f'PULLING_FORMS_{source["cell"]:02d}.json'
    out.write_text(json.dumps(result, separators=(',', ':')) + '\n')
    print(json.dumps({'cell': source['cell'], 'rows': len(rows), 'branching_nodes': len(nodes),
                      'branch_pairs': sum(len(n['separators']) for n in nodes), 'forms': len(pool),
                      'seconds': result['seconds'], 'formal_acceptance': False}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--cells', default='0')
    args = parser.parse_args()
    cells = set(map(int, args.cells.split(',')))
    ledger = json.loads((ROOT / 'docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json').read_text())
    for source in ledger['all_inputs']:
        if source['family'] == 'geometry' and source['cell'] in cells:
            propose(source)
