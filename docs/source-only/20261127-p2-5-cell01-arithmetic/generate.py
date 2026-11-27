#!/usr/bin/env python3
"""Instantiate existing finite arithmetic constructions on the frozen Cell01 data."""
import argparse
import hashlib
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
INPUT_SHA = 'd7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f'
PINS = {
    'ImbalancedChen/P2Saving16Cell00StoredFloors.lean':
        'a26efccb99e0529d166c2fe91c1f4ba78840cd761893fe9c5946e3ff348d8476',
    'docs/source-only/20261126-p2-5-cell00-row00-arithmetic/ImbalancedChen/P2Saving16Cell00Row00Arithmetic.lean':
        '2d75a057eb12c8bd77ebce748646867bac202fe1cda70fe8c0236598278bee0e',
    'docs/source-only/20261126-p2-5-cell01-parser-typed/ImbalancedChen/P2Saving16Cell01TypedPayload.lean':
        '1ddf5f99c579ef2fedcf197c7b7a5f642262e905a1ad9bdec2b6f44229cc9d99',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def replace_exact(text, old, new, count):
    if text.count(old) != count:
        raise ValueError(('donor pattern differs', old, text.count(old), count))
    return text.replace(old, new)


def emit(input_path):
    raw = input_path.read_bytes()
    if len(raw) != 344873 or sha(raw) != INPUT_SHA:
        raise ValueError('original Cell01 input differs')
    donors = {}
    for path, digest in PINS.items():
        data = (REPO / path).read_bytes()
        if sha(data) != digest:
            raise ValueError('pinned existing source differs: ' + path)
        donors[path] = data.decode()
    witness = json.loads(raw)
    rows = witness['simplices']
    assert len(rows) == 81 and len(witness['vertices']) == 35
    assert len(witness['active8_enumeration']) == 495
    for i, row in enumerate(rows):
        q = Fraction(row['jensen_bound'])
        assert row['simplex_id'] == i and len(row['vertex_ids']) == 9
        assert len(row['gap_weighted_means']) == 10
        assert all(0 <= x < 35 for x in row['vertex_ids'])
        assert int(row['jensen_floor_Q96']) == q.numerator * 2**96 // q.denominator
    total = sum(int(r['jensen_floor_Q96']) for r in rows)
    assert total == 292535084187454643081

    floor = donors['ImbalancedChen/P2Saving16Cell00StoredFloors.lean']
    floor = floor.replace('Cell00', 'Cell01').replace('cell00', 'cell01')
    start = floor.index('/-!')
    stop = floor.index('-/', start) + 2
    floor = floor[:start] + '''/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original Cell01 candidate supplies 81 separate stored Jensen bounds.
Each floor uses the unchanged original q96Floor definition. The separate sum,
ordered row indices and finite shapes are checked without replacing any data.
These equations alone establish no determinant, geometric Jensen identity,
original-archive arithmetic guard, pulling ownership or integral endpoint.
-/''' + floor[stop:]
    first = floor.index('theorem simplex04_stored_jensen_floor')
    last = floor.index('theorem cell01_simplex_count')
    equations = ''.join(
        f'theorem simplex{i:02}_stored_jensen_floor :\n'
        f'    simplex{i:02}.jensenFloor = q96Floor simplex{i:02}.jensenBound := by decide +kernel\n\n'
        for i in range(81))
    floor = floor[:first] + equations + floor[last:]
    floor = replace_exact(floor, 'cell01Payload.simplices.size = 8',
                          'cell01Payload.simplices.size = 81', 2)
    floor = replace_exact(floor, 'cell01Payload.active8.size = 45',
                          'cell01Payload.active8.size = 495', 2)
    floor = replace_exact(floor, 'cell01Payload.vertices.size = 16',
                          'cell01Payload.vertices.size = 35', 1)
    floor = replace_exact(floor, '13236428172062120', str(total), 3)
    begin = floor.index('  intro s\n  fin_cases s\n')
    end = floor.index('\ntheorem cell01_stored_floor_guard', begin)
    floor = (floor[:begin] + '  intro s\n  fin_cases s\n' +
             ''.join(f'  · exact simplex{i:02}_stored_jensen_floor\n' for i in range(81)) +
             '\n' + floor[end:])
    floor = replace_exact(floor, 'Compose the eight previously checked floor equalities',
                          'Compose the 81 previously checked floor equalities', 1)
    floor_names = re.findall(r'^theorem (simplex\d\d_stored_jensen_floor)', floor, re.M)
    assert floor_names == [f'simplex{i:02}_stored_jensen_floor' for i in range(81)]

    donor_row = donors['docs/source-only/20261126-p2-5-cell00-row00-arithmetic/ImbalancedChen/P2Saving16Cell00Row00Arithmetic.lean']
    row = donor_row.replace('Cell00', 'Cell01').replace('cell00', 'cell01')
    row = replace_exact(row, '(0 : Fin 8)', '(0 : Fin 81)', 3)
    assert row.replace('Cell01', 'Cell00').replace('cell01', 'cell00').replace(
        '(0 : Fin 81)', '(0 : Fin 8)') == donor_row
    outputs = {
        'ImbalancedChen/P2Saving16Cell01StoredFloors.lean': floor.encode(),
        'ImbalancedChen/P2Saving16Cell01Row00Arithmetic.lean': row.encode(),
    }
    manifest = {
        'schema': 'p25-cell01-finite-arithmetic-pilot-v1',
        'status_at_generation': 'SOURCE_ONLY_NOT_COMPILED',
        'generator_sha256': sha(Path(__file__).read_bytes()),
        'manuscript_commit': '3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e',
        'manuscript_formula_provenance': [
            {
                'path': 'paper/release-20261106/en/argument.tex',
                'label': 'eq:current-eighth-saving',
                'formula': '4*(M-R6)/((R6-S8)*(M-S8)*product(t_i))',
            },
            {
                'path': 'paper/release-20261106/en/numerical-appendix.tex',
                'label': 'num:simplex-moment',
                'formulas': ['mean gap G/9',
                             'gap-weighted factor means (sum(f)+sum(g*f)/G)/10'],
            },
            {
                'path': 'proof-library/source/eighth-prefix-family-20261009.tex',
                'scope': 'original eight-dimensional simplex certificate',
                'formulas': ['physical volume abs(det)/8!',
                             'physical Jacobian 1', 'separate per-simplex Q96 floors'],
            },
        ],
        'source_pins': PINS,
        'input': {'file': input_path.name, 'bytes': len(raw), 'sha256': INPUT_SHA},
        'counts': {'simplices': 81, 'vertices': 35, 'active8': 495},
        'stored_jensen_floor_sum': str(total),
        'row00_vertex_ids': rows[0]['vertex_ids'],
        'row00_reverse_substitution_exact': True,
        'row00_index_annotation_replacements': 3,
        'host_floor_diagnostic_rows': 81,
        'host_diagnostics_are_formal_proofs': False,
        'outputs': [{'path': p, 'bytes': len(b), 'sha256': sha(b)} for p, b in outputs.items()],
        'all81_geometric_arithmetic_claimed': False,
        'P2_5_proved': False,
    }
    outputs['MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if __debug__ is False:
        raise RuntimeError('run without Python -O')
    outputs = emit(args.input)
    for name, raw in outputs.items():
        path = ROOT / name
        if path.exists() and path.read_bytes() != raw:
            raise ValueError('preserve differing existing output: ' + name)
        if args.check and not path.exists():
            raise ValueError('missing existing output: ' + name)
    if not args.check:
        for name, raw in outputs.items():
            path = ROOT / name
            if not path.exists():
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(raw)
    print(json.dumps({'outputs': len(outputs), 'check': args.check}))


if __name__ == '__main__':
    main()
