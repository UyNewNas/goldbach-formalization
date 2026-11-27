"""Advisory exact-rational replay of the original Cell05 frozen evaluator.

This is an independent computational preflight, not a Lean certificate. Every
record equality still needs its parser-bound kernel proof and real semantics.
"""
from fractions import Fraction as Q
import hashlib
import json
from math import comb, prod
from pathlib import Path
import time

DATA = Path('/workspace/goldbach-research')
OUT = Path('/workspace/p26-numeric05-20261128')
FILES = [
    ('geometry', 'eighth-third-minorant-extension-20261009-a23-s23_low-05-cell.witness.json',
     'e601ac9ceda569646f06a64f4baddcf9cd405cde1e377a323a238ad4e4681b82'),
    ('moments', 'eighth-third-moment-refinement-20261009-a23-low-05.witness.json',
     '9a85e92f79b24c2b2361717d3a29ecb6167059e5509211c2f3fb290b5284fe2c'),
]


def fixed(bits, value):
    return value.numerator * (1 << bits) // value.denominator


def main():
    started = time.monotonic()
    parsed, sources = {}, {}
    for tag, name, expected in FILES:
        path = DATA / name
        raw = path.read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        assert actual == expected
        parsed[tag] = json.loads(raw)
        sources[tag] = {'path': str(path), 'bytes': len(raw), 'sha256': actual}
    geometry, moments = parsed['geometry'], parsed['moments']
    assert moments['cell_id'] == 5 and moments['log_degree'] == 6 and moments['exp_degree'] == 3
    assert int(moments['log_floor_denominator']) == 1 << 80
    assert int(moments['final_floor_denominator']) == 1 << 96
    assert len(geometry['simplices']) == len(moments['records']) == 56
    problems, rows = [], []
    maximum_bits = 0
    for index, (row, record) in enumerate(zip(geometry['simplices'], moments['records'])):
        assert row['simplex_id'] == record['simplex_id'] == index
        vertices = [geometry['vertex_values'][i] for i in row['vertex_ids']]
        assert len(vertices) == 9
        gaps = [Q(v['gap']) for v in vertices]
        gap_sum = sum(gaps, Q(0))
        assert min(gaps) >= 0 and gap_sum > 0
        assert Q(row['mean_gap']) == gap_sum / 9
        means = list(map(Q, row['gap_weighted_means']))
        tops = list(map(Q, row['factor_maxima']))
        assert len(means) == len(tops) == len(record['log_gap_factor_floors_Q80']) == 10
        floors = []
        for factor in range(10):
            values = [Q(v['factors'][factor]) for v in vertices]
            assert min(values) > 0 and tops[factor] == max(values)
            expected_mean = (sum(values, Q(0)) +
                             sum((g * v for g, v in zip(gaps, values)), Q(0)) / gap_sum) / 10
            assert means[factor] == expected_mean
            deviations = [1 - v / tops[factor] for v in values]
            assert min(deviations) >= 0 and max(deviations) < 1
            # Complete homogeneous coefficients of nine nodes, degrees 0..6.
            homogeneous = [Q(1)] + [Q(0)] * 6
            for node in deviations:
                for k in range(1, 7):
                    homogeneous[k] += node * homogeneous[k - 1]
            powers = [sum((g * y**k for g, y in zip(gaps, deviations)), Q(0))
                      for k in range(7)]
            actual = [sum((homogeneous[k-j] * powers[j] for j in range(k+1)), Q(0)) /
                      (gap_sum * comb(9+k, k)) for k in range(7)]
            assert actual[0] == 1 and actual[1] == 1 - means[factor] / tops[factor]
            correction = sum(((actual[k] - actual[1]**k) / k for k in range(2, 7)), Q(0))
            assert correction >= 0
            maximum_bits = max(maximum_bits, correction.numerator.bit_length(),
                               correction.denominator.bit_length())
            computed = fixed(80, correction)
            stored = int(record['log_gap_factor_floors_Q80'][factor])
            if computed != stored:
                problems.append({'row': index, 'factor': factor, 'kind': 'Q80_mismatch',
                                 'computed': str(computed), 'stored': str(stored)})
            floors.append(computed)
        mass = Q(row['physical_volume']) * Q(row['mean_gap'])
        old = 4 * mass / prod(means)
        assert old == Q(row['jensen_bound'])
        old_floor = fixed(96, old)
        if old_floor != int(row['jensen_floor_Q96']) or old_floor != int(record['old_floor_Q96']):
            problems.append({'row': index, 'kind': 'old_Q96_mismatch'})
        total = Q(sum(floors), 1 << 80)
        improved = old * (1 + total * (1 + total * (Q(1, 2) + total / 6)))
        new_floor = fixed(96, improved)
        if new_floor != int(record['new_floor_Q96']):
            problems.append({'row': index, 'kind': 'new_Q96_mismatch',
                             'computed': str(new_floor), 'stored': record['new_floor_Q96']})
        assert new_floor >= old_floor
        rows.append({'row': index, 'factors': 10, 'old_floor': str(old_floor),
                     'new_floor': str(new_floor), 'improvement_units': str(new_floor-old_floor)})
    result = {'schema': 'p26_moment05_exact_rational_advisory_preflight_v1',
              'status': 'matched' if not problems else 'mismatched',
              'formal_acceptance': False, 'P2_6_complete': False,
              'sources': sources, 'rows_checked': len(rows), 'factors_checked': 560,
              'maximum_correction_integer_bits': maximum_bits,
              'problems': problems, 'rows': rows, 'seconds': time.monotonic()-started}
    OUT.mkdir(exist_ok=True)
    (OUT / 'PREFLIGHT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'rows_checked', 'factors_checked',
                     'maximum_correction_integer_bits', 'seconds', 'formal_acceptance']}))
    if problems:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
