"""Eight fixed parent diagnostics, never a whole-archive checker or Lean proof.

Reads existing typed/stored Lean literals. Mirrors the current Lean integer
formula and separately reconstructs its 3/4 logarithm bound with Fraction.
The original Python generator is not available in this local checkout.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import re
import time

ROOT = Path('/workspace/scratch/638a86a3af73/goldbach-p1')
OUT = Path('/workspace/scratch/638a86a3af73/p1-pending-repairs')
SAMPLES = (0, 1, 5, 2047, 2048, 4096, 146316, 292632)
WIDTH = (2, 2, 2, 2, 1)
VERTEX_BITS = tuple(product((0, 1), repeat=5))
CHILDREN = tuple(product(range(2), range(2), range(2), range(2), range(4)))
READS: dict[str, dict] = {}


def read_bound(path: Path) -> str:
    raw = path.read_bytes()
    READS[str(path)] = {'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)}
    return raw.decode()


def literal_row(path: Path, index: int, regex: str) -> tuple[int, ...]:
    text = read_bound(path)
    rows = re.findall(regex, text, flags=re.M)
    assert 0 <= index < len(rows)
    return tuple(map(int, rows[index]))


def source_row(index: int) -> dict:
    block, local = divmod(index, 2048)
    p = ROOT / f'ImbalancedChen/Data/P1HistoricalFifthSavedDataBlock{block:03}.lean'
    ints = literal_row(p, local,
        r'^\s*⟨(-?\d+), !\[(-?\d+), (-?\d+), (-?\d+), (-?\d+), (-?\d+)\], '
        r'(-?\d+), (-?\d+), (-?\d+), (-?\d+)⟩,?\s*$')
    assert len(ints) == 10
    return {'grid': ints[0], 'lo': ints[1:6], 'mask': ints[6],
            'opaque_parent_d': ints[7], 'opaque_parent_A': ints[8],
            'opaque_parent_B': ints[9], 'source_file': str(p), 'local_index': local}


def stored_row(index: int) -> dict:
    block, local = divmod(index, 4096)
    p = ROOT / f'ImbalancedChen/Data/P5SubdivisionStoredBlock{block:03}.lean'
    ints = literal_row(p, local, r'^\s*⟨(\d+), (-?\d+), (-?\d+)⟩,?\s*$')
    assert ints[0] == index
    return {'sourceIndex': ints[0], 'oldQ80': ints[1], 'newQ80': ints[2],
            'source_file': str(p), 'local_index': local}


def mask_slots(rank: int, mask: int) -> tuple[int, ...]:
    return tuple(i for i in range(rank) if (mask >> i) & 1)


def parent_picks(raw: dict) -> list[tuple[tuple[int, ...], int]]:
    result = []
    for mask in range(1, 16):
        slots = mask_slots(4, mask)
        ss = sum(2 * raw['lo'][i] + 1 for i in slots)
        a = 32 * raw['grid'] + 16 * ss
        c = 57 * raw['grid'] - 48 * ss
        k = 153 * raw['grid'] // 4
        pick = 0 if a <= c and a <= k else (1 if c <= k else 2)
        result.append((slots, pick))
    return result


def old_plane(pick: int, ss: int) -> int:
    return 25600 + 16 * ss if pick == 0 else (45600 - 48 * ss if pick == 1 else 30600)


def exact_floor(row: dict) -> dict:
    d, A, B, hi, n = (row[k] for k in ('d', 'A', 'B', 'hi', 'n'))
    if d <= 0:
        return {'floor': 0, 'branch': 'nonpositive_d', 'fraction_floor': 0,
                'rational_identity_matches': True}
    H = 1024 * hi[4]
    C = H * A - d * B
    z = d * B
    den = 2 * H * (A - B) - z
    rn = 2 * z * (15 * den**4 + 5 * z**2 * den**2 + 3 * z**4)
    rd = 15 * den**5
    y = C - 2 * H * B
    cc, yy = C**2, y**2
    ln = 2 * y * (315 * cc**4 - 210 * yy * cc**3 -
                  42 * yy**2 * cc**2 - 18 * yy**3 * cc - 10 * yy**4)
    ld = 315 * C**7 * (cc - yy)
    dn = B * (C * rn * ld - d * B * ln * rd)
    dd = C * A * rd * ld
    numerator = 4 * n * math.prod(WIDTH) * dn
    denominator = math.prod(hi) * hi[4] * dd
    assert B > 0 and denominator > 0, ('division sign', row)
    integer_floor = (numerator * 2**80) // denominator

    # Independent rational algebra from Q_b(e), using three lower log terms
    # and four upper terms plus the directed geometric tail. No floats.
    b, e = F(A, B), F(d, H)
    a = b - e
    r = ((b - 1) - (a - 1)) / ((b - 1) + (a - 1))
    t = ((a - 1) - 1) / ((a - 1) + 1)
    lower_log = 2 * sum((r**(2*j + 1) / (2*j + 1) for j in range(3)), F(0))
    upper_log = 2 * sum((t**(2*j + 1) / (2*j + 1) for j in range(4)), F(0))
    upper_log += 2 * t**9 / (9 * (1 - t*t))
    q_bound = (a * lower_log - e * upper_log) / (a * b)
    scaled_bound = F(4*n*math.prod(WIDTH), math.prod(hi)*hi[4]) * q_bound
    assert scaled_bound == F(numerator, denominator), ('rational transcription', row)
    q80 = scaled_bound * 2**80
    fraction_floor = q80.numerator // q80.denominator
    assert integer_floor == fraction_floor
    return {'floor': integer_floor, 'branch': 'positive_d', 'fraction_floor': fraction_floor,
            'rational_identity_matches': True, 'b': str(b), 'e': str(e), 'a': str(a),
            'domain_gate_2_le_a_lt_b_le_4': 2 <= a < b <= 4,
            'polynomial_numerator': str(numerator), 'polynomial_denominator': str(denominator)}


def child_record(raw: dict, child: tuple[int, ...], picks: list) -> dict:
    lo = tuple(4*x + w*c for x, w, c in zip(raw['lo'], WIDTH, child))
    hi = tuple(x + w for x, w in zip(lo, WIDTH))
    vertices = [tuple(x + w*bit for x, w, bit in zip(lo, WIDTH, bits)) for bits in VERTEX_BITS]
    selected = mask_slots(5, raw['mask'])
    d = 0
    pairs = ([], [])
    for v in vertices:
        ss = sum(v[i] for i in selected)
        a_plane, c_plane = 25600 + 16*ss, 45600 - 48*ss
        old = max([30600 - 12*v[2]] + [old_plane(p, sum(v[i] for i in slots)) for slots, p in picks])
        d += min(a_plane, c_plane) - max(old, 32*(sum(v) + 2*v[4]))
        pairs[0].append((a_plane - 32*sum(v), 32*v[4]))
        pairs[1].append((c_plane - 32*sum(v), 32*v[4]))
    maxima = []
    for ps in pairs:
        best = ps[0]
        for nxt in ps[1:]:
            if best[0]*nxt[1] < nxt[0]*best[1]:
                best = nxt
        maxima.append(best)
    asc, desc = maxima
    A, B = desc if desc[0]*asc[1] < asc[0]*desc[1] else asc
    row = {'child': child, 'n': 1600, 'lo': lo, 'hi': hi, 'mask': raw['mask'], 'd': d, 'A': A, 'B': B}
    row.update(exact_floor(row))
    return row


def main() -> None:
    start = time.perf_counter()
    assert len(SAMPLES) == 8 and len(CHILDREN) == 64
    records = []
    for index in SAMPLES:
        raw, saved = source_row(index), stored_row(index)
        picks = parent_picks(raw)
        children = [child_record(raw, c, picks) for c in CHILDREN]
        child_sum = sum(c['floor'] for c in children)
        expected = max(saved['oldQ80'], child_sum)
        record = {'sourceIndex': index, 'raw': raw, 'stored': saved, 'parent_picks': picks,
                  'children': children, 'original_child_sum': child_sum,
                  'reconstructed_max': expected, 'stored_new_minus_reconstructed': saved['newQ80'] - expected,
                  'exact_max_matches': saved['newQ80'] == expected,
                  'chosen_branch': 'old' if saved['oldQ80'] >= child_sum else 'child',
                  'nonpositive_children': sum(c['d'] <= 0 for c in children)}
        records.append(record)
        print(json.dumps({k:record[k] for k in ('sourceIndex', 'original_child_sum', 'reconstructed_max',
            'stored_new_minus_reconstructed', 'exact_max_matches', 'chosen_branch', 'nonpositive_children')}))
    for name in ('P5OriginalChildIntegerWireBinding', 'P5FullStoredParentSameOwnerBinding'):
        read_bound(ROOT / f'ImbalancedChen/{name}.lean')
    report = {'status': 'DIAGNOSTIC_ONLY_NOT_FORMAL_ACCEPTANCE', 'indices': SAMPLES,
              'parents': len(records), 'children': 64*len(records), 'log_terms': [3, 4],
              'formula_source': 'current exact Lean integer transcription, independently cross-checked by Fraction series',
              'original_python_generator_available': False, 'whole_archive_checked': False,
              'all_sample_max_equalities_match': all(r['exact_max_matches'] for r in records),
              'all_active_domain_gates_hold': all(c.get('domain_gate_2_le_a_lt_b_le_4', True) for r in records for c in r['children']),
              'elapsed_seconds': time.perf_counter()-start, 'source_files': READS,
              'diagnostic_script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'records': records}
    (OUT/'selected-stored-parent-diagnostic.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('records', 'source_files')}))


if __name__ == '__main__':
    main()
