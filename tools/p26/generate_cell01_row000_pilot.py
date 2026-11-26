#!/usr/bin/env python3
"""Generate only the cell01/row000 source pilot; never invoke Lean or a job API.

The established cell00 row000 owners are structural donors. Host rational
calculations generate candidate literals, each of which has a closed Lean
proof obligation in the generated owners. Existing source owners are read only.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import re


REPO = Path(__file__).resolve().parents[2]
DEFAULT_INPUTS = Path('/workspace/p26-original-inputs')
DEFAULT_TEMPLATE_ROOT = Path('/workspace/p26-recovery-candidates/cell00-row000-moment-floor')
GNAME = 'eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json'
MNAME = 'eighth-third-moment-refinement-20261009-a23-low-01.witness.json'
EXPECTED = {
    GNAME: 'e19eee9d7e282cd3a618a71f12e93bcce28319485c9d0fd31bbeaf9f81a995a4',
    MNAME: '03e9360189414e240818a191e5b53102aa5e8c3a1e7c18fbd8553ba020078d8c',
}


def fingerprint(path: Path) -> dict:
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def write_new(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        raise FileExistsError(f'Refusing to replace an existing owner: {path}')
    path.write_text(text)


def write_json(path: Path, data: object) -> None:
    write_new(path, json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def adapt(text: str) -> str:
    text = text.replace('Cell00', 'Cell01').replace('cell00', 'cell01')
    text = text.replace('Geometry00', 'Geometry01').replace('GEOMETRY00', 'GEOMETRY01')
    text = text.replace('Moment00', 'Moment01').replace('momentConcrete00', 'momentConcrete01')
    text = text.replace('Fin 56', 'Fin 144').replace('P26_ROW000', 'P26_CELL01_ROW000')
    marker = '/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or\n'
    marker += 'independently kernel-replayed. Existing suppliers are imported unchanged. -/\n\n'
    text, count = re.subn(r'((?:^import [^\n]+\n)+)\n', lambda m: m[1] + '\n' + marker,
                         text, count=1, flags=re.M)
    assert count == 1
    return text


def replace_once(text: str, pattern: str, replacement) -> str:
    result, count = re.subn(pattern, replacement, text, count=1, flags=re.S)
    assert count == 1, pattern
    return result


def rat(q: Fraction) -> str:
    return f'({q.numerator} : ℚ) / {q.denominator}'


def vec(values) -> str:
    return '![' + ', '.join(str(value) for value in values) + ']'


def candidate(q: Fraction) -> dict:
    return {'numerator': str(q.numerator), 'denominator': str(q.denominator)}


def comparison(t):
    return (1 + t[0] + t[3]) / 2


def new_cap(t):
    return (1 + t[1] + t[3] + t[7]) / 2 - Fraction(1, 1000000)


def factors(t):
    return [comparison(t) - sum(t), new_cap(t) - sum(t)] + t


def host_prefix(z):
    table = [1] + [0] * 6
    for a in reversed(z):
        carry = 0
        next_table = []
        for value in table:
            carry = value + a * carry
            next_table.append(carry)
        table = next_table
    return table


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', type=Path, default=DEFAULT_INPUTS)
    parser.add_argument('--template-root', type=Path, default=DEFAULT_TEMPLATE_ROOT)
    args = parser.parse_args()
    output = REPO / 'ImbalancedChen'
    report_dir = REPO / 'docs/verification/20261126-p26/cell01-row000-pilot'
    fixtures = []
    raw = []
    for name in [GNAME, MNAME]:
        path = args.inputs / name
        identity = fingerprint(path)
        assert identity['sha256'] == EXPECTED[name], identity
        fixtures.append(identity)
        raw.append(json.loads(path.read_bytes()))
    geometry, moments = raw
    assert geometry['dimension'] == moments['dimension'] == 8
    assert moments['cell_id'] == 1 and moments['source_witness'] == GNAME
    assert len(geometry['simplices']) == len(moments['records']) == 144
    assert len(geometry['vertices']) == 40
    row, moment_row = geometry['simplices'][0], moments['records'][0]
    assert row['simplex_id'] == moment_row['simplex_id'] == 0
    ids = row['vertex_ids']
    assert ids == [39, 35, 29, 28, 25, 13, 3, 1, 0]
    vertices = [[Fraction(q) for q in geometry['vertices'][i]] for i in ids]
    gaps = [new_cap(t) - comparison(t) for t in vertices]
    tops = [Fraction(value) for value in row['factor_maxima']]
    deviations = [[1 - factors(v)[j] / tops[j] for v in vertices] for j in range(10)]
    gap_scale = math.lcm(*(q.denominator for q in gaps))
    gap_nats = [int(q * gap_scale) for q in gaps]
    denominators = [math.lcm(*(q.denominator for q in ds)) for ds in deviations]
    deviation_nats = [[int(q * d) for q in ds] for ds, d in zip(deviations, denominators)]
    assert all(x >= 0 for x in gap_nats)
    assert all(x >= 0 for zs in deviation_nats for x in zs)
    assert sum(gap_nats) > 0

    def host_moment(z, d, k):
        table = host_prefix(z)
        numerator = sum(table[k-j] * sum(g * y**j for g, y in zip(gap_nats, z))
                        for j in range(k+1))
        return Fraction(numerator, sum(gap_nats) * math.comb(9+k, k) * d**k)

    moment_values = [[host_moment(z, d, k) for k in range(1, 7)]
                     for z, d in zip(deviation_nats, denominators)]
    gap_values = [sum((ms[k-1] - ms[0]**k) / k for k in range(2, 7))
                  for ms in moment_values]
    saved_total = sum(map(int, moment_row['log_gap_factor_floors_Q80']))
    saved_new = int(moment_row['new_floor_Q96'])

    # These checks only reject an inconsistent candidate-generation input.
    # Every accepted mathematical statement is still a generated Lean obligation.
    host_floor_values = [math.floor(q * 2**80) for q in gap_values]
    assert host_floor_values == list(map(int, moment_row['log_gap_factor_floors_Q80']))
    total = Fraction(saved_total, 2**80)
    host_new = math.floor(Fraction(row['jensen_bound']) *
                          (1 + total * (1 + total * (Fraction(1, 2) + total / 6))) * 2**96)
    assert host_new == saved_new

    generated = []
    donors = []

    def source(name):
        path = output / f'{name}.lean'
        donors.append(fingerprint(path))
        return path.read_text()

    def emit(name, text):
        path = output / f'{name}.lean'
        write_new(path, text)
        namespace = re.search(r'^namespace\s+([\w.]+)\s*$', text, re.M)[1]
        theorems = re.findall(r'^theorem\s+(\w+)', text, re.M)
        generated.append({'module': 'ImbalancedChen.' + name, 'source': fingerprint(path),
                          'imports': re.findall(r'^import\s+([\w.]+)\s*$', text, re.M),
                          'namespace': namespace, 'theorems': theorems,
                          'owned_theorems': [namespace + '.' + theorem for theorem in theorems],
                          'status': 'source_candidate_not_compiled'})

    emit('P2OriginalSaving19Geometry01BoundedAccess',
         adapt(source('P2OriginalSaving19Geometry00BoundedAccess')))

    text = adapt(source('P2OriginalSaving19Cell00Row000Input'))
    text = text.replace('open P2OriginalSaving19Geometry01Decoding\n',
                        'open P2OriginalSaving19Geometry01Decoding\n'
                        'open P2OriginalSaving19Geometry01DirectDecoding\n')
    vertex_def = 'noncomputable def vertices : Fin 9 → QPoint :=\n  !['
    vertex_def += ',\n    '.join(f'(fun j => geometryVerticesTyped{v:03d}[j.val]!)' for v in ids)
    vertex_def += ']\n\n'
    text = replace_once(text, r'noncomputable def vertices : Fin 9 → QPoint :=.*?\n\n',
                        lambda _: vertex_def)
    emit('P2OriginalSaving19Cell01Row000Input', text)

    for suffix in ['Determinant', 'Physical', 'Gap', 'Means', 'Maxima', 'Jensen',
                   'Arithmetic', 'OldFloor']:
        emit('P2OriginalSaving19Cell01Row000' + suffix,
             adapt(source('P2OriginalSaving19Cell00Row000' + suffix)))

    text = adapt(source('P2OriginalSaving19Cell00Row000MomentEncoding'))
    encodings = f'def gapScale : Nat := {gap_scale}\n\n'
    encodings += f'def gapNats : Fin 9 → Nat := {vec(gap_nats)}\n\n'
    encodings += f'def deviationDenominators : Fin 10 → Nat := {vec(denominators)}\n\n'
    encodings += 'def deviationNats : Fin 10 → Fin 9 → Nat :=\n  !['
    encodings += ',\n    '.join(vec(z) for z in deviation_nats) + ']\n\n'
    text = replace_once(text, r'def gapScale : Nat :=.*?(?=def prefixMoment)',
                        lambda _: encodings)
    emit('P2OriginalSaving19Cell01Row000MomentEncoding', text)

    for j in range(10):
        suffix = f'{j:02d}'
        text = adapt(source('P2OriginalSaving19Cell00Row000MomentFactor' + suffix))
        for k, q in enumerate(moment_values[j], 1):
            pattern = (rf'(theorem factor{suffix}_moment{k} : '
                       rf'prefixMoment \({j} : Fin 10\) {k} = ).*?( := by)')
            text = replace_once(text, pattern, lambda m, q=q: m[1] + rat(q) + m[2])
        pattern = (rf'(theorem factor{suffix}_gap_value :\s*'
                   rf'gapEvaluator \(prefixMoment \({j} : Fin 10\)\) = ).*?( := by)')
        text = replace_once(text, pattern, lambda m: m[1] + rat(gap_values[j]) + m[2])
        emit('P2OriginalSaving19Cell01Row000MomentFactor' + suffix, text)

    text = adapt(source('P2OriginalSaving19Cell00Row000PrefixFloorChecks'))
    old_total = re.search(r'theorem total_Q80_value :\s*totalLowerQ80 prefixMoment = '
                          r'\((\d+) : ℚ\)', text)[1]
    assert text.count(old_total) == 2
    text = text.replace(old_total, str(saved_total))
    text = replace_once(text, r'(theorem new_Q96_value :\s*newFloorQ96 '
                        r'\(massOf row\) \(meansOf row\) prefixMoment = )\d+( := by)',
                        lambda m: m[1] + str(saved_new) + m[2])
    emit('P2OriginalSaving19Cell01Row000PrefixFloorChecks', text)

    bridge_path = (args.template_root / 'bridge-candidate/ImbalancedChen/'
                   'P2OriginalSaving19Cell00Row000OriginalFloorBridge.lean')
    donors.append(fingerprint(bridge_path))
    text = adapt(bridge_path.read_text())
    text = replace_once(text, r'/\-! SOURCE-ONLY integration candidate\..*?\-/',
                        lambda _: '/-! Exact row000 transport through the existing HigherMomentsPrefix\n'
                        'representation theorem and original Q96 namespace bridge. This new owner\n'
                        'requires its own acceptance and imports both generic suppliers unchanged. -/')
    text = text.replace('namespace ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge\n',
                        'namespace ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge\n\n'
                        'set_option maxRecDepth 1000000\nset_option Elab.async false\n')
    text = text.replace('This does not connect the remaining twelve archive cells.',
                        'The remaining 143 rows and all other cells are separate obligations.')
    emit('P2OriginalSaving19Cell01Row000OriginalFloorBridge', text)

    order = [record['module'] for record in generated]
    assert len(order) == 23 and len(set(order)) == 23
    expected_suppliers = [
        'ImbalancedChen.P2OriginalSaving19Geometry01Shape',
        'ImbalancedChen.P2OriginalSaving19Moment01Shape',
        'ImbalancedChen.P2OriginalSaving19RowNumericsPure',
        'ImbalancedChen.P2Winner9FastDetPure',
        'ImbalancedChen.P2OriginalSaving19PrefixMoments',
        'ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix',
        'ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge',
    ]
    for record in generated:
        body = re.sub(r'/\-.*?\-/', '', (REPO / Path(record['module'].replace('.', '/') + '.lean')).read_text(),
                      flags=re.S)
        body = re.sub(r'--[^\n]*', '', body)
        assert not re.search(r'\b(?:axiom|sorry|admit|native_decide|unsafe)\b', body)
        assert 'Cell00' not in body
        for module in record['imports']:
            if module.startswith('ImbalancedChen.'):
                assert (REPO / Path(module.replace('.', '/') + '.lean')).is_file(), module
                if module in order:
                    assert order.index(module) < order.index(record['module'])

    witness = {
        'schema': 'saving19_cell01_row000_candidates_v1',
        'status': 'host candidates only; no Lean or kernel acceptance',
        'original_fixtures': fixtures,
        'original_vertex_ids': ids,
        'gap_scale': str(gap_scale), 'gap_nats': list(map(str, gap_nats)),
        'deviation_denominators': list(map(str, denominators)),
        'deviation_nats': [list(map(str, z)) for z in deviation_nats],
        'moment_degree1_through6_candidates': [[candidate(q) for q in ms] for ms in moment_values],
        'log_gap_candidates': [candidate(q) for q in gap_values],
        'original_saved_Q80': moment_row['log_gap_factor_floors_Q80'],
        'original_old_Q96': moment_row['old_floor_Q96'],
        'original_new_Q96': moment_row['new_floor_Q96'],
        'candidate_total_Q80': str(saved_total),
        'host_candidate_consistency_checks_only': True,
        'mathematical_acceptance_from_host': False,
    }
    write_json(report_dir / 'CANDIDATE_WITNESSES.json', witness)
    manifest = {
        'schema': 'saving19_cell01_row000_source_pilot_v1',
        'status': 'source_generated_no_Lean_or_cloud_run',
        'scope': 'one row only: cell01 row000, plus reusable 144-row bounded access from certified shape',
        'generator': fingerprint(Path(__file__).resolve()),
        'original_fixtures': fixtures,
        'structural_donors': donors,
        'reference_generators': [fingerprint(args.template_root / name)
                                 for name in ['setup_and_generate.py', 'generate_final.py']],
        'new_owners': generated,
        'cloud_order': order,
        'expected_existing_supplier_roots': expected_suppliers,
        'suppliers_recompiled': False,
        'original_definitions_modified': False,
        'all_144_row_arithmetic_claimed': False,
        'integral_claimed': False,
    }
    write_json(report_dir / 'SOURCE_MANIFEST.json', manifest)
    write_new(report_dir / 'cloud_order.txt', '\n'.join(order) + '\n')
    print(json.dumps({'source_owners': len(generated), 'source_manifest': str(report_dir / 'SOURCE_MANIFEST.json'),
                      'cloud_order': str(report_dir / 'cloud_order.txt'), 'status': manifest['status'],
                      'original_vertex_ids': ids, 'gap_scale': gap_scale,
                      'saved_new_Q96_candidate': str(saved_new)}, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
