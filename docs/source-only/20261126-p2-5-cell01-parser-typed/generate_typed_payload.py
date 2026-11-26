#!/usr/bin/env python3
"""Generate UNTRUSTED Cell01 literal data for the unchanged typed decoder.

No parser/decoder is replaced and no theorem is generated.  The original Lean
decoder must separately be proved equal to this candidate.  Existing output
bytes are immutable: rerunning this script only checks them.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path
from measure_input import load_input, MEASUREMENTS

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
INPUT_SHA = 'd7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f'
DONOR = ROOT.parent / '20261126-p2-5-cell00-segmented/donor/generate.py'
DONOR_SHA = '3114c68369ad3a6e3f7e3171aedadb40830917cf1592cc09e99932afdf71703d'
DONOR_COMMIT = 'bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3'
MODULE = 'ImbalancedChen.P2Saving16Cell01TypedPayload'
FIELDS = [
    ('dimension', 'Dimension'), ('physical_jacobian', 'PhysicalJacobian'),
    ('cell_id', 'CellId'), ('left_masks', 'LeftMasks'),
    ('right_masks', 'RightMasks'), ('facet_original_indices', 'FacetOriginalIndices'),
    ('positive_normal_balance', 'PositiveNormalBalance'), ('normal_rank', 'NormalRank'),
    ('active8_enumeration', 'Active8'), ('vertices', 'Vertices'),
    ('vertex_values', 'VertexValues'), ('all_original_constraint_minima', 'AllOriginalMinima'),
    ('facet_vertices', 'FacetVertices'), ('face_ledger', 'FaceLedger'),
    ('simplices', 'Simplices'), ('physical_volume', 'PhysicalVolume'),
    ('integral_gap', 'IntegralGap'),
]
SIMPLEX_FIELDS = [
    ('simplex_id', 'simplexId'), ('vertex_ids', 'vertexIds'),
    ('physical_volume', 'physicalVolume'), ('mean_gap', 'meanGap'),
    ('factor_maxima', 'factorMaxima'), ('gap_weighted_means', 'gapWeightedMeans'),
    ('max_bound', 'maxBound'), ('jensen_bound', 'jensenBound'),
    ('max_floor_Q96', 'maxFloor'), ('jensen_floor_Q96', 'jensenFloor'),
]


def immutable(path, data):
    if path.exists():
        assert path.read_bytes() == data, f'Generated output drift: {path}'
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True, help='Existing exact original Cell01 witness')
    args = parser.parse_args()
    raw, node, obj, ns, schemas, measured = load_input(args.input)
    assert measured == json.loads(MEASUREMENTS.read_text())
    assert FIELDS == schemas['FIELDS'] and SIMPLEX_FIELDS == schemas['SIMPLEX_FIELDS']
    donor_names = {'Node', 'Field', 'RawPlanner', 'quote_char', 'quote_list', 'lean_node'}
    assert list(obj) == [k for k, _ in FIELDS]
    nodes = {f.key.scalar: f.value for f in node.fields}
    quote = ns['quote_list']
    quote_node = ns['lean_node']
    scalar_lines, data_lines = [], []
    rational_entries, integer_entries = {}, {}
    decls = []

    def emit(name, typ, value, target=data_lines):
        decls.append(name)
        target.append(f'def {name} : {typ} :=\n  {value}\n')

    def integer_token(s):
        assert isinstance(s, str) and re.fullmatch(r'-?[0-9]+', s)
        assert str(int(s)) == s, f'Unexpected noncanonical integer spelling: {s}'
        return s

    def rat(s, site):
        assert isinstance(s, str)
        if s not in rational_entries:
            parts = s.split('/')
            assert len(parts) in (1, 2)
            n = integer_token(parts[0])
            d = integer_token(parts[1]) if len(parts) == 2 else None
            assert d is None or int(d) != 0
            index = len(rational_entries)
            name, chars_name = f'rational{index:03}', f'rationalChars{index:03}'
            expr = f'({n} : ℚ)' if d is None else f'({n} : ℚ) / ({d} : ℚ)'
            emit(chars_name, 'List Char', quote(s), scalar_lines)
            emit(name, 'ℚ', expr, scalar_lines)
            rational_entries[s] = {
                'name': name, 'chars_name': chars_name, 'original_string': s,
                'numerator_string': n, 'denominator_string': d,
                'lean_expression': expr, 'locations': [],
            }
        rational_entries[s]['locations'].append(site)
        return rational_entries[s]['name']

    def integer(s, site):
        integer_token(s)
        if s not in integer_entries:
            index = len(integer_entries)
            name, chars_name = f'integer{index:03}', f'integerChars{index:03}'
            emit(chars_name, 'List Char', quote(s), scalar_lines)
            emit(name, 'ℤ', s, scalar_lines)
            integer_entries[s] = {
                'name': name, 'chars_name': chars_name, 'original_string': s, 'locations': [],
            }
        integer_entries[s]['locations'].append(site)
        return integer_entries[s]['name']

    def nat(n):
        assert type(n) is int and n >= 0
        return str(n)

    def array(xs):
        return '#[' + ', '.join(xs) + ']'

    def rats(xs, site):
        return array([rat(x, f'{site}/{i}') for i, x in enumerate(xs)])

    def naturals(xs):
        return array([nat(x) for x in xs])

    # Candidate raw subtrees.  Exact original field order and every retained
    # nested value come from the unchanged donor quotation.
    for key, suffix in FIELDS:
        child = nodes[key]
        if key in ('vertices', 'simplices'):
            prefix = 'rawVertex' if key == 'vertices' else 'rawSimplex'
            names = []
            for i, item in enumerate(child.children):
                name = f'{prefix}{i:02}'
                emit(name, 'SourceJson', quote_node(item))
                names.append(name)
            emit(f'raw{suffix}Items', 'List SourceJson', '[' + ', '.join(names) + ']')
            emit(f'raw{suffix}', 'SourceJson', f'.arr raw{suffix}Items')
        elif key in ('active8_enumeration', 'vertex_values', 'face_ledger'):
            emit(f'raw{suffix}Items', 'List SourceJson',
                 '[' + ', '.join(quote_node(n) for n in child.children) + ']')
            emit(f'raw{suffix}', 'SourceJson', f'.arr raw{suffix}Items')
        else:
            emit(f'raw{suffix}', 'SourceJson', quote_node(child))
    emit('rawFields', 'List (String × SourceJson)', '[\n    ' + ',\n    '.join(
        f'(String.ofList {quote(key)}, raw{suffix})' for key, suffix in FIELDS) + '\n  ]')
    emit('rawRoot', 'SourceJson', '.obj rawFields')

    # Candidate typed values follow the unchanged decodeCell / decodeSimplex
    # record schemas.  Raw geometry arrays remain SourceJson arrays.
    for key, name in [('cell_id', 'cellId'), ('dimension', 'dimension'),
                      ('physical_jacobian', 'physicalJacobian')]:
        emit(name, 'Nat', nat(obj[key]))
    for key, name in [('left_masks', 'leftMasks'), ('right_masks', 'rightMasks'),
                      ('facet_original_indices', 'facetOriginalIndices')]:
        emit(name, 'Array Nat', naturals(obj[key]))
    emit('positiveNormalBalance', 'Array ℚ', rats(obj['positive_normal_balance'], '/positive_normal_balance'))
    emit('normalRank', 'Nat', nat(obj['normal_rank']))
    emit('active8', 'Array SourceJson', 'rawActive8Items.toArray')
    for i, row in enumerate(obj['vertices']):
        assert len(row) == 8
        emit(f'vertex{i:02}', 'Array ℚ', rats(row, f'/vertices/{i}'))
    emit('vertices', 'Array (Array ℚ)', array([f'vertex{i:02}' for i in range(len(obj['vertices']))]))
    emit('vertexValues', 'Array SourceJson', 'rawVertexValuesItems.toArray')
    emit('allOriginalMinima', 'Array ℚ', rats(obj['all_original_constraint_minima'], '/all_original_constraint_minima'))
    emit('facetVertices', 'Array (Array Nat)', array([naturals(row) for row in obj['facet_vertices']]))
    emit('faceLedger', 'Array SourceJson', 'rawFaceLedgerItems.toArray')
    assert len(obj['simplices']) == measured['counts']['simplices']
    for i, simplex in enumerate(obj['simplices']):
        assert list(simplex) == [k for k, _ in SIMPLEX_FIELDS]
        parts = []
        for key, name in SIMPLEX_FIELDS:
            site = f'/simplices/{i}/{key}'
            if key == 'simplex_id':
                expr = nat(simplex[key])
            elif key == 'vertex_ids':
                assert len(simplex[key]) == 9
                expr = naturals(simplex[key])
            elif key in ('factor_maxima', 'gap_weighted_means'):
                assert len(simplex[key]) == 10
                expr = rats(simplex[key], site)
            elif key in ('max_floor_Q96', 'jensen_floor_Q96'):
                expr = integer(simplex[key], site)
            else:
                expr = rat(simplex[key], site)
            parts.append(f'    {name} := {expr}')
        emit(f'simplex{i:02}', 'SimplexRecord', '{\n' + '\n'.join(parts) + '\n  }')
    emit('simplices', 'Array SimplexRecord', array([f'simplex{i:02}' for i in range(len(obj['simplices']))]))
    for key, name in [('physical_volume', 'physicalVolume'), ('integral_gap', 'integralGap')]:
        emit(name, 'ℚ', rat(obj[key], '/' + key))
    typed_names = [
        'cellId', 'dimension', 'physicalJacobian', 'leftMasks', 'rightMasks',
        'facetOriginalIndices', 'positiveNormalBalance', 'normalRank', 'active8',
        'vertices', 'vertexValues', 'allOriginalMinima', 'facetVertices',
        'faceLedger', 'simplices', 'physicalVolume', 'integralGap',
    ]
    emit('cell01Payload', 'CellRecord', '{\n' + '\n'.join(
        f'    {name} := {name}' for name in typed_names) + '\n  }')
    assert len(rational_entries) == measured['counts']['unique_rational_strings']
    assert sum(len(v['locations']) for v in rational_entries.values()) == measured['counts']['rational_occurrences']
    assert len(integer_entries) == measured['counts']['unique_integer_strings']
    assert sum(len(v['locations']) for v in integer_entries.values()) == measured['counts']['integer_occurrences']
    header = f'''import ImbalancedChen.P2OriginalSaving16Decoder

/-!
UNTRUSTED CANDIDATE DATA ONLY.  These literals are generated from the exact
{len(raw):,}-byte original cell01 JSON.  They are not a decoding certificate.
Every scalar retains the original numerator/denominator spelling; no host
rational normalization is used.  Raw fields preserve all nested data and
their original order.  The unchanged original decoder must separately be
proved to return `cell01Payload` from the certified original `rootValue`.
This module adds no decoder, theorem, assumption, finite guard, or Q96 claim.
-/
namespace ImbalancedChen.P2Saving16Cell01TypedPayload

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (CellRecord SimplexRecord)
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
noncomputable section

'''
    source = (header + '\n'.join(scalar_lines + data_lines) +
              '\nend\nend ImbalancedChen.P2Saving16Cell01TypedPayload\n').encode()
    target = ROOT / (MODULE.replace('.', '/') + '.lean')
    immutable(target, source)
    manifest = {
        'schema': 'p25-cell01-untrusted-typed-payload-v1',
        'status': 'UNTRUSTED_LITERAL_CANDIDATE_NOT_A_DECODER_CERTIFICATE',
        'proof_credit_from_generator': False, 'typed_decode_proved': False,
        'input': {'path': measured['input']['install_path'], 'bytes': len(raw), 'sha256': INPUT_SHA},
        'measurements': {'path': str(MEASUREMENTS.relative_to(REPO)),
                         'sha256': hashlib.sha256(MEASUREMENTS.read_bytes()).hexdigest()},
        'donor': {'commit': DONOR_COMMIT,
                  'path': 'docs/verification/20261125-p26/archive-segment-generator/generate.py',
                  'sha256': DONOR_SHA, 'unchanged_definitions': sorted(donor_names)},
        'module': MODULE, 'source': str(target.relative_to(REPO)),
        'source_bytes': len(source), 'source_sha256': hashlib.sha256(source).hexdigest(),
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'candidate_declarations': decls, 'candidate_declaration_count': len(decls),
        'raw_fields': [{'json_key': key, 'lean_name': 'raw' + suffix,
                        'byte_span': [nodes[key].start, nodes[key].end], 'kind': nodes[key].kind}
                       for key, suffix in FIELDS],
        'typed_fields': typed_names,
        'counts': {'top_fields': len(FIELDS), 'active8': len(obj['active8_enumeration']),
                   'vertices': len(obj['vertices']), 'vertex_dimension': 8,
                   'vertex_values': len(obj['vertex_values']),
                   'all_original_minima': len(obj['all_original_constraint_minima']),
                   'facet_vertices': len(obj['facet_vertices']), 'face_ledger': len(obj['face_ledger']),
                   'simplices': len(obj['simplices']),
                   'rational_occurrences': sum(len(v['locations']) for v in rational_entries.values()),
                   'unique_rational_strings': len(rational_entries),
                   'integer_occurrences': sum(len(v['locations']) for v in integer_entries.values()),
                   'unique_integer_strings': len(integer_entries)},
        'rational_candidates': list(rational_entries.values()),
        'integer_candidates': list(integer_entries.values()),
    }
    immutable(ROOT / 'TYPED_PAYLOAD_MANIFEST.json',
              (json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode())
    print(json.dumps({k: manifest[k] for k in ['status', 'module', 'source_bytes',
                     'source_sha256', 'candidate_declaration_count', 'counts']}))


if __name__ == '__main__':
    main()
