"""Specialize the pinned Cell01 typed-literal renderer to archive index three."""
import re


def render(raw, node, obj, ns, schemas, measured):
    FIELDS = schemas["FIELDS"]
    SIMPLEX_FIELDS = schemas["SIMPLEX_FIELDS"]
    assert FIELDS == schemas['FIELDS'] and SIMPLEX_FIELDS == schemas['SIMPLEX_FIELDS']
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
    emit('cell03Payload', 'CellRecord', '{\n' + '\n'.join(
        f'    {name} := {name}' for name in typed_names) + '\n  }')
    assert len(rational_entries) == measured['counts']['unique_rational_strings']
    assert sum(len(v['locations']) for v in rational_entries.values()) == measured['counts']['rational_occurrences']
    assert len(integer_entries) == measured['counts']['unique_integer_strings']
    assert sum(len(v['locations']) for v in integer_entries.values()) == measured['counts']['integer_occurrences']
    header = f'''import ImbalancedChen.P2OriginalSaving16Decoder

/-!
UNTRUSTED CANDIDATE DATA ONLY.  These literals are generated from the exact
{len(raw):,}-byte original cell03 JSON.  They are not a decoding certificate.
Every scalar retains the original numerator/denominator spelling; no host
rational normalization is used.  Raw fields preserve all nested data and
their original order.  The unchanged original decoder must separately be
proved to return `cell03Payload` from the certified original `rootValue`.
This module adds no decoder, theorem, assumption, finite guard, or Q96 claim.
-/
namespace ImbalancedChen.P2Saving16Cell03TypedPayload

open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (CellRecord SimplexRecord)
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
noncomputable section

'''
    source = (header + '\n'.join(scalar_lines + data_lines) +
              '\nend\nend ImbalancedChen.P2Saving16Cell03TypedPayload\n').encode()
    return source.decode(), {
        "rational_candidates": list(rational_entries.values()),
        "integer_candidates": list(integer_entries.values()),
        "raw_fields": [{"key": key, "start": nodes[key].start, "end": nodes[key].end}
                       for key, _ in FIELDS],
    }
