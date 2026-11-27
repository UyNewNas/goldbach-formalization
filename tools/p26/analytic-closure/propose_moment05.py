"""Emit apply_patch candidates for the original Cell05 parse/decode interface.

The Cell00 proof layout is reused only as a template. Exact spans, JSON values
and typed rows are proposed from the byte-verified original Cell05 input. No
parser equation, floor inequality or Lean acceptance is inferred by Python.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'ImbalancedChen'
DATA = Path('/workspace/goldbach-research')
STAGE = Path('/workspace/p26-analytic-closure-20261127/original-moment05')


def chars(text):
    escapes = {'\r': r'\r', '\n': r'\n', '\t': r'\t', '\\': r'\\', "'": r"\'"}
    return '[' + ', '.join("'" + escapes.get(c, c) + "'" for c in text) + ']'


def string(text):
    return '(String.ofList ' + chars(text) + ')'


def value(item):
    if isinstance(item, str):
        return '.str ' + string(item)
    if isinstance(item, int):
        return '.number ' + string(str(item))
    if isinstance(item, list):
        return '.arr [' + ', '.join(value(x) for x in item) + ']'
    if isinstance(item, dict):
        return '.obj [' + ', '.join('(' + string(k) + ', ' + value(v) + ')'
                                   for k, v in item.items()) + ']'
    raise TypeError(type(item))


def spans(raw):
    decoder = json.JSONDecoder()
    fields, rows = [], []
    cursor = 1
    skip = lambda pos: pos + len(raw[pos:]) - len(raw[pos:].lstrip())
    for _ in range(9):
        start = cursor
        key, pos = decoder.raw_decode(raw, skip(cursor))
        pos = skip(pos)
        assert raw[pos] == ':'
        item, pos = decoder.raw_decode(raw, skip(pos + 1))
        pos = skip(pos)
        assert raw[pos] == ','
        cursor = pos + 1
        fields.append((start, cursor, key, item))
    header = cursor
    key, pos = decoder.raw_decode(raw, skip(cursor))
    assert key == 'records'
    pos = skip(pos)
    assert raw[pos] == ':'
    opening = skip(pos + 1)
    assert raw[opening] == '['
    cursor = opening + 1
    for i in range(56):
        start = cursor
        item, pos = decoder.raw_decode(raw, skip(cursor))
        assert item['simplex_id'] == i
        pos = skip(pos)
        assert raw[pos] == (']' if i == 55 else ',')
        cursor = pos + 1
        rows.append((start, cursor, item))
    assert raw[cursor:] == '\r\n}\r\n'
    return {'fields': fields, 'rows': rows, 'header': header,
            'opening': opening, 'ending': cursor}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--emit', help='Template suffix without .lean; emit one Add File patch')
    args = parser.parse_args()
    raw = []
    for cell, expected in [(0, 'd88e9d02334dfa840f81c0e2be8e97d559978ac3848fdea13990deced9a65052'),
                           (5, '9a85e92f79b24c2b2361717d3a29ecb6167059e5509211c2f3fb290b5284fe2c')]:
        data = (DATA / f'eighth-third-moment-refinement-20261009-a23-low-{cell:02d}.witness.json').read_bytes()
        assert hashlib.sha256(data).hexdigest() == expected
        text = data.decode('ascii')
        assert '\r\n' in text and text.count('\n') == text.count('\r\n')
        raw.append(text)
    old, new = map(spans, raw)
    # The reused root equation is value (fuel + 105); parseChars uses length + 1.
    parse_headroom = 105
    offsets = {len(raw[0]): len(raw[1]),
               len(raw[0]) + 1 - parse_headroom: len(raw[1]) + 1 - parse_headroom}
    for key in ['header', 'opening', 'ending']:
        offsets[old[key]] = new[key]
    offsets[old['opening'] + 1] = new['opening'] + 1
    offsets[old['ending'] + 3] = new['ending'] + 3
    for a, b in zip(old['rows'], new['rows']):
        offsets[a[0]], offsets[a[1]] = b[0], b[1]
    templates = sorted(SOURCE.glob('P2OriginalSaving19Moment00*.lean'))
    assert len(templates) == 35
    generated = {}
    for template in templates:
        suffix = template.stem.removeprefix('P2OriginalSaving19Moment00')
        text = template.read_text()
        replacements = dict(offsets)
        if suffix.startswith('RecordsBlock'):
            block = int(suffix.removeprefix('RecordsBlock'))
            first, last = 4 * block, 4 * block + 3
            a = old['rows'][last][1] - old['rows'][first][0]
            b = new['rows'][last][1] - new['rows'][first][0]
            assert a not in replacements or replacements[a] == b
            replacements[a] = b
        def quoted(match):
            name, literal = match.groups()
            old_text = ''.join(ast.literal_eval(literal))
            if name.startswith('momentMetadataField'):
                index = int(re.search(r'Field(\d+)', name)[1])
                a, b, _, _ = old['fields'][index]
                assert raw[0][a:b] == old_text
                a, b, _, _ = new['fields'][index]
                return f'noncomputable def {name} : List Char := ' + chars(raw[1][a:b])
            if name.startswith('momentRecordsChunk'):
                index = int(re.search(r'Chunk(\d+)', name)[1])
                a, b, _ = old['rows'][index]
                assert raw[0][a:b] == old_text
                a, b, _ = new['rows'][index]
                return f'noncomputable def {name} : List Char := ' + chars(raw[1][a:b])
            return match[0]
        text = re.sub(r'noncomputable def (\w+Chars) : List Char := (\[[^\n]*\])', quoted, text)
        def metadata(match):
            index = int(match[1])
            return match[0].split(':=')[0] + ':= ' + value(new['fields'][index][3])
        text = re.sub(r'noncomputable def momentMetadataField(\d+)Value : SourceJson := [^\n]*', metadata, text)
        def push(match):
            index = int(match[1])
            return match[0].split(':=')[0] + ':=\n  ' + value(new['rows'][index][2]) + ' :: acc'
        text = re.sub(r'noncomputable def momentRecordsChunk(\d+)Push \(acc : List SourceJson\) : List SourceJson :=\n[^\n]*', push, text)
        def typed(match):
            index = int(match[1])
            item = new['rows'][index][2]
            floors = ', '.join(f'({int(x)} : Int)' for x in item['log_gap_factor_floors_Q80'])
            return (f'noncomputable def momentTypedRecord{index:03d} : MomentRecord :=\n'
                    f'  {{ simplexId := {index},\n    factorFloorsQ80 := #[{floors}],\n'
                    f'    oldFloorQ96 := ({int(item["old_floor_Q96"])} : Int),\n'
                    f'    newFloorQ96 := ({int(item["new_floor_Q96"])} : Int) }}')
        text = re.sub(r'noncomputable def momentTypedRecord(\d+) : MomentRecord :=\n.*?\n    newFloorQ96 := [^\n]*', typed, text, flags=re.S)
        if suffix == 'DecodeMetadata':
            text = text.replace(
                '    parse_moment_metadata_logDenominator, parse_moment_metadata_finalDenominator,\n'
                '    get_moment_records_field, SourceJson.getArr?, pure_bind]',
                '    get_moment_records_field, SourceJson.getArr?]')
            text = text.replace('momentMetadataDecoded_cellId : Nat := 0',
                                'momentMetadataDecoded_cellId : Nat := 5')
            text = re.sub(r'(momentMetadataDecoded_sourceWitness : String := )[^\n]*',
                          lambda m: m[1] + string(new['fields'][1][3]), text)
        if suffix == 'Shape':
            text = text.replace('momentConcrete00.cellId = 0', 'momentConcrete00.cellId = 5')
        text = re.sub(r'\b\d{3,}\b', lambda m: str(replacements.get(int(m[0]), int(m[0]))), text)
        text = text.replace('Moment00', 'Moment05').replace('MOMENT00', 'MOMENT05')
        text = text.replace('ArchiveMomentData00', 'ArchiveMomentData05')
        for name in ['momentPacked', 'momentChars', 'momentRest', 'momentConcrete']:
            text = text.replace(name + '00', name + '05')
        text = text.replace('low-00-cell.witness.json', 'low-05-cell.witness.json')
        text = text.replace('moment00', 'moment05').replace('cell00', 'cell05')
        assert '\n+  ' not in text
        generated[suffix] = text
    for suffix, text in generated.items():
        target = SOURCE / ('P2OriginalSaving19Moment05' + suffix + '.lean')
        if target.exists():
            assert target.read_text() == text, ('Candidate changed after generation', target)
    if args.emit:
        assert args.emit in generated
        target = SOURCE / ('P2OriginalSaving19Moment05' + args.emit + '.lean')
        assert not target.exists(), target
        print('*** Begin Patch\n*** Add File: ' + str(target))
        print(''.join('+' + line + '\n' for line in generated[args.emit].splitlines()), end='')
        print('*** End Patch')
    else:
        print(json.dumps({'candidate_modules': len(generated),
                          'candidate_bytes': sum(len(x.encode()) for x in generated.values()),
                          'suffixes': sorted(generated), 'formal_acceptance': False}))


if __name__ == '__main__':
    main()
