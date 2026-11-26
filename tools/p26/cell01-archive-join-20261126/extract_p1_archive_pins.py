#!/usr/bin/env python3
"""Read exact extra supplier pins from the existing accepted Archive context."""
from pathlib import Path
import hashlib
import json
import sys


def fp(path):
    path = Path(path)
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1048576), b''):
            h.update(data)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': h.hexdigest()}


request = json.loads(Path(sys.argv[1]).read_text())
attempt = Path('/workspace/p26-continuation-59264dd64286/archive-bridges/attempts/20261126-geometry01-transparent-v4')
result_pin = fp(attempt / 'RESULT.json')
assert result_pin['sha256'] == '79328a828a252a88d6c62541b6f15c06a2847e9919271c321ed86ae557912590'
result = json.loads((attempt / 'RESULT.json').read_text())
assert result['status'] == 'PASS_ARCHIVE_BRIDGES'
inputs = json.loads((attempt / 'INPUT_FINGERPRINTS.json').read_text())
rows = []
for module, expected in request['suppliers'].items():
    if module in inputs['canonical_modules']:
        chosen = inputs['canonical_modules'][module]
        origin = 'existing_archive_canonical'
    else:
        records = [x for x in result['records'] if x['module'] == module]
        assert len(records) == 3 and [x['mode'] for x in records] == ['normal', 'kernel', 'owned']
        chosen = json.loads(Path(records[0]['receipt']['path']).read_text())
        origin = 'existing_archive_owner'
    source, obj = chosen['source'], chosen['object']
    assert all(source[k] == expected[k] for k in ('bytes', 'sha256'))
    for pin in (source, obj):
        actual = fp(pin['path'])
        assert all(actual[k] == pin[k] for k in ('bytes', 'sha256'))
    rows.append({'module': module, 'source': source, 'object': obj, 'authority_kind': origin})
print(json.dumps({'schema': 'p26_archive_extra_canonical_pins_v1', 'suppliers': rows,
                  'authority_result': result_pin, 'inputs': fp(attempt / 'INPUT_FINGERPRINTS.json'),
                  'proof_commands': 0}, indent=2))
