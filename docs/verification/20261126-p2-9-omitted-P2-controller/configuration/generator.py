#!/usr/bin/env python3
"""Generate only a new, isolated Omitted configuration from the accepted raw preflight."""
import base64
import copy
import difflib
import hashlib
import json
from pathlib import Path
import tomllib

SOURCE = Path('/dev/shm/p29-omitted-controller-1126/OMITTED_PREFLIGHT_ORIGINAL_RESULT.json')
OUT = Path('/dev/shm/p29-omitted-config-delta-1126')
TARGET = 'ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall'
NAMES = ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')
ROOTS = ('/workspace/goldbach-p2', '/workspace/p2-saving16-20261125')

def identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}

raw = SOURCE.read_bytes()
assert identity(raw) == {'bytes': 60957, 'sha256': 'f8acaf368810fed58d3691061d224eb0429aacde902cc73133f40a1a7aa31a4f',
                         'git_blob': '5d7923d168ebe2bdedc1baf63934468b4281593a'}
data = json.loads(raw)
assert data['status'] == 'BOUNDED_CURRENT_METADATA_CAPTURED_NOT_A_NEW_IMPORT_OR_PROOF_QUALIFICATION'
pairs = data['project_configuration_candidates']
assert set(pairs) == set(ROOTS)
original = {}
recorded = {}
for root in ROOTS:
    recorded[root] = {}
    for name in NAMES:
        row = pairs[root]['files'][name]
        assert row['content_status'] == 'COMPLETE_ORIGINAL_READ'
        content = base64.b64decode(row['content_base64'], validate=True)
        observed = identity(content)
        assert observed['bytes'] == row['bytes'] and observed['sha256'] == row['sha256']
        if name in original:
            assert original[name] == content
        else:
            original[name] = content
        recorded[root][name] = {k: v for k, v in row.items() if k != 'content_base64'}
    assert pairs[root]['files']['lakefile.lean']['status'] == 'NO_ENTRY_AT_THIS_EXACT_PATH'

accepted_unit_path = Path('/workspace/scratch/005887317b49/p29-current/unit-tail-qualified/project/lakefile.toml')
accepted_unit_bytes = accepted_unit_path.read_bytes()
assert identity(accepted_unit_bytes)['sha256'] == '035c29575c6d6f626eba65025fd7ac56198e12be0e80ba584b4030a2f2c670cd'
accepted_unit_config = tomllib.loads(accepted_unit_bytes.decode())
unit_lib = accepted_unit_config['lean_lib']
assert unit_lib == [{'name':'ImbalancedChen',
                    'roots':['ImbalancedChen.P2FiniteMarkedGamma5UnitTailCount'],
                    'globs':['ImbalancedChen.P2FiniteMarkedGamma5UnitTailCount']}]

before_toml = original['lakefile.toml']
old_cfg = tomllib.loads(before_toml.decode())
assert old_cfg['lean_lib'] == [{'name':'ImbalancedChen'}]
assert [x['name'] for x in old_cfg['require']] == ['mathlib', 'goldbach']
goldbach_block = (b'[[require]]\nname = "goldbach"\n'
                 b'git = "https://github.com/subfish-zhou/goldbach-lean.git"\n'
                 b'rev = "09b97db5764ade1246bfb77206baa1b124760958"\n\n')
assert before_toml.count(goldbach_block) == 1
goldbach_offset = before_toml.index(goldbach_block)
without_goldbach = before_toml.replace(goldbach_block, b'', 1)
lib_header = b'[[lean_lib]]\nname = "ImbalancedChen"\n'
assert without_goldbach.count(lib_header) == 1
scope = ('roots = ' + json.dumps([TARGET]) + '\nglobs = ' + json.dumps([TARGET]) + '\n').encode()
after_toml = without_goldbach.replace(lib_header, lib_header + scope, 1)
assert after_toml.count(scope) == 1
back = after_toml.replace(scope, b'', 1)
assert back[:goldbach_offset] + goldbach_block + back[goldbach_offset:] == before_toml
new_cfg = tomllib.loads(after_toml.decode())
expected_cfg = copy.deepcopy(old_cfg)
expected_cfg['require'] = [x for x in expected_cfg['require'] if x['name'] != 'goldbach']
expected_cfg['lean_lib'][0]['roots'] = [TARGET]
expected_cfg['lean_lib'][0]['globs'] = [TARGET]
assert new_cfg == expected_cfg

before_manifest = original['lake-manifest.json']
mtext = before_manifest.decode()
old_manifest = json.loads(mtext)
assert len(old_manifest['packages']) == 11
assert old_manifest['packages'][0]['name'] == 'goldbach'
assert sum(x['name'] == 'goldbach' for x in old_manifest['packages']) == 1
start = mtext.index('[', mtext.index('"packages"')) + 1
while mtext[start].isspace():
    start += 1
first, end = json.JSONDecoder().raw_decode(mtext, start)
assert first == old_manifest['packages'][0]
while mtext[end].isspace():
    end += 1
assert mtext[end] == ','
end += 1
while mtext[end].isspace():
    end += 1
removed_manifest = mtext[start:end]
after_manifest_text = mtext[:start] + mtext[end:]
assert after_manifest_text[:start] + removed_manifest + after_manifest_text[start:] == mtext
after_manifest = after_manifest_text.encode()
new_manifest = json.loads(after_manifest)
expected_manifest = copy.deepcopy(old_manifest)
expected_manifest['packages'] = expected_manifest['packages'][1:]
assert new_manifest == expected_manifest
assert len(new_manifest['packages']) == 10
assert all(x['name'] != 'goldbach' for x in new_manifest['packages'])
assert next(x for x in new_manifest['packages'] if x['name'] == 'mathlib')['rev'] == 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
post = {'lean-toolchain': original['lean-toolchain'],
        'lakefile.toml': after_toml, 'lake-manifest.json': after_manifest}
assert post['lean-toolchain'] == original['lean-toolchain']

# This directory is reserved to this generator; no original config or controller is written.
for label, contents in (('original', original), ('postimage', post)):
    target_dir = OUT / label
    target_dir.mkdir(exist_ok=False)
    for name, content in contents.items():
        with (target_dir / name).open('xb') as stream:
            stream.write(content)
patch = ''.join(''.join(difflib.unified_diff(original[name].decode().splitlines(True),
                                          post[name].decode().splitlines(True),
                                          fromfile='original/' + name,
                                          tofile='postimage/' + name))
                for name in NAMES)
with (OUT / 'CONFIG_DELTA.patch').open('x') as stream:
    stream.write(patch)
assert SOURCE.read_bytes() == raw
result = {
    'schema': 'p29_omitted_new_root_exact_configuration_postimage_v1',
    'status': 'GENERATED_AND_STATICALLY_CHECKED_NOT_RUN_BY_LAKE',
    'target': TARGET,
    'input_preflight': {'path': str(SOURCE), **identity(raw)},
    'two_recorded_roots_have_identical_three_original_files': True,
    'original_recorded_config_identities': recorded,
    'original': {name: {'path': str(OUT/'original'/name), **identity(content)} for name, content in original.items()},
    'postimage': {name: {'path': str(OUT/'postimage'/name), **identity(content)} for name, content in post.items()},
    'exact_patch': {'path': str(OUT/'CONFIG_DELTA.patch'), **identity(patch.encode())},
    'syntax_reference': {'path': str(accepted_unit_path), **identity(accepted_unit_bytes),
                         'scope': 'Reuse the already accepted Unit128 single-module roots/globs TOML form at the same toolchain.'},
    'changes': ['Remove the one goldbach require block from lakefile.toml.',
                'Add roots/globs arrays containing only the OmittedPrimeWall target.',
                'Remove only the goldbach package entry and its separating whitespace/comma from the original manifest.'],
    'mechanical_checks': {'TOML_parses_with_tomllib': True, 'JSON_parses': True,
                          'TOML_semantic_delta_exact': True, 'manifest_semantic_delta_exact': True,
                          'raw_inverse_splices_recover_both_original_changed_files': True,
                          'toolchain_byte_identical': True,
                          'all_ten_retained_package_records_and_order_identical': True,
                          'preflight_original_file_unchanged': True},
    'retained_package_pins': new_manifest['packages'],
    'preserved_fields': ['package name/version/defaultTargets', 'mathlib direct require including URL/rev',
                         'all ten retained manifest entries including LeanArchitect', 'packagesDir/version/lakeDir/fixedToolchain',
                         'original lean-toolchain', 'all fields outside the three enumerated deltas'],
    'boundary': 'A new isolated root configuration only. No old source/config/controller is changed. No package checkout, compiled header selection, facet graph or successful compilation is claimed. The current actual-import gate remains required.',
    'Lean_calls': 0, 'remote_calls': 0, 'old_graph_reads': 0, 'new_formal_credit': 0
}
output = (json.dumps(result, ensure_ascii=False, indent=2) + '\n').encode()
with (OUT / 'CONFIG_IDENTITY.json').open('xb') as stream:
    stream.write(output)
print(json.dumps({'identity': identity(output), 'path': str(OUT/'CONFIG_IDENTITY.json'),
                  'postimage': result['postimage'], 'patch': result['exact_patch']}))
