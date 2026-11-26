"""Admit root's final explicit prepared-only inputs before the local draft build."""
from pathlib import Path
import hashlib
import json

ROOT = Path('/tmp/p24-integration-repairs-20261126')
PLAN = ROOT / 'canonical-a-publication-draft02-inputs.json'
PREFIX = 'docs/source-only/20261125-p24-original-compact/canonical-a-b55'
DIAG = 'diagnostics/canonical-a-b55-20261126'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


original_plan = PLAN.read_bytes()
plan = json.loads(original_plan)
assert len(plan['text_inputs']) == 351
assert sha(original_plan) == '3b4862c0f1c1f26711dc3ab0e9097112247437b9d1a85c0005ca28a0b8b72390'
authorized_preparation_updates = {
    str(ROOT / 'make_canonical_a_publication_draft02.py'),
    str(ROOT / 'build_canonical_a_publication_draft02.py'),
    str(ROOT / 'canonical_a_draft02_extra_validation.py'),
}
changes = []
for item in plan['text_inputs']:
    raw = Path(item['origin']).read_bytes()
    if item['sha256'] != sha(raw) or item['bytes'] != len(raw):
        assert item['origin'] in authorized_preparation_updates, item['origin']
        changes.append({'path': item['origin'], 'old_sha256': item['sha256'],
                        'new_sha256': sha(raw), 'new_bytes': len(raw)})
        item.update(bytes=len(raw), sha256=sha(raw))


def add(path, target, role):
    path = Path(path)
    assert not any(item['origin'] == str(path) or item['target'] == target for item in plan['text_inputs'])
    raw = path.read_bytes()
    assert raw.decode().encode() == raw
    plan['text_inputs'].append({'origin': str(path), 'target': target, 'bytes': len(raw),
                               'sha256': sha(raw), 'role': role})


folder = Path('/tmp/p24-global-duplicate-repairs-b55-20261126/isolated-wrappers-01')
manifest_path = folder / 'six-isolated-wrappers-manifest.json'
wrappers = json.loads(manifest_path.read_bytes())
assert not wrappers['executed'] and not wrappers['canonical_credit'] and len(wrappers['wrappers']) == 6
add(manifest_path, PREFIX + '/prepared-six-proof-candidates/six-isolated-wrappers-manifest.json',
    'six isolated wrappers prepared only, no execution or promotion')
for wrapper in wrappers['wrappers']:
    for key in ['shell', 'python', 'patch']:
        item = wrapper[key]
        path = Path(item['path'])
        raw = path.read_bytes()
        assert path.parent == folder and len(raw) == item['bytes'] and sha(raw) == item['sha256']
        add(path, DIAG + '/prepared-six-proof-candidates/wrappers/' + path.name,
            'prepared-only single-module workflow with original gates; not executed')

recovery = Path('/tmp/p24-native-recovery-readonly-20261126')
index = json.loads((recovery / 'locked-cache-source-index.json').read_bytes())
assert index['source_code_not_executed'] and index['status'] == 'prepared-only'
for name in ['exact-native-restoration-design.md', 'locked-cache-source-index.json', 'prepared-only-verification.json']:
    add(recovery / name, PREFIX + '/native-restoration-prepared/' + name,
        'read-only exact restoration design; no download/restore executed; blocked state unchanged')
for row in index['files']:
    path = Path(row['path'])
    raw = path.read_bytes()
    assert path.parent == recovery and len(raw) == row['bytes'] and sha(raw) == row['sha256']
    add(path, DIAG + '/native-restoration-prepared/' + path.name,
        'locked official Cache source for read-only analysis, not executed')

add(Path(__file__), DIAG + '/' + Path(__file__).name,
    'local-only explicit input-freeze amendment; no compiler/remote/Git operations')
plan['initial_input_plan_sha256'] = sha(original_plan)
plan['preparation_updates_before_final_freeze'] = changes
plan['final_additions_authorized_by_root'] = [
    'six isolated wrapper manifest and its exact shell/python/patch inputs',
    'exact native restoration design and locked source index plus named source inputs',
]
raw = (json.dumps(plan, ensure_ascii=False, indent=2) + '\n').encode()
PLAN.write_bytes(raw)
print(json.dumps({'text_inputs': len(plan['text_inputs']), 'input_plan_bytes': len(raw),
                  'input_plan_sha256': sha(raw), 'changed_preparation_files': len(changes),
                  'original_builder_unchanged': sha((ROOT / 'build_canonical_a_publication.py').read_bytes())
                    == plan['original_builder']['sha256']}, sort_keys=True))
