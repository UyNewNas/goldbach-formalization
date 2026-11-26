#!/usr/bin/env python3
"""Recover only published cell05 evidence; no Lean execution or cloud access."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import re
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OLD = REPO / 'tools/p26/scalable'
DOCS = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05'
ARCHIVES = {
    'pilot': ('cell05-scalable-completed-evidence.tar.xz', 1462880,
              '1fb3fd544b39648bbcf8511ac559ce3ccce98e9fc6ccffc2b164e464046da505',
              'ACCEPTED_EXPORT_MANIFEST.json', 111),
    'raw05-context': ('raw05-current-context-kernel-addendum.tar.xz', 11944,
                      'a37b3796dbc51f9a2b103bb851d0f8e3a4aaf4ca0860c6f0c1f5e53cce849d67',
                      'EXPORT_MANIFEST.json', 9),
    'raw05-history': ('raw05-supplier-evidence.tar.xz', 184036,
                      'f4feab458fec447cb09e4d375102e2ecd3218d88d8336302eafc860d112a60c6',
                      'RECOVERED_EXPORT_MANIFEST.json', 74),
}


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def fp(path):
    path = Path(path)
    return {'path': str(path.relative_to(REPO)), **pin(path.read_bytes())}


def write_new(path, value):
    path = Path(path)
    data = value if isinstance(value, bytes) else value.encode() if isinstance(value, str) else (json.dumps(value, indent=2) + '\n').encode()
    if path.exists():
        assert path.read_bytes() == data, ('Frozen candidate drift', str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as out:
            out.write(data)


def read_archive(key):
    name, count_bytes, digest, manifest_name, count = ARCHIVES[key]
    path = DOCS / name
    assert pin(path.read_bytes()) == {'bytes': count_bytes, 'sha256': digest}
    files = {}
    with tarfile.open(path, 'r:xz') as archive:
        for item in archive.getmembers():
            rel = PurePosixPath(item.name)
            assert item.isfile() and not rel.is_absolute() and '..' not in rel.parts
            assert item.name not in files
            files[item.name] = archive.extractfile(item).read()
    manifest = json.loads(files[manifest_name])
    assert len(manifest['members']) == count
    assert {row['member'] for row in manifest['members']} | {manifest_name} == set(files)
    for row in manifest['members']:
        assert pin(files[row['member']]) == {k: row[k] for k in ('bytes', 'sha256')}
    return files


def protected_files():
    paths = (DOCS / 'HANDOFF_STAGING_FILES.txt').read_text().splitlines()
    assert len(paths) == len(set(paths)) == 70
    return [fp(REPO / path) for path in paths]


def main():
    protected = protected_files()
    archives = {key: read_archive(key) for key in ARCHIVES}
    selected = {
        'pilot': {name: data for name, data in archives['pilot'].items()
                  if name.startswith('verification/') or name.startswith('tools/p26/scalable/owned-audits/')
                  or name == 'ACCEPTED_EXPORT_MANIFEST.json'},
        'raw05-context': archives['raw05-context'],
        'raw05-history': {name: data for name, data in archives['raw05-history'].items()
                          if not name.endswith('.olean')},
    }
    members = []
    for family, files in selected.items():
        for name, data in sorted(files.items()):
            relative = 'baseline/' + family + '/' + name
            write_new(HERE / relative, data)
            members.append({'relative_path': relative, **pin(data)})
    assert len(members) == 154, len(members)
    pilot = archives['pilot']
    success_member = json.loads(pilot['ACCEPTED_EXPORT_MANIFEST.json'])['success_member']
    success = json.loads(pilot[success_member])
    old_stage = PurePosixPath(success['stage'])
    verifier_name = str(PurePosixPath(success['verifier_manifest']['path']).relative_to(old_stage))
    verifier = json.loads(pilot[verifier_name])
    old_targets = {row['module']: row for row in verifier['targets'] if row['cell'] == 5}
    suppliers = []
    current = json.loads(archives['raw05-context']['BEFORE.json'])
    groups = current['nine_supplier_sources_objects_and_sidecars']
    assert len(groups) == 18 and all(len(group['files']) == 1 for group in groups)
    current_map = {(group['module'], group['kind']): group['files'][0] for group in groups}
    modules = sorted({module for module, _ in current_map} | set(old_targets))
    assert len(modules) == 15
    for module in modules:
        rel = module.replace('.', '/')
        src = pilot['project/' + rel + '.lean']
        obj = pilot['objects/' + rel + '.olean']
        assert src == (REPO / (rel + '.lean')).read_bytes()
        if module not in old_targets:
            for kind, data in [('source', src), ('object', obj)]:
                assert pin(data) == {k: current_map[module, kind][k] for k in ('bytes', 'sha256')}
        else:
            assert pin(src) == {k: old_targets[module]['source'][k] for k in ('bytes', 'sha256')}
        suppliers.append({'module': module, 'source': pin(src), 'object': pin(obj),
                          'project_imports': re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', src.decode()),
                          'evidence_basis': 'pilot_18_steps' if module in old_targets else 'published_current_context_closure',
                          'must_not_recompile': True})
    write_new(HERE / 'SUPPLIER_REGISTRY.json', {
        'schema': 'cell05_complete_suppliers_v2', 'suppliers': suppliers, 'supplier_count': 15,
        'accepted_old_owners': sorted(old_targets), 'expected_object_sidecars': [],
        'runtime_binaries': {key: current[key] for key in ('lean_binary', 'leanchecker_binary')},
        'full_supplier_kernel_closed_requires_capsule_validation': True})
    write_new(HERE / 'BASELINE_EVIDENCE.json', {
        'schema': 'cell05_complete_baseline_v2', 'members': members,
        'archives': {key: fp(DOCS / item[0]) for key, item in ARCHIVES.items()},
        'published_files': protected, 'published_file_count': 70,
        'capsule_members': 154, 'accepted_pilot_steps': 18, 'accepted_pilot_owned_declarations': 2054,
        'raw05_current_context_addendum_required': True,
        'original_pilot_closed_boolean_alone_is_insufficient': True,
        'old_Lean_executions_for_recovery': 0})
    write_new(HERE / 'receipt_support.py', (OLD / 'Geometry01Decoding_verify.py').read_bytes())
    assert protected_files() == protected
    print(json.dumps({'status': 'PUBLISHED_BASELINE_RECOVERED', 'capsule_members': len(members),
                      'suppliers': len(suppliers), 'old_Lean_executions': 0}))


if __name__ == '__main__':
    main()
