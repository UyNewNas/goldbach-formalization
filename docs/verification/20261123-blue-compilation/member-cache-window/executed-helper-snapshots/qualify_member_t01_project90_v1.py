"""Qualify only90 new Member project candidates; stage authenticated payloads outside builds.
Derived from existing qualify_cdc_p6.py; no Lean/Lake/source compiler is invoked.
"""
import collections
import hashlib
import json
from pathlib import Path
import zipfile
import os
import sys
import tomllib
import subprocess
sys.dont_write_bytecode = True

BASE = Path('/workspace/artifacts')
ARCHIVE = BASE / 't01-fifth-objects-42753193835-1.zip'
CHECKPOINT = BASE / 't01-fifth-objects-42753193835-1/CHECKPOINT.json'
SELECTION = Path('/workspace/artifacts/member-t01-project90-20261123/NEW90_SELECTION.json')
PROJECT = Path('/workspace/blue-member-build')
TOOLCHAIN = Path('/workspace/toolchains/lean-4.33.0-rc1-linux')
OUT = BASE / 'member-t01-project90-20261123/qualification-v1'
OUT.mkdir(exist_ok=False)
EXECUTED_HELPER_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

cp = json.loads(CHECKPOINT.read_text())
sel = json.loads(SELECTION.read_text())
state = json.loads(Path('/workspace/blue-build-tools/member-runtime-evidence/state.json').read_text())
files = cp['files']
records = {}
unaccepted = {}
for group, source_map, rows, good in [
    ('native', sel['native_sources'], cp['all_guarded_package_compilations'], 'PACKAGE_COMPILE_CHECKPOINT_REQUIRES_VERIFIED_REBIND'),
    ('project', sel['project_sources'], cp['modules'], 'COMPILED_CHECKPOINT_ONLY_NOT_KERNEL_ACCEPTANCE'),
]:
    for row in rows:
        name = row.get('module')
        if name not in source_map:
            continue
        why = []
        if row['source']['sha256'] != source_map[name]['sha256']:
            why.append('SOURCE_SELECTION_MISMATCH')
        source_path = PROJECT / ('.lake/packages/goldbach' if group == 'native' else '') / source_map[name]['install_path']
        if not source_path.is_file() or sha(source_path) != source_map[name]['sha256']:
            why.append('INSTALLED_SOURCE_MISMATCH_OR_ABSENT')
        if row['classification'] != good:
            why.append('ORIGINAL_CHECKPOINT_QUARANTINED')
        if why:
            unaccepted[name] = why
        else:
            records[name] = {'group': group, 'original': row, 'selected_source': source_map[name], 'reasons': []}

archive = zipfile.ZipFile(ARCHIVE)
payload_cache = {}
def payload(record):
    p = record.get('payload')
    if not p:
        raise ValueError('No archived payload for ' + record['original_path'])
    raw = archive.read(p)
    assert len(raw) == record['bytes'] and hashlib.sha256(raw).hexdigest() == record['sha256'], p
    return raw

PRIOR_AUDIT = Path('/workspace/artifacts/cdc-generated-c-completion-20261123-v3-p6-member/PHYSICAL_INPUT_AUDIT.json')
PRIOR_RECEIPT = Path('/workspace/artifacts/cdc-generated-c-completion-20261123-v3-p6-member/CORRECTION_RECEIPT.json')
prior_receipt = json.loads(PRIOR_RECEIPT.read_text())
assert sha(PRIOR_AUDIT) == prior_receipt['physical_input_audit_sha256']
prior_rows = json.loads(PRIOR_AUDIT.read_text())
prior = {r['path']: r for r in prior_rows}
local_hashes = {}; physical_audit = {}; methods = collections.Counter()
def token(path):
    st = path.stat()
    return [st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]
def local_hash(path):
    key = str(path)
    if not path.is_file():return None
    stamp = token(path)
    if key in local_hashes and physical_audit[key]['stat_identity'] == stamp:return local_hashes[key]
    old = prior.get(key)
    if old is not None and old['stat_identity'] == stamp:
        value = old['sha256']; method = 'PRIOR_AUTHENTICATED_SHA_UNCHANGED_DEV_INODE_SIZE_MTIME_CTIME'
    else:
        value = sha(path); method = 'FRESH_SHA_NEW90_REQUIRED_CHANGED_OR_UNSEEN_FILE'
    assert token(path) == stamp, 'Physical file changed while hashing: ' + key
    local_hashes[key] = value; methods[method] += 1
    physical_audit[key] = {'path': key, 'sha256': value, 'stat_identity': stamp, 'method': method}
    return value
# Bind the existing archive/checkpoint without rehashing previously authenticated
# immutable bytes; this is metadata reuse, not requalification of the old617.
assert local_hash(ARCHIVE) == 'c506ac0c034e971c5554802a4e551762f122a42d25701b07a5a6c4c6471d4b7b'
assert local_hash(CHECKPOINT) == 'aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a'
assert cp['runtime_audit_valid'] and cp['all_dependency_source_pins_valid']
assert cp['runtime_state']['policy'] == state['policy']
config = tomllib.loads((PROJECT/'lakefile.toml').read_text())
assert config.get('name') == 'imbalancedChen'
assert config.get('moreLeanArgs') == ['-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000']
assert not config.get('leanOptions') and not config.get('weakLeanArgs')
assert all(not x.get('leanOptions') and not x.get('moreLeanArgs') and not x.get('weakLeanArgs') for x in config.get('lean_lib', []))
current_lock = {p['name']:p for p in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']}
for p in cp['packages']:
    assert p['pin_matches'] and p['rev'] == current_lock[p['name']]['rev']
    assert subprocess.check_output(['git','-C',str(PROJECT/'.lake/packages'/p['name']),'rev-parse','HEAD'],text=True).strip() == p['rev']

runtime_checks = []
for path, expected in cp['runtime_state']['runtime_sha256'].items():
    if path.startswith(cp['runtime_state']['realbin'] + '/'):
        local = TOOLCHAIN / 'bin' / Path(path).name
        runtime_checks.append({'local': str(local), 'expected': expected, 'observed': local_hash(local), 'matched': local_hash(local) == expected})
abi_checks = []
for row in cp['native_and_toolchain_library_ABI_receipts']:
    original = row['original_path']
    local = TOOLCHAIN / 'lib/lean' / Path(original).name if '/lib/lean/' in original else Path(original)
    abi_checks.append({'original': original, 'local': str(local), 'expected': row['sha256'], 'observed': local_hash(local), 'matched': local_hash(local) == row['sha256'], 'kind': row['role']})

assert runtime_checks and all(r['matched'] for r in runtime_checks), 'Pinned runtime binary mismatch'
assert all(r['matched'] for r in abi_checks if r['kind'] == 'pinned-toolchain-shared-library-ABI'), 'Pinned Lean shared ABI mismatch'

import_parts = {}
import_maps = {}
source_checks = {}
package_roots = {p['name']: PROJECT / '.lake/packages' / p['name'] for p in cp['packages']}

def package_of(name):
    origin = cp['actual_import_sources'].get(name)
    if not origin:
        return None
    return origin.get('package')

def local_artifact(name, remote):
    package = package_of(name)
    rel = Path(*name.split('.'))
    remote_base = Path(remote).name
    stem_base = rel.name
    suffix = remote_base[len(stem_base):] if remote_base.startswith(stem_base + '.') else None
    if suffix is None:
        for ext in ['.olean.server', '.olean.private', '.ir.sig', '.olean', '.ir']:
            if remote.endswith(ext):
                suffix = ext
                break
    if suffix is None:
        return None
    if package == 'pinned-lean-toolchain':
        return TOOLCHAIN / 'lib/lean' / (str(rel) + suffix)
    if package == 'project':
        return PROJECT / '.lake/build/lib/lean' / (str(rel) + suffix)
    if package in package_roots:
        return package_roots[package] / '.lake/build/lib/lean' / (str(rel) + suffix)
    return None

def check_source(name):
    if name in source_checks:
        return source_checks[name]
    origin = cp['actual_import_sources'].get(name)
    if not origin or 'source' not in origin:
        source_checks[name] = {'status': 'MISSING_ORIGINAL_SOURCE_RECEIPT'}
        return source_checks[name]
    package = origin['package']
    if package == 'project':
        local = PROJECT / (name.replace('.', '/') + '.lean')
    elif package == 'pinned-lean-toolchain':
        local = TOOLCHAIN / 'src/lean' / (name.replace('.', '/') + '.lean')
    else:
        local = package_roots[package] / (name.replace('.', '/') + '.lean')
    expected = origin['source']['sha256']
    got = local_hash(local)
    source_checks[name] = {'package': package, 'local': str(local), 'expected': expected, 'observed': got, 'status': 'MATCH' if got == expected else 'DIFFERENT_OR_MISSING'}
    return source_checks[name]

for index, (name, entry) in enumerate(records.items(), 1):
    row = entry['original']
    assert row['completed_guarded_compile_candidate'] and not row['missing_actual_import_artifacts']
    assert not row['missing_expected_direct_imports'] and not row['observed_output_descriptor_contradiction']
    assert all(q['matched'] for q in row['trace_output_descriptor_sidecar_checks'])
    assert payload(row['source']) == (PROJECT/entry['selected_source']['install_path']).read_bytes()
    trace = json.loads(payload(row['trace']))
    assert trace['schemaVersion'] == '2025-09-10' and trace['synthetic'] is False
    assert trace['depHash'] == row['lake_depHash']
    assert any(x[0] == 'Module.leanArgs: #[-DmaxRecDepth=100000, -DmaxHeartbeats=4000000]' for x in trace['inputs'])
    for cmd in row['guarded_source_commands']:
        assert cmd['tool'] == 'lean' and cmd['command'][1:4] == ['-t0','-j2','-M12288']
        assert cmd['input_args'][:2] == ['-DmaxRecDepth=100000','-DmaxHeartbeats=4000000']
        stem_old = row['trace']['original_path'].removesuffix('.trace')
        ir_old = row['setup']['original_path'].removesuffix('.setup.json')
        assert cmd['input_args'][2:] == [row['source']['original_path'], '-o', stem_old+'.olean',
            '-i', stem_old+'.ilean', '-c', ir_old+'.c', '--setup', row['setup']['original_path'], '--json'], 'Original/current compiler profile differs'
    assert row['guarded_source_commands']
    setup = json.loads(payload(row['setup']))
    assert setup['name'] == name and setup['package'] == 'imbalancedChen' and setup['options'] == {}
    assert not setup['dynlibs'] and not setup['plugins']
    assert trace['outputs']['m'] == setup['isModule']
    entry['setup_options'] = setup.get('options')
    entry['isModule'] = setup.get('isModule')
    normalized = {}
    dependencies = set()
    bad = []
    for imported, arrays in setup['importArts'].items():
        imported_source = check_source(imported)
        if imported_source['status'] != 'MATCH':
            bad.append('IMPORTED_SOURCE_MISMATCH:' + imported)
        normalized[imported] = []
        for array in arrays:
            for remote in array:
                absolute = str(Path(row['command']['cwd']) / remote) if not remote.startswith('/') else remote
                receipt = files.get(absolute)
                if not receipt:
                    bad.append('MISSING_ORIGINAL_IMPORT_RECEIPT:' + absolute)
                    continue
                expected = receipt['sha256']
                normalized[imported].append([absolute, expected])
                key = absolute
                if key not in import_parts:
                    local = local_artifact(imported, absolute)
                    observed = local_hash(local) if local else None
                    provider = imported if imported in records and receipt.get('payload') else None
                    if observed == expected:
                        status = 'LOCAL_HASH_MATCH'
                    elif provider:
                        provider_outputs = records[provider]['original'].get('facet_files', [])
                        if records[provider]['group'] == 'project':
                            provider_outputs = [r for r in files.values() if r['original_path'] in records[provider]['original']['required_output_parts']]
                        good_output = any(r['sha256'] == expected and r['original_path'] == absolute for r in provider_outputs)
                        status = 'MATCHING_SELECTED_CHECKPOINT_PROVIDER' if good_output else 'UNBOUND_PROVIDER_FACET'
                    else:
                        status = 'LOCAL_MISMATCH_OR_MISSING_NO_SELECTED_PROVIDER'
                    import_parts[key] = {'module': imported, 'package': package_of(imported), 'remote': absolute, 'local': str(local) if local else None, 'sha256': expected, 'bytes': receipt['bytes'], 'local_sha256': observed, 'status': status, 'checkpoint_provider': provider, 'payload': receipt.get('payload')}
                part = import_parts[key]
                if part['status'] == 'MATCHING_SELECTED_CHECKPOINT_PROVIDER':
                    dependencies.add(part['checkpoint_provider'])
                elif part['status'] != 'LOCAL_HASH_MATCH':
                    bad.append('IMPORTED_ARTIFACT_UNBOUND:' + absolute)
    mapped_hash = hashlib.sha256(json.dumps(normalized, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    assert mapped_hash == row['actual_import_map_sha256'], name
    for dynamic in setup.get('dynlibs', []) + setup.get('plugins', []):
        remote = dynamic.get('path') if isinstance(dynamic, dict) else dynamic
        bad.append('NATIVE_DYNAMIC_LIBRARY_REQUIRES_ABI_REBUILD:' + remote)
    entry['actual_import_map_sha256_verified'] = mapped_hash
    entry['checkpoint_dependencies'] = sorted(dependencies)
    entry['import_part_keys'] = sorted(p for imported in normalized.values() for p, h in imported)
    entry['reasons'].extend(sorted(set(bad)))
    if index % 10 == 0:
        print('checked_setup_maps', index, 'unique_import_parts', len(import_parts), flush=True)

# A blocked provider blocks each consumer that consumed its exact previous bytes.
changed = True
while changed:
    changed = False
    for name, entry in records.items():
        blocked = [dep for dep in entry['checkpoint_dependencies'] if records[dep]['reasons']]
        for dep in blocked:
            reason = 'BLOCKED_CHECKPOINT_IMPORT_PROVIDER:' + dep
            if reason not in entry['reasons']:
                entry['reasons'].append(reason)
                changed = True

manifest_groups = {}
staged_paths = {}
excluded_native_facets = []
for name, entry in records.items():
    row = entry['original']
    facets = row.get('facet_files')
    if facets is None:
        prefix = '/home/runner/work/_temp/t01-project/.lake/build/'
        stem_lib = prefix + 'lib/lean/' + name.replace('.', '/')
        stem_ir = prefix + 'ir/' + name.replace('.', '/')
        facets = [r for r in files.values() if r['original_path'].startswith((stem_lib + '.', stem_ir + '.'))]
    output_records = []
    for facet in facets:
        original = facet['original_path']
        marker = '/.lake/packages/goldbach/' if entry['group'] == 'native' else '/t01-project/'
        rel = original.split(marker, 1)[1]
        install = ('.lake/packages/goldbach/' if entry['group'] == 'native' else '') + rel
        # Never install original source text or any system-native executable bytes.
        if not rel.startswith('.lake/build/'):
            continue
        if any(rel.endswith(suffix) for suffix in ('.so', '.a', '.o', '.o.export', '.o.noexport')):
            excluded_native_facets.append({'module': name, 'install_path': install, 'sha256': facet['sha256']})
            continue
        assert rel.endswith(('.olean','.olean.server','.olean.private','.ilean','.ir','.ir.sig','.c','.hash','.trace','.setup.json')), 'Unsupported native/extra output'
        staged = OUT / 'candidate-tree' / install
        staged.parent.mkdir(parents=True, exist_ok=True)
        raw = payload(facet)
        destination = PROJECT / install
        if destination.exists() and local_hash(destination) != facet['sha256']:
            entry['reasons'].append('EXISTING_DISTINCT_FACET_MUST_NOT_OVERWRITE:' + install)
        staged.write_bytes(raw)
        staged_paths[install] = {'sha256': facet['sha256'], 'bytes': len(raw), 'archive_payload': facet['payload'], 'module': name, 'status': 'BLOCKED' if entry['reasons'] else 'HASH_BOUND_FOR_KERNEL_REPLAY'}
        output_records.append({'install_path': install, 'sha256': facet['sha256'], 'bytes': len(raw), 'archive_payload': facet['payload']})
    manifest_groups[name] = {'group': entry['group'], 'classification': 'UNACCEPTED_IMPORT_OR_SOURCE_MISMATCH' if entry['reasons'] else 'HASH_BOUND_CANDIDATE_REQUIRES_KERNEL_REPLAY', 'source': entry['selected_source'], 'setup_options': entry['setup_options'], 'isModule': entry['isModule'], 'actual_import_map_sha256_verified': entry['actual_import_map_sha256_verified'], 'checkpoint_dependencies': entry['checkpoint_dependencies'], 'import_part_keys': entry['import_part_keys'], 'reasons': entry['reasons'], 'facets': output_records, 'kernel_verified': False}

# Existing distinct outputs discovered during staging also block consumers.
changed = True
while changed:
    changed = False
    for name, entry in records.items():
        for dep in entry['checkpoint_dependencies']:
            reason = 'BLOCKED_CHECKPOINT_IMPORT_PROVIDER:' + dep
            if records[dep]['reasons'] and reason not in entry['reasons']:
                entry['reasons'].append(reason); changed = True
for name, entry in records.items():
    manifest_groups[name]['reasons'] = sorted(set(entry['reasons']))
    manifest_groups[name]['classification'] = 'UNACCEPTED_IMPORT_OR_SOURCE_MISMATCH' if entry['reasons'] else 'HASH_BOUND_CANDIDATE_REQUIRES_KERNEL_REPLAY'
assert sha(Path(__file__)) == EXECUTED_HELPER_SHA256
(OUT/'PHYSICAL_INPUT_AUDIT.json').write_text(json.dumps(list(physical_audit.values()),separators=(',',':'))+'\n')
result = {
    'schema': 'member-new90-source-import-hash-qualification-v1',
    'helper_sha256': EXECUTED_HELPER_SHA256,
    'prior_physical_audit': {'path':str(PRIOR_AUDIT),'sha256':prior_receipt['physical_input_audit_sha256']},
    'physical_audit': {'path':str(OUT/'PHYSICAL_INPUT_AUDIT.json'),'sha256':sha(OUT/'PHYSICAL_INPUT_AUDIT.json')},
    'physical_identity_methods':dict(methods),
    'scope_new_project_candidates':90,
    'existing617_or_original44k_global_requalification_run':False,
    'source_compiler_or_Lake_invoked':False,
    'build_tree_files_written':False,
    'status': 'CANDIDATE_STAGING_ONLY_NO_LEAN_LOADING_OR_MATHEMATICAL_ACCEPTANCE',
    'archive': {'path': str(ARCHIVE), 'artifact_id': 13749339878, 'sha256': 'c506ac0c034e971c5554802a4e551762f122a42d25701b07a5a6c4c6471d4b7b', 'bytes': ARCHIVE.stat().st_size},
    'checkpoint_sha256': local_hash(CHECKPOINT), 'selection': {'path': str(SELECTION), 'sha256': sha(SELECTION)},
    'target_project': str(PROJECT), 'original_runtime_audit_valid': cp['runtime_audit_valid'],
    'original_package_source_pins_valid': cp['all_dependency_source_pins_valid'],
    'runtime_policy_matches': cp['runtime_state']['policy'] == state['policy'], 'runtime_binary_checks': runtime_checks,
    'abi_checks': abi_checks, 'native_executable_facets_excluded': excluded_native_facets,
    'modules': manifest_groups, 'preliminary_unaccepted': unaccepted,
    'import_parts': import_parts, 'import_source_checks': source_checks, 'staged_paths': staged_paths,
    'summary': {'module_groups': len(manifest_groups), 'native': sum(r['group'] == 'native' for r in manifest_groups.values()), 'project': sum(r['group'] == 'project' for r in manifest_groups.values()), 'hash_bound_candidate_groups': sum(not r['reasons'] for r in manifest_groups.values()), 'blocked_groups': sum(bool(r['reasons']) for r in manifest_groups.values()), 'unique_import_parts': len(import_parts), 'import_part_statuses': dict(collections.Counter(r['status'] for r in import_parts.values())), 'staged_files': len(staged_paths), 'staged_bytes': sum(r['bytes'] for r in staged_paths.values())},
    'install_policy': 'No sources are staged. Recheck imports/source/runtime immediately before use; do not install blocked groups. Exact Lean shared library and runtime hashes match, while host C runtime libraries differ; no system-native executables are eligible. Kernel replay and complete type/transitive-axiom audit remain required. Absolute original setup paths are retained as historical receipts and require separate mapping if regenerating Lake setups/traces.'
}
(OUT / 'MANIFEST.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result['summary'], indent=2), flush=True)
print('manifest', OUT / 'MANIFEST.json', flush=True)
