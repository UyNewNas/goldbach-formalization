"""GitHub-only caller binding for the exact Stored064--071 source packet.

The shared coherent-cache bundle owns all restoration and compiler admission.
This caller binds the existing generator, source hashes, original acceptance
gates, and retained current files. It never supplies a cache-repair fallback.
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import tarfile

HERE = Path(__file__).resolve().parent
SELECTION_SHA = '7aa3efa21f7877ffa022cf7f94265063ef20f9a0abaf106e5c2d003431df7e4b'  # static postimage packet, CI gates mandatory
PROFILE_SHA = '26a6b01a52446ad6aae63d5201330b902ec94a1171fb1f0baf9fc61016098491'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def checked(path, record):
    path = Path(path)
    require(path.is_file() and not path.is_symlink(), 'Missing/nonregular caller input: ' + str(path))
    require(path.stat().st_size == record['bytes'] and sha(path) == record['sha256'],
            'Caller input bytes changed: ' + str(path))


def write(path, value):
    path = Path(path)
    require(not path.exists(), 'Refusing caller receipt overwrite: ' + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes((json.dumps(value, indent=2) + '\n').encode())


def context():
    require(SELECTION_SHA is not None, "UNPUBLISHED DRAFT: exact source-selection postimages not bound")
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux', 'GitHub Linux only')
    workspace = Path(os.environ['GITHUB_WORKSPACE']).resolve()
    control_path = Path(os.environ['CACHE_ROOT_CONTROL']).resolve()
    require(control_path == HERE / 'ROOT_CONTROL.json', 'Wrong exact Stored control path')
    control = read(control_path)
    tools = (workspace / control['bundle_path']).resolve()
    require(tools.is_relative_to(workspace), 'Shared tool path escapes immutable checkout')
    sys.path.insert(0, str(tools))
    from coherent_cache import bind_inputs
    binding = bind_inputs('STORED_PARENT')
    require(os.environ['SOURCE_COMMIT'] == os.environ['GITHUB_SHA'], 'Stored source identity differs from actual driver')
    for row in control['reviewed_caller_files'] + control['unchanged_original_inputs']:
        target = (workspace / row['path']).resolve()
        require(target.is_relative_to(workspace), 'Caller manifest path escape')
        checked(target, row)
    selection_path = workspace / control['source_selection']['path']
    require(sha(selection_path) == SELECTION_SHA, 'Wrong unchanged new8 selection')
    selection = read(selection_path)
    require(selection['new_modules'] == [f'ImbalancedChen.Data.P5SubdivisionStoredBlock{i:03}' for i in range(64, 72)],
            'Wrong selected new8 graph')
    protected = [selection['parent']['module']] + [f'ImbalancedChen.Data.P5SubdivisionStoredBlock{i:03}' for i in range(64)]
    require(control['driver_base'] == 'c7ccad3c900a544514a13cec57a0d40db0442e76'
            and control['driver_branch'] == 'ci/stored-blocks-064-071-20261113', 'Wrong actual base or branch')
    require(control['source_admission'] == {'new_modules': selection['new_modules'],
            'protected_modules': protected, 'audit_filename': 'StoredBatchAudit.lean'}, 'Wrong explicit Stored source admission')
    require(selection['forbidden_old_source_compile_modules'] == protected
            and selection['forbidden_old_kernel_replay_modules'] == protected
            and selection['kernel_replay_scope'] == selection['new_modules']
            and selection['owned_types_axioms_scope'] == selection['new_modules'], 'Old/new source or replay boundary changed')
    return workspace, control, binding, selection


def source_rows(project, selection, before):
    checked(project / 'lakefile.toml', {'bytes': 487, 'sha256': PROFILE_SHA})
    checked(project / selection['parent']['install_path'], selection['parent'])
    rows = []
    for row in selection['files']:
        expected = row['pre_input'] if before else row
        path = project / row['install_path']
        checked(path, expected)
        rows.append({'module': row['module'], 'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path)})
    return rows


def preflight():
    workspace, control, binding, selection = context()
    logs = Path(os.environ['LOGS'])
    logs.mkdir(parents=True, exist_ok=True)
    write(logs / 'STORED_DRIVER_BINDING.json', {'binding': binding,
          'control_sha256': sha(HERE / 'ROOT_CONTROL.json'), 'source_selection_sha256': SELECTION_SHA,
          'profile_sha256': PROFILE_SHA, 'new_modules': selection['new_modules'],
          'protected_modules': selection['forbidden_old_source_compile_modules'],
          'parent_source_compile_allowed': False, 'accepted65_source_compile_allowed': False,
          'root_owns_priority_and_fresh_queue_check': True, 'root_publishing_authority_only': True})


def before():
    workspace, control, binding, selection = context()
    project, logs = Path(os.environ['PROJECT']), Path(os.environ['LOGS'])
    from coherent_cache import CacheSession
    session = CacheSession('STORED_PARENT')
    qualification = session.receipt('CACHE_QUALIFICATION.json')
    require(qualification['status'] == 'PASS_AUTHENTIC_STOCK_NO_BUILD_CACHE_INPUT_ONLY', 'Parent stock qualification missing')
    session.verify_restored()
    session.policy_audit()
    rows = source_rows(project, selection, True)
    write(logs / 'STORED_SOURCE_INPUTS_BEFORE.json', {'binding': binding, 'files': rows,
          'qualification_sha256': sha(logs / 'CACHE_QUALIFICATION.json'), 'source_selection_sha256': SELECTION_SHA})
    (logs / 'new-modules.txt').write_text('\n'.join(selection['new_modules']) + '\n')


def bind_sources():
    workspace, control, binding, selection = context()
    project, logs = Path(os.environ['PROJECT']), Path(os.environ['LOGS'])
    prior = read(logs / 'STORED_SOURCE_INPUTS_BEFORE.json')
    require(prior['binding'] == binding and prior['source_selection_sha256'] == SELECTION_SHA,
            'Source preimage receipt belongs to another caller/run')
    rows = source_rows(project, selection, False)
    receipt = read(logs / 'STORED_BATCH_REPAIRS.json')
    require(receipt['source_commit'] == os.environ['SOURCE_COMMIT'] and len(receipt['repairs']) == 8,
            'Wrong original generator receipt')
    by_name = {r['module']: r for r in receipt['repairs']}
    require(set(by_name) == set(selection['new_modules']), 'Wrong generator module set')
    for i, row in enumerate(selection['files']):
        actual = by_name[row['module']]
        require(actual['old_sha256'] == row['pre_input']['sha256'] and actual['new_sha256'] == row['sha256']
                and actual['rows'] == (1817 if i == 7 else 4096) and actual['base'] == (64 + i) * 4096 and actual['data_unchanged'] is True,
                'Generator postimage does not match unchanged reviewed selection')
    modules = (logs / 'modules.txt').read_text().splitlines()
    require(modules == selection['new_modules'], 'Wrong exact new8-only replay/audit universe')
    audit = project / 'StoredBatchAudit.lean'
    require(audit.is_file(), 'Original declaration audit not generated')
    write(logs / 'STORED_SOURCE_BINDING.json', {'binding': binding, 'files': rows,
          'source_selection_sha256': SELECTION_SHA, 'preimage_receipt_sha256': sha(logs / 'STORED_SOURCE_INPUTS_BEFORE.json'),
          'generator_receipt_sha256': sha(logs / 'STORED_BATCH_REPAIRS.json'),
          'audit': {'path': str(audit), 'bytes': audit.stat().st_size, 'sha256': sha(audit)},
          'rows': 30489, 'range': [262144, 292633], 'private_components': 477, 'Fin64_private_components': 476, 'Fin25_private_components': 1,
          'kernel_accepted_here': False})


def final():
    workspace, control, binding, selection = context()
    project, logs = Path(os.environ['PROJECT']), Path(os.environ['LOGS'])
    from coherent_cache import CacheSession
    CacheSession('STORED_PARENT').validate_final()
    rows = source_rows(project, selection, False)
    bound = read(logs / 'STORED_SOURCE_BINDING.json')
    require(bound['binding'] == binding and bound['files'] == rows, 'Bound new8 source changed')
    checked(project / 'StoredBatchAudit.lean', bound['audit'])
    acceptance = read(logs / 'BATCH_ACCEPTANCE.json')
    require(acceptance['status'] == 'PASS_SELECTED_BLOCKS_ONLY'
            and acceptance['modules'] == selection['new_modules']
            and acceptance['source_commit'] == os.environ['SOURCE_COMMIT']
            and acceptance['whole_t01_accepted'] is False, 'Original full batch acceptance gate missing')
    require((logs / 'runtime-audit.log').is_file(), 'Original actual runtime audit log missing')
    state_path = logs / 'runtime/state.json'
    state = read(state_path)
    runtime = read(logs / 'runtime/audit.json')
    require(runtime['status'] == 'PASS_RUNTIME_GUARD_ONLY' and runtime['probe'] is True
            and runtime['source_commands'] > 0 and runtime['compiler_commands'] >= runtime['source_commands']
            and runtime['state_sha256'] == sha(state_path)
            and runtime['command_log_sha256'] == sha(state['log']), 'Original runtime audit receipt is not current and complete')
    commands = [json.loads(line) for line in Path(state['log']).read_text().splitlines()]
    protected_paths = {(project / (m.replace('.', '/') + '.lean')).resolve()
                       for m in control['source_admission']['protected_modules']}
    new_paths = {(project / row['install_path']).resolve(): row['module'] for row in selection['files']}
    starts = {module: 0 for module in selection['new_modules']}
    for command in commands:
        if command['tool'] == 'lean':
            for argument in command['input_args']:
                if argument.endswith('.lean'):
                    path = Path(argument)
                    if not path.is_absolute():
                        path = Path(command['cwd']) / path
                    path = path.resolve()
                    require(path not in protected_paths, 'Accepted source compiler start was recorded')
                    if path in new_paths:
                        starts[new_paths[path]] += 1
    require(all(count == 1 for count in starts.values()), 'Every new proof module must have exactly one actual guarded compiler start')
    replay = [line.removeprefix('replaying ') for line in (logs / 'batch-checker.log').read_text().splitlines()
              if line.startswith('replaying ')]
    require(len(replay) == 8 and set(replay) == set(selection['new_modules']), 'Kernel replay must target exactly the new eight')
    write(logs / 'STORED_SCOPE_RECEIPT.json', {'binding': binding, 'status': 'PASS_ORIGINAL_SELECTED_BATCH_GATES_ONLY',
          'new_modules': selection['new_modules'], 'new_rows': 30489, 'range': [262144, 292633],
          'restored_previously_accepted_parent': selection['parent']['module'],
          'parent_current_replay': False,
          'accepted65_recompiled_or_replayed': False, 'protected_Lean_source_compiler_starts': 0,
          'new_module_guarded_compiler_starts': starts, 'kernel_replay_modules': replay,
          'complete_serialized_declarations': acceptance['complete_serialized_declarations'],
          'old_proof_credit_increment': 0, 'whole_T01_accepted': False,
          'source_binding_sha256': sha(logs / 'STORED_SOURCE_BINDING.json'),
          'original_acceptance_sha256': sha(logs / 'BATCH_ACCEPTANCE.json'),
          'cache_final_input_audit_sha256': sha(logs / 'CACHE_FINAL_INPUT_AUDIT.json'),
          'runtime_audit_log_sha256': sha(logs / 'runtime-audit.log'),
          'runtime_audit_receipt_sha256': sha(logs / 'runtime/audit.json'),
          'independent_remote_evidence_review_still_required': True})


def retain():
    # This failure-path collector intentionally does not require a successful
    # qualification or acceptance receipt. It cannot create or repair facets.
    require(os.environ.get('GITHUB_ACTIONS') == 'true' and sys.platform == 'linux', 'GitHub Linux only')
    project, logs = Path(os.environ['PROJECT']).resolve(), Path(os.environ['LOGS']).resolve()
    inputs = Path(os.environ['CACHE_INPUTS']).resolve()
    require(not logs.is_relative_to(project) and not logs.is_relative_to(inputs), 'Disjoint evidence roots required')
    logs.mkdir(parents=True, exist_ok=True)
    members, errors = {}, []

    def add(path, archive_name):
        path = Path(path)
        if path.is_file():
            resolved = path.resolve()
            existing = members.get(resolved)
            if existing is None:
                members[resolved] = archive_name

    for base, label in [(project / '.lake/build', 'project/.lake/build'), (inputs, 'authentic-cache-inputs')]:
        if base.is_dir():
            for path in sorted(base.rglob('*')):
                if path.is_file():
                    add(path, label + '/' + path.relative_to(base).as_posix())
    for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'T01_PROVENANCE.json', 'StoredBatchAudit.lean']:
        add(project / name, 'project/' + name)
    names = ['ImbalancedChen.P5SubdivisionStoredParentTypes'] + [f'ImbalancedChen.Data.P5SubdivisionStoredBlock{i:03}' for i in range(64, 72)]
    for name in names:
        relative = name.replace('.', '/') + '.lean'
        add(project / relative, 'project/' + relative)
        if not (project / relative).is_file():
            errors.append({'path': str(project / relative), 'error': 'Selected source absent in partial materialization'})

    candidates = []
    part_receipt = logs / 'CACHE_IMPORT_PARTS.json'
    if part_receipt.is_file():
        try:
            candidates += [r['path'] for r in read(part_receipt)['parts'].values()]
        except Exception as error:
            errors.append({'path': str(part_receipt), 'error': str(error)})
    setup_root = project / '.lake/build/ir'
    if setup_root.is_dir():
        for path in sorted(setup_root.rglob('*.setup.json')):
            try:
                setup = read(path)
                arts = setup['importArts']; items = arts.items() if isinstance(arts, dict) else arts
                candidates += [p for name, arrays in items for group in arrays for p in group]
                candidates += [p if isinstance(p, str) else p['path'] for field in ['dynlibs', 'plugins'] for p in setup[field]]
            except Exception as error:
                errors.append({'path': str(path), 'error': str(error)})
    state_path = logs / 'runtime/state.json'
    state = {}
    if state_path.is_file():
        try:
            state = read(state_path)
        except Exception as error:
            errors.append({'path': str(state_path), 'error': str(error)})
    checkpoint_path = inputs / 'CHECKPOINT.json'
    mappings = []
    if checkpoint_path.is_file():
        try:
            checkpoint = read(checkpoint_path)
            old = checkpoint['runtime_state']
            mappings = [(old['root'], str(project))]
            for field in ['realbin', 'shadow']:
                if state.get(field):
                    before = str(Path(old[field]).parent) if field == 'realbin' else old[field]
                    after = str(Path(state[field]).parent) if field == 'realbin' else state[field]
                    mappings.append((before, after))
            for index, row in enumerate(checkpoint['native_and_toolchain_library_ABI_receipts']):
                try:
                    value = row['original_path']
                    for before, after in mappings:
                        if value == before or value.startswith(before + '/'):
                            value = after + value[len(before):]
                            break
                    path = Path(value).resolve()
                    checked(path, row)
                    add(path, f'verified-ABI/{index:04}/' + path.name)
                except Exception as error:
                    errors.append({'path': row.get('original_path'), 'error': str(error)})
        except Exception as error:
            errors.append({'path': str(checkpoint_path), 'error': str(error)})
    roots = [(project, 'project')]
    if state.get('shadow'):
        roots.append((Path(state['shadow']).resolve(), 'runtime-shadow'))
    if state.get('realbin'):
        roots.append((Path(state['realbin']).resolve().parent, 'runtime-realroot'))
    candidates += list(state.get('runtime_sha256', {}))
    for value in candidates:
        for before, after in mappings:
            if value == before or value.startswith(before + '/'):
                value = after + value[len(before):]
                break
        path = Path(value)
        if not path.is_absolute():
            path = project / path
        resolved = path.resolve()
        if resolved in members:
            continue  # Exact original ABI bytes were already checked and retained above.
        matches = [(base, label) for base, label in roots if resolved.is_relative_to(base)]
        if not matches:
            errors.append({'path': str(path), 'error': 'Unmapped referenced file retained as failure metadata only'})
            continue
        base, label = max(matches, key=lambda item: len(item[0].parts))
        if path.is_file():
            add(path, label + '/' + resolved.relative_to(base).as_posix())
            add(Path(str(path) + '.hash'), label + '/' + resolved.relative_to(base).as_posix() + '.hash')
        else:
            errors.append({'path': str(path), 'error': 'Missing actual referenced file'})
    archive = logs / 'STORED_FULL_RAW_AND_CURRENT_FACETS.tar.gz'
    require(not archive.exists(), 'Refusing retained archive overwrite')
    rows = []
    with tarfile.open(archive, 'w:gz', compresslevel=1) as output:
        for path, name in sorted(members.items(), key=lambda item: item[1]):
            try:
                before = {'bytes': path.stat().st_size, 'sha256': sha(path)}
                output.add(path, arcname=name, recursive=False)
                checked(path, before)
                rows.append({'path': str(path), 'archive_path': name, **before})
            except Exception as error:
                errors.append({'path': str(path), 'error': str(error)})
    write(logs / 'STORED_RETENTION.json', {'status': 'COMPLETE_AVAILABLE_FILES' if not errors else 'FAILURE_AND_PARTIAL_FILES_RETAINED',
          'archive': {'path': str(archive), 'bytes': archive.stat().st_size, 'sha256': sha(archive)},
          'files': rows, 'errors': errors, 'cache_or_proof_acceptance_granted': False})
    require(not errors, 'Retained available/partial bytes and original missing-input evidence; see STORED_RETENTION.json')


def main():
    actions = {'preflight': preflight, 'before': before, 'bind-sources': bind_sources, 'final': final, 'retain': retain}
    require(len(sys.argv) == 2 and sys.argv[1] in actions, 'Expected preflight/before/bind-sources/final/retain')
    actions[sys.argv[1]]()


if __name__ == '__main__':
    main()

