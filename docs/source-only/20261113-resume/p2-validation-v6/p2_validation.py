"""CI-only input binding and evidence retention around the existing P0 stage/collector.

Preparation artifact only: do not run this materializer, or its reused collector,
locally. No proof program is implemented here. The existing stage_p4.py and
runtime guard are used byte for byte; the collector's proof gates are retained.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open('rb') as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b''):
            result.update(chunk)
    return result.hexdigest()


def checked(path: Path, record: dict) -> bytes:
    data = path.read_bytes()
    assert len(data) == record['bytes'], str(path)
    assert hashlib.sha256(data).hexdigest() == record['sha256'], str(path)
    if 'git_blob' in record:
        assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == record['git_blob'], str(path)
    return data


def git_output(argv, **kwargs):
    assert argv[0] == 'git'
    return subprocess.check_output(['git', '-c', 'protocol.allow=never', *argv[1:]],
                                   env=dict(os.environ, GIT_NO_LAZY_FETCH='1'), **kwargs)


def committed_driver_selection() -> tuple[dict, dict]:
    workspace = Path(os.environ['GITHUB_WORKSPACE'])
    commit = os.environ['GITHUB_SHA']
    assert re.fullmatch(r'[0-9a-f]{40}', commit)
    assert git_head(workspace) == commit
    assert os.environ['GITHUB_EVENT_NAME'] == 'push', 'Only the root-selected narrow push route is prepared'
    branch = 'ci/p2-integer-mass-r20-20261115'
    assert os.environ['GITHUB_REF'] == 'refs/heads/' + branch
    path = 'verification/parts/p0/P2_INTEGER_MASS_DRIVER_SELECTION.json'
    committed = git_output(['git', '-C', str(workspace), 'show', commit + ':' + path])
    assert (workspace / path).read_bytes() == committed, 'Root selection differs from driver commit'
    selection = json.loads(committed)
    assert selection['schema'] == 'p2-integer-mass-root-driver-selection-v2'
    assert re.fullmatch(r'[0-9a-f]{64}', selection['bundle_registry_sha256'])
    assert re.fullmatch(r'[0-9a-f]{64}', selection['manifest_sha256'])
    assert selection['driver_base'] == 'ada8518c9e06e85d71abcb56ced05f475f68c8db'
    assert selection['driver_branch'] == branch
    assert selection['workflow_path'] == '.github/workflows/p2-integer-mass-validation.yml'
    assert selection['bundle_path'] == 'docs/source-only/20261113-resume/p2-validation-v6'
    assert HERE.resolve() == (workspace / selection['bundle_path']).resolve()
    # A first branch push may have event.before = 0. The real immutable
    # parent is in the commit header and needs no parent-history fetch.
    raw_commit = git_output(['git', '-C', str(workspace), 'cat-file', 'commit', commit])
    headers = raw_commit.split(b'\n\n', 1)[0].decode().splitlines()
    parents = [line.removeprefix('parent ') for line in headers if line.startswith('parent ')]
    assert parents == [selection['driver_base']], 'Prepared one-commit driver must directly extend the reviewed base'
    return selection, {'driver_commit': commit, 'actual_commit_parents': parents,
                       'event_name': os.environ['GITHUB_EVENT_NAME'], 'ref': os.environ['GITHUB_REF'],
                       'selection_path': path, 'selection_sha256': hashlib.sha256(committed).hexdigest(),
                       'selection_git_blob': hashlib.sha1(b'blob ' + str(len(committed)).encode() + b'\0' + committed).hexdigest()}


def load_bound_bundle() -> tuple[dict, dict]:
    selection, binding = committed_driver_selection()
    registry_path = HERE / 'REGISTRY.json'
    assert digest(registry_path) == selection['bundle_registry_sha256']
    registry = json.loads(registry_path.read_text())
    for record in registry['files']:
        path = HERE / record['path']
        assert path.resolve().is_relative_to(HERE.resolve())
        checked(path, record)
    manifest_path = HERE / 'P2_VALIDATION_MANIFEST.json'
    assert digest(manifest_path) == os.environ['EXPECTED_MANIFEST']
    manifest = json.loads(manifest_path.read_text())
    assert not manifest['missing']
    assert manifest['primary_target'] == 'ImbalancedChen.Certificates.P2HistoricalThirdIntegerMass'
    assert manifest['required_audit_targets'] == ['ImbalancedChen.FinitePiIntegral']
    assert manifest['targets'] == [manifest['primary_target'], *manifest['required_audit_targets']]
    assert manifest['source_commit'] == os.environ['SOURCE_COMMIT']
    assert manifest['repaired_baseline'] == os.environ['BASELINE_COMMIT']
    assert selection['source_commit'] == manifest['source_commit']
    assert selection['repaired_baseline'] == manifest['repaired_baseline']
    assert selection['compile_cache'] == manifest['compile_cache'], 'Root must explicitly adopt the exact independent cache route'
    assert selection['manifest_sha256'] == digest(manifest_path)
    workspace = Path(os.environ['GITHUB_WORKSPACE'])
    audit = json.loads((HERE / 'DRIVER_BASE_WORKFLOW_AUDIT.json').read_text())
    assert audit['driver_base'] == selection['driver_base']
    expected = {record['path']: record['expected_driver'] for record in audit['original_workflows']}
    workflow_record = next(r for r in registry['files'] if r['path'] == 'p2-integer-mass-validation.yml')
    expected[selection['workflow_path']] = workflow_record
    actual = {p.relative_to(workspace).as_posix()
              for pattern in ['*.yml', '*.yaml'] for p in (workspace / '.github/workflows').glob(pattern)}
    assert actual == set(expected), 'Unexpected/missing workflow in the selected driver'
    workflow_bindings = []
    for path, record in sorted(expected.items()):
        data = checked(workspace / path, record)
        assert data == git_output(['git', '-C', str(workspace), 'show', os.environ['GITHUB_SHA'] + ':' + path])
        workflow_bindings.append({'path': path, 'sha256': record['sha256'],
                                  'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()})
    binding.update(bundle_registry_sha256=digest(registry_path),
                   manifest_sha256=digest(manifest_path), workflow_bindings=workflow_bindings,
                   root_selection_outside_bundle_hash=True)
    return manifest, binding


def git_head(path: Path) -> str:
    return git_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()


def bind_installed(manifest: dict, project: Path) -> dict:
    records = []
    for record in manifest['modules']:
        path = project / record['install_path']
        checked(path, record)
        records.append({'module': record['module'], 'path': record['install_path'],
                        'sha256': record['sha256'], 'git_blob': record['git_blob']})
    for record in manifest['configuration']:
        checked(project / record['path'], record)
    return {'modules': records, 'audit_sha256': digest(project / 'CandidateAudit.lean'),
            'manifest_sha256': digest(HERE / 'P2_VALIDATION_MANIFEST.json'),
            'bundle_registry_sha256': digest(HERE / 'REGISTRY.json'),
            'committed_driver_binding_sha256': digest(Path(os.environ['LOGS']) / 'DRIVER_BINDING.json')}


def stage(manifest: dict, project: Path, logs: Path) -> None:
    origins = {'baseline': Path(os.environ['BASELINE_SOURCE']),
               'abi': Path(os.environ['ABI_SOURCE']),
               'repair': Path(os.environ['REPAIR_SOURCE']),
               'repair_next': Path(os.environ['REPAIR_NEXT_SOURCE']),
               'repair_r9': Path(os.environ['REPAIR_R9_SOURCE'])}
    assert manifest['source_revisions']=={'baseline':manifest['repaired_baseline'],'abi':manifest['inherited_source_commit'],'repair':manifest['previous_source_commit'],'repair_next':manifest['prior_source_commit'],'repair_r9':manifest['source_commit']}
    for label,path in origins.items():
        assert git_head(path)==manifest['source_revisions'][label]
    for path in origins.values():
        assert not git_output(['git', '-C', str(path), 'diff', 'HEAD', '--'])
    view = Path(os.environ['P2_SOURCE_VIEW'])
    assert not view.exists() and not project.exists(), 'Require fresh isolated roots'
    view.mkdir(parents=True)
    logs.mkdir(parents=True, exist_ok=True)
    for record in manifest['modules']:
        expected_ref = manifest['source_revisions'][record['origin']]
        assert record['source_commit'] == expected_ref
        source = origins[record['origin']] / record['origin_path']
        data = checked(source, record)
        dest = view / record['source']
        assert dest.resolve().is_relative_to(view.resolve())
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
    for record in manifest['configuration']:
        (view / record['path']).write_bytes(checked(origins['baseline'] / record['path'], record))
    # Original generic exact-byte stage, including its original three pin checks.
    subprocess.run([sys.executable, str(HERE / 'reused/stage_p4.py'),
                    '--source', str(view), '--manifest', str(HERE / 'P2_VALIDATION_MANIFEST.json'),
                    '--dest', str(project)], check=True)
    receipt = {'source_commit': manifest['source_commit'],
               'repaired_baseline': manifest['repaired_baseline'],
               'overlay': manifest['overlay'], 'modules': manifest['modules'],
               'configuration': manifest['configuration'], 'compiled': False,
               'kernel_verified': False, 'new_isolated_destination': True,
               'legacy_stage_receipt_name': 'P4_STAGE_RECEIPT.json'}
    (logs / 'P2_STAGE_RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    for label, path in origins.items():
        (logs / (label + '-source-tree.txt')).write_bytes(git_output(
            ['git', '-C', str(path), 'ls-tree', '-r', 'HEAD']))
    sys.path.insert(0,str(Path(os.environ['GITHUB_WORKSPACE'])/manifest['compile_cache']['tools_bundle']['path']))
    from cache_project import load_inputs
    project_selection,_=load_inputs()
    (logs/'recompile-modules.txt').write_text('\n'.join(project_selection['compile_modules'])+'\n')
    (logs / 'VALIDATION_MANIFEST.json').write_bytes((HERE / 'P2_VALIDATION_MANIFEST.json').read_bytes())
    (logs / 'VALIDATION_BUNDLE_REGISTRY.json').write_bytes((HERE / 'REGISTRY.json').read_bytes())


def retain(manifest: dict, project: Path, logs: Path) -> None:
    before_path = logs / 'BATCH_OBJECTS_BEFORE.json'
    before = json.loads(before_path.read_text()) if before_path.exists() else {}
    paths = set(before)
    current_snapshot_paths = {
        str(p.relative_to(project))
        for pattern in ['ImbalancedChen/**/*.lean', '.lake/build/lib/lean/**/*.olean*',
                        '.lake/packages/*/.lake/build/lib/lean/**/*.olean*']
        for p in project.glob(pattern) if p.is_file()}
    paths.update(current_snapshot_paths)
    for record in manifest['modules']:
        module_path = Path(record['install_path']).with_suffix('')
        directory = project / '.lake/build/lib/lean' / module_path.parent
        paths.update(str(p.relative_to(project)) for p in directory.glob(module_path.name + '.*') if p.is_file())
        paths.add(record['install_path'])
    paths.update(['lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                  'CandidateAudit.lean', 'FinitePiPilot.lean', 'P4_STAGE_RECEIPT.json'])
    inventory, absent, changed = [], [], []
    archive_path = logs / 'compiled-objects-and-sources.tar.gz'
    # Stream all snapshot objects, including package .olean* objects, plus
    # owned .ilean/.trace files and exact final sources. No shadow sysroot.
    with tarfile.open(archive_path, 'w:gz', dereference=True) as archive:
        for relative in sorted(paths):
            path = project / relative
            assert path.resolve().is_relative_to(project.resolve()), relative
            if not path.is_file():
                absent.append(relative)
                continue
            actual = digest(path)
            if relative in before and actual != before[relative]:
                changed.append(relative)
            inventory.append({'path': relative, 'sha256': actual, 'bytes': path.stat().st_size})
            archive.add(path, arcname='project/' + relative, recursive=False)
    (logs / 'RETAINED_OBJECTS.json').write_text(json.dumps({
        'archive': archive_path.name, 'archive_sha256': digest(archive_path),
        'files': inventory, 'absent': absent, 'snapshot_present': before_path.exists(),
        'changed_since_snapshot': changed,
        'snapshot_path_additions': sorted(current_snapshot_paths - set(before)),
        'snapshot_path_removals': sorted(set(before) - current_snapshot_paths),
        'acceptance_claim': False}, indent=2) + '\n')


def finalize(manifest: dict, project: Path, logs: Path) -> None:
    from finitepi_pilot import validate_receipt
    validate_receipt(manifest, project, logs)
    cache_tools = Path(os.environ['GITHUB_WORKSPACE']) / manifest['compile_cache']['tools_bundle']['path']
    sys.path.insert(0, str(cache_tools))
    from coherent_cache import CacheSession
    cache_session = CacheSession('P2_NATIVE_398')
    cache_session.validate_final()
    from cache_project import load_inputs as project_inputs
    project_selection,_=project_inputs()
    expected_compile=project_selection['compile_modules']
    selected={r['module']:r for r in manifest['modules']}
    expected_sources={str(project/selected[n]['install_path']):n for n in expected_compile}
    events=[json.loads(line) for line in (logs/'CACHE_PREEXEC_EVENTS.jsonl').read_text().splitlines() if line.strip()]
    compiled=[e for e in events if e['classification']=='EXACT_CURRENT_CALLER_SOURCE']
    assert len(expected_compile)==len(compiled)==17
    assert all(e['tool']=='lean' and e['compiler_exec_permitted'] is True and e['context']==cache_session.binding
               and len(e['physical_inputs'])==1 for e in compiled)
    observed=[e['physical_inputs'][0]['path'] for e in compiled]
    assert len(set(observed))==17 and set(observed)==set(expected_sources), 'Only17 unique affected source compilations required'
    for event in compiled:
        physical=event['physical_inputs'][0];record=selected[expected_sources[physical['path']]]
        assert physical=={'path':str(project/record['install_path']),'bytes':record['bytes'],'sha256':record['sha256']}
    compile_census={'binding':cache_session.binding,'status':'PASS_EXACTLY17_NEW_AND_ZERO_PROTECTED_SOURCE_COMPILES',
        'expected_modules':expected_compile,'events':compiled,'source_compile_count':17,'protected_root85_compile_count':0,
        'bootstrap11_or_native407_compile_count':0,'preexec_events_sha256':digest(logs/'CACHE_PREEXEC_EVENTS.jsonl'),
        'command_log_sha256':digest(logs/'runtime/compiler-commands.jsonl')}
    census_path=logs/'P2_COMPILE_CENSUS.json';assert not census_path.exists()
    census_path.write_text(json.dumps(compile_census,indent=2)+'\n')
    checkpoint = json.loads((logs / 'CACHE_CHECKPOINT_RETENTION.json').read_text())
    assert checkpoint['exit_code'] == 0 and checkpoint['collector_sha256'] == '773e4eab588c0d196c5b7ad86a3a0f90a6a0fe1c225baa7559b2b1380e853a76'
    assert checkpoint['binding'] == cache_session.binding
    checkpoint_path = Path(checkpoint['output']).resolve()
    expected_checkpoint = (Path(os.environ['RUNNER_TEMP']) / 'p2-coherent-checkpoint').resolve()
    assert checkpoint_path == Path(os.environ['CACHE_CHECKPOINT_OUTPUT']).resolve() == expected_checkpoint
    assert not checkpoint_path.is_relative_to(project.resolve()) and not checkpoint_path.is_relative_to(logs.resolve())
    adapted_path = logs / 'CHECKPOINT_COLLECTOR_INPUT.json'
    assert checkpoint['adapter_sha256'] == digest(cache_tools / 'cache_checkpoint_retain.py')
    assert checkpoint['input_sha256'] == digest(adapted_path)
    assert checkpoint['stdout_sha256'] == digest(logs / 'checkpoint-collection.log')
    assert checkpoint['argv'] == [sys.executable, str(cache_tools / 'reference/checkpoint_objects_v3.py'),
        '--project', str(project.resolve()), '--manifest', str(adapted_path.resolve()),
        '--logs', str(logs.resolve()), '--output', str(expected_checkpoint)]
    assert (checkpoint_path / 'CHECKPOINT.json').is_file()
    adapted = json.loads(adapted_path.read_text())
    assert adapted['files'] == manifest['modules'] and adapted['data_inputs'] == []
    assert adapted['targets'] == [{'closure_modules': [r['module'] for r in manifest['modules']],
        'source_identity_sha256': hashlib.sha256(json.dumps(manifest['modules'], sort_keys=True).encode()).hexdigest()}]
    actual_checkpoint = json.loads((checkpoint_path / 'CHECKPOINT.json').read_text())
    assert actual_checkpoint['schema'] == 't01-coherent-build-checkpoint-v3'
    assert actual_checkpoint['source_commit'] == manifest['source_commit']
    assert str(actual_checkpoint['run_id']) == os.environ['GITHUB_RUN_ID']
    assert str(actual_checkpoint['run_attempt']) == os.environ['GITHUB_RUN_ATTEMPT']
    assert actual_checkpoint['runtime_state'] == json.loads((logs / 'runtime/state.json').read_text())
    assert actual_checkpoint['manifest_sha256'] == digest(adapted_path)
    assert actual_checkpoint['source_identity_sha256'] == adapted['targets'][0]['source_identity_sha256']
    assert actual_checkpoint['runtime_audit_valid'] is True and actual_checkpoint['all_dependency_source_pins_valid'] is True
    summary = json.loads((logs / 'CHECKPOINT_SUMMARY.json').read_text())
    assert summary['checkpoint_sha256'] == digest(checkpoint_path / 'CHECKPOINT.json')
    assert summary['module_count'] == len(manifest['modules']) + 1
    installed = bind_installed(manifest, project)
    assert installed == json.loads((logs / 'SOURCE_OBJECT_BINDINGS.json').read_text())
    batch = json.loads((logs / 'BATCH_ACCEPTANCE.json').read_text())
    assert batch['status'] == 'PASS_EXACT_CANDIDATE_CLOSURE_ONLY'
    assert batch['modules'] == [r['module'] for r in manifest['modules']]
    assert batch['proof_artifact_hash'] == digest(logs / 'BATCH_OBJECTS_BEFORE.json')
    runtime = json.loads((logs / 'runtime/audit.json').read_text())
    assert runtime['status'] == 'PASS_RUNTIME_GUARD_ONLY' and runtime['probe']
    assert runtime['source_commands'] > 0
    state_path = logs / 'runtime/state.json'
    assert digest(state_path) == runtime['state_sha256'], 'Runtime audit does not bind the retained state'
    state = json.loads(state_path.read_text())
    command_path = logs / 'runtime/compiler-commands.jsonl'
    assert Path(state['log']).resolve() == command_path.resolve()
    assert digest(command_path) == runtime['command_log_sha256'], 'Runtime audit does not bind the retained commands'
    assert state['guard_sha256'] == manifest['runtime_reuse']['sha256']
    retained = json.loads((logs / 'RETAINED_OBJECTS.json').read_text())
    assert retained['snapshot_present'] and not retained['absent']
    assert not retained['changed_since_snapshot']
    assert not retained['snapshot_path_additions'] and not retained['snapshot_path_removals']
    assert digest(logs / retained['archive']) == retained['archive_sha256']
    kept = {r['path'] for r in retained['files']}
    for record in manifest['modules']:
        expected = '.lake/build/lib/lean/' + record['module'].replace('.', '/') + '.olean'
        assert expected in kept, 'Missing final compiled owned module: ' + expected
    receipt = {'status': 'PASS_EXACT_P2_INTEGER_MASS_ABI_CLOSURE_ONLY',
               'source_commit': manifest['source_commit'],
               'repaired_baseline': manifest['repaired_baseline'],
               'target': manifest['primary_target'], 'modules': batch['modules'],
               'mandatory_inventory_targets': manifest['required_audit_targets'],
               'acceptance_groups': manifest['acceptance_groups'],
               'old_p4_inventory_failure_resolved': False,
               'serialized_declarations': batch['complete_serialized_declarations'],
               'manifest_sha256': installed['manifest_sha256'],
               'bundle_registry_sha256': installed['bundle_registry_sha256'],
               'generated_audit_sha256': installed['audit_sha256'],
               'compiled_archive_sha256': retained['archive_sha256'],
               'finitepi_pilot_acceptance_sha256': digest(logs / 'FINITEPI_PILOT_ACCEPTANCE.json'),
               'cache_final_input_audit_sha256': digest(logs / 'CACHE_FINAL_INPUT_AUDIT.json'),
               'cache_qualification_sha256': digest(logs / 'CACHE_QUALIFICATION.json'),
               'cache_bootstrap_qualification_sha256': digest(logs / 'CACHE_BOOTSTRAP_QUALIFICATION.json'),
               'cache_bootstrap_restore_sha256': digest(logs / 'CACHE_BOOTSTRAP_RESTORE.json'),
               'cache_project_producer_receipts': {k:v for k,v in json.loads((logs/'CACHE_FINAL_INPUT_AUDIT.json').read_text()).items() if k.startswith('project_')},
               'compile_census_sha256': digest(logs / 'P2_COMPILE_CENSUS.json'),
               'coherent_checkpoint_sha256': digest(checkpoint_path / 'CHECKPOINT.json'),
               'cache_tools_registry_sha256': manifest['compile_cache']['tools_bundle']['registry_sha256'],
               'runtime_audit_sha256': digest(logs / 'runtime/audit.json'),
               'runtime_state_sha256': digest(state_path),
               'runtime_command_log_sha256': digest(command_path),
               'committed_driver_binding_sha256': installed['committed_driver_binding_sha256'],
               'driver_commit': os.environ['GITHUB_SHA'],
               'run_id': os.environ['GITHUB_RUN_ID'],
               'run_attempt': os.environ['GITHUB_RUN_ATTEMPT'],
               'whole_p2_accepted': False, 'whole_p4_accepted': False,
               'numerical_or_guard_execution_accepted': False}
    (logs / 'FINAL_ACCEPTANCE.json').write_text(json.dumps(receipt, indent=2) + '\n')


def main() -> None:
    assert os.environ.get('GITHUB_ACTIONS') == 'true', 'Root-authorized CI only; never execute locally'
    mode = sys.argv[1]
    manifest, binding = load_bound_bundle()
    logs = Path(os.environ['LOGS'])
    if mode == 'select':
        logs.mkdir(parents=True, exist_ok=True)
        (logs / 'DRIVER_BINDING.json').write_text(json.dumps(binding, indent=2) + '\n')
        return
    assert json.loads((logs / 'DRIVER_BINDING.json').read_text()) == binding
    project = Path(os.environ['PROJECT'])
    if mode == 'stage':
        stage(manifest, project, logs)
    elif mode == 'bind':
        (logs / 'SOURCE_OBJECT_BINDINGS.json').write_text(json.dumps(bind_installed(manifest, project), indent=2) + '\n')
    elif mode == 'retain':
        retain(manifest, project, logs)
    elif mode == 'finalize':
        finalize(manifest, project, logs)
    else:
        raise SystemExit('Unknown mode')


if __name__ == '__main__':
    main()
