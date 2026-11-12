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


def committed_driver_selection() -> tuple[dict, dict]:
    workspace = Path(os.environ['GITHUB_WORKSPACE'])
    commit = os.environ['GITHUB_SHA']
    assert re.fullmatch(r'[0-9a-f]{40}', commit)
    assert git_head(workspace) == commit
    assert os.environ['GITHUB_EVENT_NAME'] == 'push', 'Only the root-selected narrow push route is prepared'
    branch = 'ci/p2-integer-mass-20261112'
    assert os.environ['GITHUB_REF'] == 'refs/heads/' + branch
    path = 'verification/parts/p0/P2_INTEGER_MASS_DRIVER_SELECTION.json'
    committed = subprocess.check_output(['git', '-C', str(workspace), 'show', commit + ':' + path])
    assert (workspace / path).read_bytes() == committed, 'Root selection differs from driver commit'
    selection = json.loads(committed)
    assert selection['schema'] == 'p2-integer-mass-root-driver-selection-v2'
    assert re.fullmatch(r'[0-9a-f]{64}', selection['bundle_registry_sha256'])
    assert re.fullmatch(r'[0-9a-f]{64}', selection['manifest_sha256'])
    assert selection['driver_base'] == '356c3782e9428098a2fcbfb18c689bef264d84fa'
    assert selection['driver_branch'] == branch
    assert selection['workflow_path'] == '.github/workflows/p2-integer-mass-validation.yml'
    assert selection['bundle_path'] == 'docs/source-only/20261112-resume/p2-validation-v2'
    assert HERE.resolve() == (workspace / selection['bundle_path']).resolve()
    # A first branch push may have event.before = 0. The real immutable
    # parent is in the commit header and needs no parent-history fetch.
    raw_commit = subprocess.check_output(['git', '-C', str(workspace), 'cat-file', 'commit', commit])
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
        assert data == subprocess.check_output(['git', '-C', str(workspace), 'show', os.environ['GITHUB_SHA'] + ':' + path])
        workflow_bindings.append({'path': path, 'sha256': record['sha256'],
                                  'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()})
    binding.update(bundle_registry_sha256=digest(registry_path),
                   manifest_sha256=digest(manifest_path), workflow_bindings=workflow_bindings,
                   root_selection_outside_bundle_hash=True)
    return manifest, binding


def git_head(path: Path) -> str:
    return subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()


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
               'abi': Path(os.environ['ABI_SOURCE'])}
    assert git_head(origins['baseline']) == manifest['repaired_baseline']
    assert git_head(origins['abi']) == manifest['source_commit']
    for path in origins.values():
        assert not subprocess.check_output(['git', '-C', str(path), 'diff', 'HEAD', '--'])
    view = Path(os.environ['P2_SOURCE_VIEW'])
    assert not view.exists() and not project.exists(), 'Require fresh isolated roots'
    view.mkdir(parents=True)
    logs.mkdir(parents=True, exist_ok=True)
    for record in manifest['modules']:
        expected_ref = manifest['repaired_baseline'] if record['origin'] == 'baseline' else manifest['source_commit']
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
        (logs / (label + '-source-tree.txt')).write_bytes(subprocess.check_output(
            ['git', '-C', str(path), 'ls-tree', '-r', 'HEAD']))
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
                  'CandidateAudit.lean', 'P4_STAGE_RECEIPT.json'])
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
