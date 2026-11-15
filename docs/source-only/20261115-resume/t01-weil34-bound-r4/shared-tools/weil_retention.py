"""Original runtime/collector plus complete immutable final proof evidence chain.

Direct outputs retain the original collector's no-Lake-trace quarantine.
Only the independently bound exact34 proof processes can earn StageA credit.
"""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

from coherent_cache import BASELINE_GUARD, HERE, checked, read, require, sha, write
from weil_cache import WeilSession, physical, process_receipt
from weil_scope import BUNDLE, bind, data, installed, roots
from weil_proof import check_outputs, validated_inventory

COLLECTOR = '773e4eab588c0d196c5b7ad86a3a0f90a6a0fe1c225baa7559b2b1380e853a76'


def source_rows():
    return [dict(module=r['module'], install_path=r['installation_path'], bytes=r['bytes'], sha256=r['sha256'], imports=r['imports'])
            for r in data()['source_rows']]


def collector_manifest(project):
    rows = source_rows()
    audit = BUNDLE/'WeilAudit.lean'
    return dict(files=rows, data_inputs=[], audit_source=dict(bytes=audit.stat().st_size, sha256=sha(audit)),
        targets=[dict(closure_modules=[r['module'] for r in rows],
            source_identity_sha256=hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest())])


def runtime():
    session = WeilSession()
    require(sha(HERE/'reused/ci_runtime_guard.py') == BASELINE_GUARD, 'Original runtime auditor changed')
    argv = [sys.executable, str(HERE/'reused/ci_runtime_guard.py'), 'audit', '--probe', '--require-source']
    result = session.run('runtime-audit', argv)
    session.emit('WEIL_RUNTIME_PROCESS.json', dict(process=result))


def retain():
    _, binding = bind(); project, logs = roots()
    failures, capture, captured = [], [], set()
    archive = logs/'weil-source-object-inputs.tar.gz'
    require(not archive.exists(), 'Raw retention already recorded')
    # No JSON is parsed before the available vendor bytes and raw receipt files
    # are captured. Each bad receipt becomes an accumulated failure afterwards.
    initial = {project/r['installation_path'] for r in data()['source_rows']}
    initial.update(project/n for n in ['T01Audit.lean', 'T01_PROVENANCE.json', 'LEANPOOL_LICENSE',
                                      'lakefile.toml', 'lean-toolchain', 'lake-manifest.json'])
    initial.update(p for p in (project/'.lake/build').rglob('*') if p.is_file())
    initial.update(p for p in logs.rglob('*') if p.is_file())
    prior_inputs = Path(os.environ['WEIL_DIRECT_INPUTS']).resolve()
    require(not prior_inputs.is_relative_to(project) and not prior_inputs.is_relative_to(logs),'Disjoint actual prior originals required')
    initial.update(p for p in prior_inputs.rglob('*') if p.is_file())
    official = Path.home()/'.elan/toolchains/leanprover--lean4---v4.33.0-rc1'
    allowed = [project, logs, official, Path(os.environ['RUNNER_TEMP']).resolve()/'p0-ci-shadow-toolchain',prior_inputs]
    with tarfile.open(archive, 'w:gz') as tar:
        def save(path, expected=None):
            path = Path(path)
            try:
                require(any(path.resolve().is_relative_to(root.resolve()) for root in allowed), 'Raw input escaped selected roots')
                require(path.is_file() and not path.is_symlink(), 'Missing/nonregular raw evidence')
                if str(path) not in captured:
                    arcname = 'physical/'+hashlib.sha256(str(path).encode()).hexdigest()+'/'+path.name
                    info = tarfile.TarInfo(arcname); info.size = path.stat().st_size
                    class DigestReader:
                        def __init__(self, stream):
                            self.stream = stream; self.digest = hashlib.sha256(); self.count = 0
                        def read(self, size=-1):
                            content = self.stream.read(size); self.digest.update(content); self.count += len(content)
                            return content
                    with path.open('rb') as stream:
                        reader = DigestReader(stream); tar.addfile(info, reader)
                    require(reader.count == info.size, 'Incomplete raw file copy')
                    record = dict(path=str(path), bytes=reader.count, sha256=reader.digest.hexdigest())
                    capture.append(dict(record, archive_member=arcname)); captured.add(str(path))
                if expected is not None: checked(path, expected)
            except Exception as error:
                failures.append(dict(path=str(path), error=str(error)))
        for path in sorted(initial):
            if path.is_file(): save(path)
        for path in sorted((logs/'direct-inputs').glob('*.json')):
            try:
                value = read(path)
                require(value['binding'] == binding, 'Wrong direct-input receipt run')
                for row in value['files']: save(row['path'], row)
                save(value['source']['path'], value['source'])
            except Exception as error:
                failures.append(dict(phase='direct-input-parse', path=str(path), error=str(error)))
        standard_path = logs/'WEIL_STANDARD_INPUTS.json'
        if standard_path.is_file():
            try:
                standard = read(standard_path)
                require(standard['binding'] == binding, 'Wrong standard receipt run')
                for row in standard['physical_files'].values(): save(row['path'], row)
                for row in standard['source_private_closure'].values():
                    identity = row['identity']
                    for part in [identity['source'], *identity['facets']]: save(part['path'], part)
            except Exception as error:
                failures.append(dict(phase='standard-input-parse', path=str(standard_path), error=str(error)))
    write(logs/'WEIL_RAW_CAPTURE.json', dict(binding=binding, files=capture, archive=archive.name,
        archive_sha256=sha(archive), integrity_errors=failures.copy(), proof_acceptance=False))
    rows = source_rows(); config = logs/'CHECKPOINT_COLLECTOR_INPUT.json'
    write(config, collector_manifest(project))
    collector = HERE/'reference/checkpoint_objects_v3.py'
    require(collector.stat().st_size == 32993 and sha(collector) == COLLECTOR, 'Original collector bytes changed')
    output = Path(os.environ['CACHE_CHECKPOINT_OUTPUT']).resolve()
    require(not output.exists() and not output.is_relative_to(project) and not output.is_relative_to(logs), 'Fresh disjoint checkpoint output required')
    argv = [sys.executable, str(collector), '--project', str(project), '--manifest', str(config), '--logs', str(logs), '--output', str(output)]
    provenance_path = project/'T01_PROVENANCE.json'
    before_provenance = sha(provenance_path) if provenance_path.is_file() else None
    temporary = output.parent/(output.name+'.collector-stdout.log')
    require(not temporary.exists(), 'Original collector already invoked')
    with temporary.open('wb') as stream:
        result = subprocess.run(argv, cwd=project, stdout=stream, stderr=subprocess.STDOUT)
    shutil.copyfile(temporary, logs/'checkpoint-collection.log')
    if before_provenance is None or not provenance_path.is_file() or sha(provenance_path) != before_provenance:
        failures.append(dict(error='Actual original source provenance missing/changed'))
    checkpoint = output/'CHECKPOINT.json'; summary = logs/'CHECKPOINT_SUMMARY.json'
    checkpoint_summary = None
    if checkpoint.is_file():
        try:
            raw = read(checkpoint)
            checkpoint_summary = {k:raw[k] for k in ['source_commit', 'run_id', 'run_attempt', 'manifest_sha256',
                                                     'runtime_audit_valid', 'all_dependency_source_pins_valid']}
        except Exception as error: failures.append(dict(phase='checkpoint-parse', error=str(error)))
    actual_summary = None
    if summary.is_file():
        try: actual_summary = read(summary)
        except Exception as error: failures.append(dict(phase='collector-summary-parse', error=str(error)))
    state = logs/'runtime/state.json'; command = None
    if state.is_file():
        try:
            command_path = Path(read(state)['log'])
            if command_path.is_file(): command = dict(path=str(command_path), sha256=sha(command_path))
        except Exception as error: failures.append(dict(phase='runtime-state-parse', error=str(error)))
    write(logs/'WEIL_RETENTION.json', dict(binding=binding, argv=argv, cwd=str(project), exit_code=result.returncode,
        collector_sha256=sha(collector), collector_bytes=collector.stat().st_size,
        collector_manifest_sha256=sha(config), source_manifest_sha256=sha(BUNDLE/'STAGE_A34.json'),
        root_source_count=len(rows), root_source_rows_sha256=hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest(),
        stdout_sha256=sha(logs/'checkpoint-collection.log'), output=str(output),
        checkpoint_sha256=sha(checkpoint) if checkpoint.is_file() else None, checkpoint_summary=checkpoint_summary,
        actual_collector_summary=actual_summary, actual_collector_summary_sha256=sha(summary) if summary.is_file() else None,
        runtime_state_sha256=sha(state) if state.is_file() else None, current_command_log=command,
        raw_capture_sha256=sha(logs/'WEIL_RAW_CAPTURE.json'), provenance_sha256=before_provenance,
        direct_outputs_have_no_synthetic_Lake_trace=True, collector_restore_classification_preserved=True,
        integrity_errors=failures, proof_acceptance=False))
    require(result.returncode == 0 and not failures, 'Original complete raw collection failed; all available evidence remains quarantined')


def validate_capture(session, capture, inventory):
    require(capture['archive'] == 'weil-source-object-inputs.tar.gz' and not capture['integrity_errors']
            and capture['archive_sha256'] == sha(session.logs/capture['archive']), 'Raw source/object archive changed')
    expected = {r['archive_member']:r for r in capture['files']}
    require(len(expected) == len(capture['files']), 'Duplicate retained archive member')
    with tarfile.open(session.logs/capture['archive'], 'r:gz') as tar:
        members = tar.getmembers()
        require(len(members) == len(expected) and {m.name for m in members} == set(expected), 'Actual raw archive file set differs')
        for member in members:
            require(member.isfile(), 'Raw archive contains a nonregular member')
            row = expected[member.name]; digest = hashlib.sha256(); count = 0
            with tar.extractfile(member) as stream:
                while content := stream.read(1024*1024):
                    count += len(content); digest.update(content)
            require(count == row['bytes'] and digest.hexdigest() == row['sha256'], 'Copied raw archive bytes differ')
    for row in capture['files']: checked(row['path'], row)
    captured = {r['path'] for r in capture['files']}
    needed = set()
    for record in inventory['complete_source_private_closure'].values():
        identity = record['identity']
        needed.add(identity['source']['path']); needed.update(r['path'] for r in identity['facets'])
    from qualified_algebra import MODULE,validate
    protected = validate(session)
    needed.update(row['path'] for row in protected['authentic_original_payloads'])
    needed.add(protected['current_source']['path'])
    needed.add(protected['current_setup']['path'])
    needed.update(row['path'] for row in protected['current_all_prior_actual_inputs'])
    needed.update(row['path'] for row in protected['current_five_facets'])
    needed.add(protected['current_additional_ilean']['path'])
    for name in [*data()['compile_order'], 'T01Audit']:
        from qualified_direct import protected_modules
        if name in protected_modules(): continue
        path = session.logs/'direct-inputs'/(name+'.json'); needed.add(str(path))
        receipt = read(path)
        needed.add(receipt['source']['path']); needed.update(r['path'] for r in receipt['files'])
    needed.update(str(session.project/n) for n in ['T01Audit.lean', 'T01_PROVENANCE.json', 'LEANPOOL_LICENSE', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'])
    require(needed <= captured, 'A prepared setup/import/library/source/private artifact was omitted from complete raw capture')
    from qualified_direct import required_capture_paths,validate as validate_all
    required = required_capture_paths(validate_all(session))
    require(required <= captured, 'R4 protected current source/setup/all actual inputs/six outputs/original evidence omitted from complete raw capture')


def finalize():
    session = WeilSession(); installed(); session.qualification_inputs()
    objects = check_outputs(session)
    # Reconstruct from the same authenticated kernel/types streams. A changed
    # stored inventory is rejected, never overwritten with a new self-signature.
    inventory = validated_inventory(session)
    require(session.receipt('WEIL_FULL_INVENTORY.json') == dict(binding=session.binding, **inventory),
            'Final complete inventory/terminals/implementation/safe replay differ from original authenticated stdout')
    require(inventory['module_identities'] == objects['identities'], 'Final physical proof identities differ')
    counts = session.compile_census(True)
    from qualified_algebra import validate
    protected_input = validate(session)
    from qualified_direct import validate as validate_all
    protected_inputs = validate_all(session)
    runtime = session.receipt('WEIL_RUNTIME_PROCESS.json')['process']
    runtime_argv = [sys.executable, str(HERE/'reused/ci_runtime_guard.py'), 'audit', '--probe', '--require-source']
    process_receipt(session, runtime, 'runtime-audit', runtime_argv)
    actual = read(session.logs/'runtime/audit.json')
    require(actual['status'] == 'PASS_RUNTIME_GUARD_ONLY' and actual['probe'] is True
            and actual['state_sha256'] == sha(session.logs/'runtime/state.json')
            and actual['command_log_sha256'] == sha(session.state['log'])
            and 'PASS_RUNTIME_GUARD_ONLY' in Path(runtime['stdout']).read_text(encoding='utf-8'), 'Actual original runtime probe/state/commands changed')
    retention = session.receipt('WEIL_RETENTION.json'); capture = session.receipt('WEIL_RAW_CAPTURE.json')
    output = Path(os.environ['CACHE_CHECKPOINT_OUTPUT']).resolve()
    config_path = session.logs/'CHECKPOINT_COLLECTOR_INPUT.json'
    expected_argv = [sys.executable, str(HERE/'reference/checkpoint_objects_v3.py'), '--project', str(session.project),
                     '--manifest', str(config_path), '--logs', str(session.logs), '--output', str(output)]
    require(retention['argv'] == expected_argv and retention['cwd'] == str(session.project)
            and retention['exit_code'] == 0 and retention['output'] == str(output) and not retention['integrity_errors']
            and retention['collector_sha256'] == COLLECTOR == sha(HERE/'reference/checkpoint_objects_v3.py')
            and retention['collector_bytes'] == 32993 and retention['collector_manifest_sha256'] == sha(config_path)
            and retention['stdout_sha256'] == sha(session.logs/'checkpoint-collection.log')
            and retention['raw_capture_sha256'] == sha(session.logs/'WEIL_RAW_CAPTURE.json'), 'Original collector exact process/input/output binding changed')
    require(read(config_path) == collector_manifest(session.project), 'Actual exact34 collector source graph/audit manifest changed')
    rows = source_rows(); graph_hash = hashlib.sha256(json.dumps(rows, sort_keys=True).encode()).hexdigest()
    provenance = session.project/'T01_PROVENANCE.json'
    require(read(provenance) == dict(schema='weil34-exact-source-original-profile-provenance-v1',
        binding=session.binding, modules=data()['source_rows'], adapter_stage_B='HOLD', full_J=False), 'Actual staged source provenance changed')
    state_path, command_path, audit_path = session.logs/'runtime/state.json', Path(session.state['log']), session.logs/'runtime/audit.json'
    require(retention['root_source_count'] == len(rows) == 34 and retention['root_source_rows_sha256'] == graph_hash
            and retention['source_manifest_sha256'] == sha(BUNDLE/'STAGE_A34.json')
            and retention['provenance_sha256'] == sha(provenance)
            and retention['runtime_state_sha256'] == sha(state_path)
            and retention['current_command_log'] == dict(path=str(command_path), sha256=sha(command_path)), 'Collector source/provenance/state/command graph changed')
    raw_path = output/'CHECKPOINT.json'; raw = read(raw_path); summary_path = session.logs/'CHECKPOINT_SUMMARY.json'
    summary = read(summary_path)
    checkpoint_summary = {k:raw[k] for k in ['source_commit', 'run_id', 'run_attempt', 'manifest_sha256',
                                            'runtime_audit_valid', 'all_dependency_source_pins_valid']}
    require(str(raw['source_commit']) == session.binding['source_commit'] and str(raw['run_id']) == session.binding['run_id']
            and str(raw['run_attempt']) == session.binding['run_attempt'] and raw['runtime_audit_valid']
            and raw['all_dependency_source_pins_valid'] and raw['manifest_sha256'] == sha(config_path)
            and raw['runtime_state'] == session.state and raw['source_identity_sha256'] == graph_hash
            and retention['checkpoint_summary'] == checkpoint_summary and retention['checkpoint_sha256'] == sha(raw_path), 'Original checkpoint exact run/attempt/manifest/source/runtime summary changed')
    require(set(raw['sources_and_data']) == {r['install_path'] for r in rows} | {'T01Audit.lean'}
            and all(raw['sources_and_data'][r['install_path']]['sha256'] == r['sha256']
                    and raw['sources_and_data'][r['install_path']]['bytes'] == r['bytes'] for r in rows)
            and raw['sources_and_data']['T01Audit.lean']['sha256'] == sha(BUNDLE/'WeilAudit.lean')
            and raw['sources_and_data']['T01Audit.lean']['bytes'] == (BUNDLE/'WeilAudit.lean').stat().st_size,
            'Original collector actual source records differ from exact34/frozen exporter')
    require(all(raw['files'][str(path)]['sha256'] == sha(path) for path in [state_path, command_path, audit_path, config_path])
            and retention['actual_collector_summary'] == summary and retention['actual_collector_summary_sha256'] == sha(summary_path)
            and summary == dict(status=raw['status'], completed_compile_candidates=raw['completed_compile_candidates'],
                module_count=len(raw['modules']), payload_blobs=raw['saved_unique_payload_blobs'], checkpoint_sha256=sha(raw_path), green=False),
            'Original checkpoint current state/audit/commands/summary file identities changed')
    names = [r['module'] for r in raw['modules']]
    require(len(names) == 35 and len(names) == len(set(names)) and set(names) == set(data()['compile_order']) | {'T01Audit'}, 'Original collector module census differs')
    validate_capture(session, capture, inventory)
    evidence = ['WEIL_FULL_INVENTORY.json', 'WEIL_KERNEL_PROCESS.json', 'direct-results/T01Audit.json',
                'WEIL_STANDARD_INPUTS.json', 'CACHE_QUALIFICATION.json', 'CACHE_BOOTSTRAP_QUALIFICATION.json',
                'WEIL_RUNTIME_PROCESS.json', 'runtime/state.json', 'runtime/audit.json', 'WEIL_RETENTION.json',
                'WEIL_RAW_CAPTURE.json', 'CHECKPOINT_COLLECTOR_INPUT.json', 'CHECKPOINT_SUMMARY.json',
                'WEIL_PRIOR_DIRECT_ACQUISITION.json', 'WEIL_PRIOR_DIRECT_ALGEBRA_QUALIFICATION.json']
    session.emit('WEIL_STAGE_A_ACCEPTANCE.json', dict(status='PASS_EXACT34_PROJECT433RC1_26A6_COMPATIBILITY_ONLY',
        evidence={name:sha(session.logs/name) for name in evidence}, actual_kernel_process=inventory['actual_kernel_process'],
        actual_types_process=inventory['actual_types_process'], actual_checkpoint_summary=checkpoint_summary,
        source_manifest_sha256=session.binding['source_manifest_sha256'], compiler_census=counts,
        protected_prior_direct_input=protected_input,protected_multi_producer_inputs=protected_inputs,
        exact_partition=dict(protected=15,fresh_compiles=19,fresh_proof_scope=34),
        original_collector_restore_eligibility_not_overridden=True, executable_implementation_kernel_or_termination_credit=False,
        all34_private_generated_declarations_two_full_types_direct_axioms_and_safe_kernel_verified=True,
        actual_private_dependency_source_object_owner_coverage_verified=True,
        adapter_stage_B='HOLD_ALL_SIX_AND_COMPLETE_REAL_DEPENDENCY_GRAPH_REQUIRED',
        half_support_closed=False, full_J=False, whole_manuscript_accepted=False, goal_count_change=0))


if __name__ == '__main__':
    require(sys.argv[1] in {'runtime', 'retain', 'finalize'}, 'Unknown runtime/retention phase')
    globals()[sys.argv[1]]()
