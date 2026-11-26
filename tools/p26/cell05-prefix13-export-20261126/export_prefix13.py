#!/usr/bin/env python3
"""Recheck/export the exact 13-owner prefix of the failed original 14-owner run.

This wrapper imports the pinned original validators from their existing stage.
It never executes Lean, alters original evidence, or creates a SUCCESS receipt.
"""
from pathlib import Path
import argparse
import fcntl
import hashlib
import importlib
import json
import os
import stat
import sys

sys.dont_write_bytecode = True

STAGE = Path('/workspace/p26-cell05-connections14-stage-557a12f3bcd7')
OUTPUT = Path('/workspace/p26-cell05-connections13-prefix-557a12f3bcd7')
TOOL = Path('tools/p26/cell05-connections14-run-20261126')
PILOT = 'ready14-pilot-v1'
CONTINUATION = 'ready14-complete-v1'
PREFIX = 'ImbalancedChen.P2OriginalSaving19Geometry05Scalable'
SUFFIXES = (
    'Active8EnumerationHeader', 'Active8EnumerationField', 'VerticesHeader', 'VerticesField',
    'VertexValuesHeader', 'VertexValuesField', 'AllOriginalConstraintMinimaHeader',
    'AllOriginalConstraintMinimaField', 'FacetVerticesHeader', 'FacetVerticesField',
    'FaceLedgerHeader', 'FaceLedgerField', 'SimplicesHeader', 'ShapeArrays',
)
MODULES = tuple(PREFIX + suffix for suffix in SUFFIXES)
MODES = ('normal', 'kernel', 'owned')
VERIFIER_PIN = {'bytes': 88101, 'sha256': '77c9b626b8ae1b2329f19bbeaff41e75db4d7b14e641c2fae2c97fd771d4dcbf'}


def require(value, message):
    if not value:
        raise ValueError(message)


def data_pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def bootstrap(stage):
    """Authenticate the unchanged workflow before importing any stage helper."""
    require(sys.flags.optimize == 0, 'Original validators require Python assertions')
    require(stage == STAGE, 'Only the original fixed failed stage is supported')
    here = stage / TOOL
    for path in [*reversed(here.parents), here]:
        mode = path.lstat().st_mode
        require(stat.S_ISDIR(mode) and not stat.S_ISLNK(mode), 'Unsafe stage ancestor')
    verifier = here / 'CONNECTIONS14_VERIFIER.json'
    require(stat.S_ISREG(verifier.lstat().st_mode), 'Verifier must be a regular file')
    body = verifier.read_bytes()
    require(data_pin(body) == VERIFIER_PIN, 'Not the frozen v1 fourteen-target verifier')
    config = json.loads(body)
    for row in config['workflow_files']:
        relative = Path(row['relative_path'])
        require(not relative.is_absolute() and '..' not in relative.parts, 'Unsafe frozen workflow path')
        path = here / relative
        for ancestor in path.parents:
            if ancestor == here:
                break
            require(stat.S_ISDIR(ancestor.lstat().st_mode), 'Unsafe workflow ancestor')
        require(stat.S_ISREG(path.lstat().st_mode), 'Nonregular frozen workflow file')
        require(data_pin(path.read_bytes()) == {key: row[key] for key in ('bytes', 'sha256')},
                'Frozen workflow changed: ' + str(relative))
    sys.path.insert(0, str(here))
    R = importlib.import_module('receipt_checks')
    V = importlib.import_module('verify_connections14')
    E = importlib.import_module('export_connections14')
    for name in ('receipt_checks', 'verify_connections14', 'export_connections14',
                 'fields_only_join', 'receipt_support', 'runtime_compat', 'runtime_probe',
                 'evidence_io', 'supplier_capsule', 'portable_receipts', 'supplier_join',
                 'baseline_checks'):
        require(Path(sys.modules[name].__file__).absolute() == here / (name + '.py'),
                'Unexpected helper import origin: ' + name)
    return R, V, E, here


def check_indexes(context, reusable, pilot, stopped):
    """Check only the partial-index contract; original validators check all proofs."""
    require(tuple(row['module'] for row in context['targets']) == MODULES,
            'Original fourteen-target context/order changed')
    expected = [(module, mode) for module in MODULES[:13] for mode in MODES]
    records = stopped['records']
    require(stopped.get('status') == 'stopped' and 'failed_result' in stopped,
            'Expected the original failed continuation index')
    require([(row.get('module'), row.get('mode')) for row in records] == expected,
            'Failed index must contain exactly the complete first 39 steps')
    require(stopped.get('newly_executed_steps') == 37 and stopped.get('reused_steps') == 3,
            'Failed attempt must retain 36 new acceptances, one failed command, and three reused steps')
    require(pilot.get('status') == 'stopped' and pilot.get('reason') == 'new_step_budget'
            and pilot.get('accepted_steps') == 3 and pilot.get('accepted_targets') == 1
            and pilot.get('newly_executed_steps') == 3 and pilot.get('reused_steps') == 0
            and pilot.get('whole_geometry_decoded') is False and pilot.get('P2_6_complete') is False,
            'Pilot is not the original three-step budget boundary')
    require([(row.get('module'), row.get('mode')) for row in pilot['records']] == expected[:3],
            'Pilot record order differs')
    objects, steps = {}, []
    for index, row in enumerate(records):
        key = row['module'], row['mode']
        item = reusable[key]
        require(item is not None and row['accepted'] == item['accepted'], 'Index does not bind the validated original seal')
        attempt = Path(row['accepted']['path']).parent.parent.name
        require(attempt == (PILOT if index < 3 else CONTINUATION), 'Unexpected original acceptance attempt')
        require(row.get('disposition') == ('reused' if index < 3 else 'executed'),
                'Incorrect continuation execution/reuse label')
        if index < 3:
            earlier = pilot['records'][index]
            require(earlier['accepted'] == row['accepted'] and earlier.get('disposition') == 'executed',
                    'Pilot prefix was replaced or relabelled')
        obj = item['result']['object']
        previous = objects.setdefault(row['module'], obj)
        require(previous == obj, 'Normal/kernel/owned do not bind one exact object')
        steps.append(item)
    require(len(objects) == 13 and all(reusable[MODULES[13], mode] is None for mode in MODES),
            'ShapeArrays has acceptance or the prefix omits an owner')
    return steps, objects


def check_failed_normal(R, context, run_path, stopped):
    """Preserve the genuine failed ShapeArrays chain separately from accepted work."""
    module = MODULES[13]
    folder = run_path.parent / module.split('.')[-1]
    result_path = folder / 'normal-result.json'
    result = R.checked(stopped['failed_result'], result_path)
    require(result.get('schema') == 'cell05_connections14_step_result_v1'
            and result.get('module') == module and result.get('mode') == 'normal'
            and result.get('status') == 'failed' and result.get('exit_code') == 1
            and result.get('termination_reason') is None and 'validation_error' not in result,
            'Expected the original first normal failure, not a successful/evidence-failed record')
    command_path = folder / 'normal-command.json'
    command = R.checked(result['command'], command_path)
    require(command.get('schema') == 'cell05_connections14_step_command_v1'
            and command.get('module') == module and command.get('mode') == 'normal',
            'Failed command labels differ')
    for value in (command, result):
        require(value.get('run') == R.fp(run_path), 'Failed chain RUN identity differs')
    require(command.get('argv') == R.expected_argv(context, module, 'normal')
            and command.get('cwd') == context['cwd'] and command.get('environment') == context['environment'],
            'Failed command context differs')
    paths = R.target_paths(context, module)
    source = R.fp(paths['source'])
    require(R.same(source, context['targets'][13]['source']), 'Failed source changed')
    dependencies = R.dependency_objects(context, module)
    for value in (command, result):
        require(value.get('source') == source and value.get('audit_source') is None
                and value.get('dependency_objects') == dependencies, 'Failed chain source/dependency binding differs')
    require(command.get('object_before') is None and result.get('object') is None
            and not paths['object'].exists(), 'Unexpected object from the failed normal command')
    log_path = folder / 'normal.log'
    require(result.get('log') == R.fp(log_path), 'Failed log identity differs')
    require(set(path.name for path in R.tree_files(folder)) ==
            {'normal-command.json', 'normal-result.json', 'normal.log'},
            'Unexpected ShapeArrays seal, later step, or failure artifact')
    return {'result': R.fp(result_path), 'command': R.fp(command_path), 'log': R.fp(log_path),
            'source': source, 'module': module, 'mode': 'normal', 'status': 'failed', 'exit_code': 1,
            'accepted': False, 'object': None}


def validate_prefix(R, V, here):
    config, registry, joined = V.load_configuration(here)
    run_path = STAGE / 'verification' / CONTINUATION / 'RUN.json'
    stopped_path = run_path.with_name('STOPPED.json')
    stopped = R.read(stopped_path)
    run = R.checked(stopped['run'], run_path)
    require(run.get('schema') == 'cell05_connections14_run_v1' and run.get('attempt') == CONTINUATION,
            'Unexpected failed continuation RUN')
    context = run['context']
    V.bind_context_to_package(context, here, config, registry, joined)
    require(context['stage'] == str(STAGE), 'Original stage changed')
    pilot_path = STAGE / 'verification' / PILOT / 'STOPPED.json'
    pilot = R.read(pilot_path)
    pilot_run = R.checked(pilot['run'], pilot_path.with_name('RUN.json'))
    require(pilot_run.get('schema') == 'cell05_connections14_run_v1'
            and pilot_run.get('attempt') == PILOT and pilot_run.get('context') == context,
            'Pilot and continuation did not use the identical full fourteen-target context')
    attempts = {path.name for path in (STAGE / 'verification').iterdir()}
    require(attempts == {PILOT, CONTINUATION}, 'Unexpected attempt requires separate review')
    require(not any((STAGE / 'verification' / name / 'SUCCESS.json').exists()
                    for name in attempts), 'A full-batch SUCCESS must not be treated as this failed prefix')
    R.reject_missing_successful_objects(STAGE, MODULES)
    reusable = {(module, mode): R.prior(context, module, mode) for module in MODULES for mode in MODES}
    require(R.require_accepted_prefix(context, reusable) == 39, 'Not the exact complete 13-owner prefix')
    steps, objects = check_indexes(context, reusable, pilot, stopped)
    failure = check_failed_normal(R, context, run_path, stopped)
    return {'config': config, 'registry': registry, 'joined': joined, 'context': context,
            'steps': steps, 'objects': objects, 'failure': failure,
            'pilot_index': R.fp(pilot_path), 'failed_index': R.fp(stopped_path),
            'records': stopped['records']}


def freeze_inputs(R, state):
    paths = R.tree_files(STAGE)
    paths += [Path(row['path']) for row in state['context']['frozen_inputs']]
    return {str(path): R.fp(path) for path in sorted(set(paths))}


def export_prefix(R, V, E, here, output_dir, state):
    require(output_dir == OUTPUT, 'Only the fixed independent prefix-export root is supported')
    require(not output_dir.exists(), 'Independent export directory already exists; preserve it, do not overwrite')
    for root in (STAGE, Path(state['joined']['supplier_project']), Path(state['joined']['supplier_objects'])):
        R.disjoint(output_dir, root)
    script = R.canonical(Path(__file__).absolute(), True)
    require(not script.is_relative_to(STAGE), 'The exporter must remain outside the original stage')
    R.disjoint(output_dir, script.parent)
    before = freeze_inputs(R, state)
    entries = {}

    def select(path):
        path = R.canonical(path, True)
        require(path.is_relative_to(STAGE), 'Unexpected original stage file')
        member = path.relative_to(STAGE).as_posix()
        require(member not in ('PARTIAL_INDEX.json', 'EXPORT_MANIFEST.json'), 'Reserved member collision')
        previous = entries.setdefault(member, path)
        require(previous == path, 'Duplicate member with different origin')

    # Keep all fourteen original source/audit inputs, including the failed source.
    # Only the thirteen accepted object bodies are selected.
    for index, row in enumerate(state['config']['targets']):
        relative = Path(row['module'].replace('.', '/'))
        for directory in ('sources', 'project'):
            select(STAGE / directory / relative.with_suffix('.lean'))
        select(here / row['audit_relative_path'])
        if index < 13:
            select(STAGE / 'objects' / relative.with_suffix('.olean'))
    for row in state['config']['workflow_files']:
        select(here / row['relative_path'])
    select(here / 'CONNECTIONS14_VERIFIER.json')
    select(here / 'SUPPLIER_JOIN.json')
    for path in R.verification_files(STAGE, MODULES):
        select(path)
    expected_objects = {module.replace('.', '/') + '.olean' for module in MODULES[:13]}
    actual_objects = {name.removeprefix('objects/') for name in entries if name.startswith('objects/')}
    require(actual_objects == expected_objects and len(actual_objects) == 13,
            'Export must contain exactly the thirteen accepted new objects')
    require(not any(name.endswith('.olean') and not name.startswith('objects/') for name in entries),
            'Unexpected old or failed object outside the accepted object root')
    entries['partial-export/export_prefix13.py'] = script
    owned = [item['result'] for item in state['steps'] if item['result']['mode'] == 'owned']
    original_mapping = [{'original': R.fp(path), 'archive_member': member}
                        for member, path in sorted(entries.items())]
    index = {
        'schema': 'cell05_connections14_prefix13_independent_index_v1',
        'status': 'THIRTEEN_OWNER_PREFIX_VALIDATED_FOURTEENTH_NORMAL_FAILED',
        'original_stage': str(STAGE), 'original_target_count': 14, 'original_planned_steps': 42,
        'original_context': state['context'], 'pilot_index': state['pilot_index'],
        'failed_continuation_index': state['failed_index'], 'original_records': state['records'],
        'accepted_targets': 13, 'accepted_steps': 39,
        'step_counts': {'normal': 13, 'kernel': 13, 'owned': 13},
        'accepted_objects': state['objects'],
        'owned_declaration_count': sum(row['owned_declaration_count'] for row in owned),
        'pilot_new_accepted_steps': 3, 'continuation_reused_accepted_steps': 3,
        'continuation_new_accepted_steps': 36, 'continuation_failed_commands': 1,
        'continuation_raw_newly_executed_steps': 37,
        'failed_fourteenth_owner': state['failure'],
        'old_supplier_proof_commands': 0, 'Lean_commands_executed_for_export': 0,
        'full_fourteen_target_success': False, 'whole_geometry_decoded': False, 'P2_6_complete': False,
        'original_evidence_rewritten': False, 'original_context_reduced_to_thirteen_targets': False,
        'supplier_join': state['context']['supplier_join'], 'runtime_guard': state['context']['runtime_guard'],
        'original_to_archive_map': original_mapping,
        'scope': 'First thirteen original header/field owners only; failed ShapeArrays has no acceptance; nine downstream owners remain excluded',
    }
    R.dump_new(output_dir / 'PARTIAL_INDEX.json', index)
    entries['PARTIAL_INDEX.json'] = output_dir / 'PARTIAL_INDEX.json'
    manifest = {
        'schema': 'cell05_connections14_prefix13_cloud_export_v1',
        'status': index['status'], 'original_stage': str(STAGE),
        'original_attempt': CONTINUATION, 'original_target_count': 14,
        'partial_index': R.fp(output_dir / 'PARTIAL_INDEX.json'), 'partial_index_member': 'PARTIAL_INDEX.json',
        'accepted_targets': 13, 'accepted_steps': 39, 'step_counts': index['step_counts'],
        'owned_declaration_count': index['owned_declaration_count'],
        'failed_fourteenth_owner': state['failure'],
        'members': [{'member': member, **data_pin(path.read_bytes())} for member, path in sorted(entries.items())],
        'old_supplier_object_bodies_included': False, 'failed_object_body_included': False,
        'old_supplier_proof_commands': 0, 'Lean_commands_executed_for_export': 0,
        'original_evidence_rewritten': False, 'full_fourteen_target_success': False,
        'whole_geometry_decoded': False, 'P2_6_complete': False, 'automatic_archive_transfer': False,
    }
    archive_path = output_dir / 'connections14-prefix13-v1-evidence.tar.xz'
    archive_identity = E.write_verified_archive(archive_path, entries, manifest)
    after_state = validate_prefix(R, V, here)
    require(after_state == state, 'Validated original prefix/context/failure changed during export')
    require(freeze_inputs(R, after_state) == before, 'Original stage or frozen external input changed during export')
    E.recheck_archive(archive_path, manifest)
    report = {
        'schema': 'cell05_connections14_prefix13_cloud_export_report_v1',
        'status': 'PASS_PARTIAL_PREFIX13_EXPORT_RECHECK', 'archive': archive_identity,
        'partial_index': R.fp(output_dir / 'PARTIAL_INDEX.json'),
        'archive_members': len(entries) + 1, 'accepted_targets': 13, 'accepted_steps': 39,
        'owned_declaration_count': index['owned_declaration_count'],
        'step_counts': index['step_counts'], 'pilot_reused_steps': 3,
        'failed_fourteenth_owner': state['failure'], 'runtime_guard': state['context']['runtime_guard'],
        'original_context_target_count': 14, 'original_stage_and_frozen_inputs_unchanged': True,
        'archive_member_recheck_passed': True, 'old_supplier_object_bodies_included': False,
        'old_supplier_proof_commands': 0, 'Lean_commands_executed_for_export': 0,
        'original_receipts_rewritten': False, 'full_fourteen_target_success': False,
        'whole_geometry_decoded': False, 'P2_6_complete': False, 'automatic_archive_transfer': False,
    }
    R.dump_new(output_dir / 'PARTIAL_EXPORT_REPORT.json', report)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=OUTPUT)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    R, V, E, here = bootstrap(STAGE)
    output = R.canonical(args.output_dir)
    # Open the existing lock read-only. The original executor uses an exclusive
    # lock on this inode, so a live writer blocks this evidence-only operation.
    lock_path = R.canonical(STAGE / 'EXECUTION.lock', True)
    require(stat.S_ISREG(lock_path.lstat().st_mode), 'Original execution lock is not regular')
    with lock_path.open('rb') as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
        state = validate_prefix(R, V, here)
        if args.check_only:
            report = {'status': 'PASS_ORIGINAL_PREFIX13_RECEIPTS_NO_EXPORT',
                      'accepted_targets': 13, 'accepted_steps': 39,
                      'failed_fourteenth_owner': state['failure'],
                      'original_context_target_count': 14, 'full_fourteen_target_success': False,
                      'Lean_commands_executed': 0, 'P2_6_complete': False}
        else:
            report = export_prefix(R, V, E, here, output, state)
    print(json.dumps(report, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
