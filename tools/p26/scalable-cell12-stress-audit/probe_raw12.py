#!/usr/bin/env python3
"""Read-only cloud inventory for raw12 evidence and existing stress successes.

This program writes no file, runs no subprocess and prints metadata only.
Its output is a discovery report, never a substitute for strict acceptance.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

sys.dont_write_bytecode = True


def fingerprint(path):
    path = Path(path)
    digest, count = hashlib.sha256(), 0
    with path.open('rb') as handle:
        while data := handle.read(1024 * 1024):
            digest.update(data)
            count += len(data)
    return {'path': str(path), 'resolved_path': str(path.resolve()), 'bytes': count, 'sha256': digest.hexdigest()}


def same(actual, expected):
    return all(actual[key] == expected[key] for key in ('bytes', 'sha256'))


def observe(identity):
    path = Path(identity['path'])
    if not path.is_file():
        return {'path': str(path), 'exists': False, 'matches_pin': False}
    result = fingerprint(path)
    return {**result, 'exists': True, 'matches_pin': same(result, identity)}


def verified_json(identity):
    observed = observe(identity)
    if not observed['matches_pin']:
        return observed, None
    assert identity['bytes'] < 2 * 1024 * 1024, 'Unexpectedly large historical JSON'
    return observed, json.loads(Path(identity['path']).read_text())


def checked_log(path, sha256, exact=None):
    path = Path(path)
    if not path.is_file():
        return {'path': str(path), 'exists': False, 'matches_recorded_sha256': False}
    observed = fingerprint(path)
    result = {**observed, 'exists': True, 'matches_recorded_sha256': observed['sha256'] == sha256}
    if exact is not None:
        result['matches_exact_target_log'] = path.read_text().strip() == exact
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--plan', required=True, help='Exact RAW12_HISTORY_LOCATORS.json from the local audit')
    parser.add_argument('--stage', action='append', default=[], help='Known stress stage to inspect, never modified')
    parser.add_argument('--generic-objects', default='/workspace/p26-continuation-59264dd64286/scalable-geometry/objects')
    args = parser.parse_args()
    plan = json.loads(Path(args.plan).read_text())
    assert plan['schema'] == 'cell12_raw_history_locators_v1'
    module = plan['module']
    assert module == 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12'
    history = plan['historical_locations']
    output = {'schema': 'cell12_raw_readonly_discovery_v1', 'status': 'DISCOVERY_ONLY_NOT_ACCEPTANCE',
              'plan': fingerprint(args.plan), 'module': module, 'new_Lean_steps_run': 0,
              'files_written': 0, 'proof_subprocesses': 0,
              'full_current_context_kernel_closed': False}
    normal_pin, normal = verified_json(history['normal_receipt'])
    output['normal_receipt'] = normal_pin
    wrapper_pins = [identity for group in history['successful_wrapper_runs'] for identity in group]
    wrappers = {}
    output['wrapper_and_input_context_files'] = []
    for identity in wrapper_pins:
        observed, document = verified_json(identity)
        output['wrapper_and_input_context_files'].append(observed)
        if document is not None:
            wrappers[Path(identity['path']).name] = document
    if normal is not None:
        command = normal['normal_command']
        outputs = normal['source_plus_five_outputs']
        output['normal_binding_checks'] = {
            'module_exact': normal['module'] == module, 'status': normal['status'],
            'exit_code': command['exit_code'], 'argv': command['argv'], 'cwd': command['cwd'],
            'source_matches_expected': same(outputs[module.replace('.', '/') + '.lean'], plan['exact_source']),
            'object_matches_expected': same(outputs['.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'], plan['exact_object']),
            'command_receipt': checked_log(command['command_receipt'], command['command_sha256']),
            'log': checked_log(command['log'], command['log_sha256']),
            'historical_project_dependency_objects': normal['dependency_context']['dependency_objects_and_traces']}
    validation_observed = []
    for identity in history['audit_receipts']:
        observed, validation = verified_json(identity)
        entry = {'receipt': observed}
        if validation is not None:
            lane = Path(identity['path']).parent
            command = validation['kernel_commands'][module]
            kernel_log = lane / command['log']
            assert kernel_log.resolve().is_relative_to(lane.resolve()), 'Historical log escaped its lane'
            audit = validation['audit_command']
            owned_log = lane / audit['log']
            assert owned_log.resolve().is_relative_to(lane.resolve()), 'Historical owned log escaped its lane'
            outputs = validation['source_plus_five_outputs'][module]
            entry.update({
                'status': validation['status'], 'modules': validation['modules'],
                'kernel_argv': command['argv'], 'kernel_cwd': command['cwd'], 'kernel_exit_code': command['exit_code'],
                'kernel_targets_raw12': command['argv'][-3:] == ['leanchecker', '--verbose', module],
                'kernel_log': checked_log(kernel_log, command['log_sha256'], 'replaying ' + module),
                'owned_exit_code': audit['exit_code'], 'owned_argv': audit['argv'],
                'owned_log': checked_log(owned_log, audit['log_sha256']),
                'total_owned_exports': validation['total_owned_exports'],
                'full_owned_including_private_generated': validation['full_owned_including_private_generated'],
                'only_standard_axioms': validation['only_standard_axioms'],
                'source_object_unchanged_across_checks': validation['source_plus_five_outputs_unchanged_across_kernel_and_audit'],
                'successful_normal_not_repeated': validation['successful_normal_not_repeated'],
                'target_source_matches_expected': same(outputs[module.replace('.', '/') + '.lean'], plan['exact_source']),
                'target_object_matches_expected': same(outputs['.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'], plan['exact_object']),
                'full_owned_log_not_reparsed_by_this_discovery_script': True})
        validation_observed.append(entry)
    output['historical_validations'] = validation_observed
    if 'RESULT.json' in wrappers:
        result = wrappers['RESULT.json']
        output['wrapper_result_scope'] = {key: result.get(key) for key in
            ['status', 'module', 'accepted_owners', 'normal_passed', 'accepted_for_actual_P1_context_only',
             'archive_complete', 'archive_shape_or_row_guards_proved', 'target_source_sha256']}
        original = next(row for row in result['loader_inputs'] if row['family'] == 'geometry' and row['cell'] == 12)
        output['historical_raw12_input_pin_matches'] = same(original, plan['original_input'])
    input_pin = {**plan['original_input'], 'path': plan['original_input']['resolved_actual_path']}
    output['current_original_input'] = observe(input_pin)
    short = module.split('.')[-1]
    provider_pairs = [
        ('frozen_archive_extra', Path('/workspace/p26-continuation-59264dd64286/cell00/archive-extra/sources'),
         Path('/workspace/p26-continuation-59264dd64286/cell00/archive-extra/objects')),
        ('blue_member_existing', Path('/workspace/blue-member-build'), Path('/workspace/blue-member-build/.lake/build/lib/lean'))]
    output['raw12_provider_candidates'] = []
    for label, sources, objects in provider_pairs:
        output['raw12_provider_candidates'].append({'label': label,
            'source': observe({**plan['exact_source'], 'path': str(sources/'ImbalancedChen'/(short+'.lean'))}),
            'object': observe({**plan['exact_object'], 'path': str(objects/'ImbalancedChen'/(short+'.olean'))})})
    output['current_generic_object_candidates'] = []
    for row in plan['eight_current_generic_suppliers']:
        path = Path(args.generic_objects)/(row['module'].replace('.', '/')+'.olean')
        output['current_generic_object_candidates'].append({'module': row['module'],
            **observe({**row['object'], 'path': str(path)})})
    stages = args.stage or ['/workspace/p26-continuation-59264dd64286/scalable-geometry']
    stress_shorts = ['P2OriginalSaving19Geometry12Scalable'+suffix for suffix in
                    ['Input', 'SimplicesBlock000', 'TypedRows000', 'SimplicesBlock412', 'TypedRows412',
                     'SimplicesBlock824', 'TypedRows824']]
    censuses = []
    for value in stages:
        stage = Path(value)
        objects, markers = [], []
        for stress_short in stress_shorts:
            object_path = stage/'objects/ImbalancedChen'/(stress_short+'.olean')
            if object_path.is_file():
                objects.append(fingerprint(object_path))
            for pattern in ['*-result.json', '*-accepted.json']:
                for path in sorted((stage/'verification').glob('*/'+stress_short+'/'+pattern)):
                    document = json.loads(path.read_text())
                    markers.append({**fingerprint(path), **{key: document.get(key) for key in ['module','mode','status','exit_code']}})
        indexed = []
        for filename in ('SUCCESS.json', 'STOPPED.json'):
            for path in sorted((stage/'verification').glob('*/'+filename)):
                document = json.loads(path.read_text())
                rows = [row for row in document.get('records', [])
                        if row.get('module', '').split('.')[-1] in stress_shorts]
                if rows:
                    indexed.append({**fingerprint(path), 'matching_record_count': len(rows)})
        censuses.append({'stage': str(stage), 'existing_objects': objects,
                         'success_or_failure_marker_count': len(markers), 'markers_first_12': markers[:12],
                         'markers_truncated': len(markers)>12, 'success_or_stopped_indexes': indexed,
                         'strict_v3_reuse_decision_not_made': True})
    output['known_stage_census'] = censuses
    text = json.dumps(output, separators=(',', ':'))
    if len(text.encode()) > 18000:
        for row in output['known_stage_census']:
            row['markers_first_12'] = []
            row['markers_truncated'] = row['success_or_failure_marker_count'] > 0
        output['metadata_census_details_trimmed_to_output_budget'] = True
        text = json.dumps(output, separators=(',', ':'))
    assert len(text.encode()) <= 20000, 'Metadata exceeds read budget; do not print unbounded output'
    print(text)


if __name__ == '__main__':
    main()
