#!/usr/bin/env python3
"""Read only genuine local fields73 metadata; never fabricate missing receipts."""
from pathlib import Path, PurePosixPath
import collections
import hashlib
import json
import sys

sys.dont_write_bytecode = True
REPO = Path(__file__).absolute().parents[3]
HERE = REPO / 'tools/p26/scalable-cell05-connections-run'
sys.path.insert(0, str(HERE))
from baseline_checks import verify_baseline
from portable_receipts import MODES, expected_argv
from supplier_capsule import load_plan, metadata, original_layout


def same(a, b):
    return all(a[k] == b[k] for k in ('bytes', 'sha256'))


def fp(path):
    body = path.read_bytes()
    return {'path': str(path), 'bytes': len(body),
            'sha256': hashlib.sha256(body).hexdigest()}


def main():
    plan = load_plan(HERE)
    spec, run, success, export = metadata(HERE, plan, 'fields73')
    context = run['context']
    stage = PurePosixPath(spec['stage'])
    assert run['schema'] == 'cell05_complete_run_v2'
    assert context['schema'] == 'cell05_complete_context_v2'
    assert success['schema'] == 'cell05_complete_success_v2'
    assert len(context['targets']) == 73 and len(context['suppliers']) == 15
    assert success['run'] == spec['run'] and export['success'] == spec['success']
    assert run['context'] == success['context']
    assert (success['accepted_targets'], success['accepted_steps']) == (73, 219)
    assert (success['newly_executed_steps'], success['reused_steps']) == (219, 0)
    assert success['status'] == 'succeeded' and success['frozen_inputs_unchanged']
    assert context['old_supplier_proof_commands'] == 0
    assert context['cloud_source_generation'] is False
    assert success['whole_geometry_decoded'] is False and success['P2_6_complete'] is False

    members = {row['member']: row for row in export['members']}
    assert len(members) == len(export['members']) == 1432
    path_pins = {str(stage / name): {'path': str(stage / name),
                    **{key: row[key] for key in ('bytes', 'sha256')}}
                 for name, row in members.items()}
    external = original_layout(context)
    assert not (set(path_pins) & set(external))
    path_pins.update({name: row['original'] for name, row in external.items()})
    frozen = {row['path']: row for row in context['frozen_inputs']}
    assert len(frozen) == len(context['frozen_inputs'])
    assert set(frozen) <= set(path_pins)
    for path, identity in frozen.items():
        assert path_pins[path] == identity, path
    for key in ('lean_binary', 'leanchecker_binary'):
        identity = context['runtime'][key]
        assert path_pins[identity['path']] == identity

    targets = [row['module'] for row in context['targets']]
    assert [(row['module'], row['mode']) for row in success['records']] == [
        (module, mode) for module in targets for mode in MODES]
    expected_step_paths = set()
    first = {}
    for item in success['records']:
        module, mode = item['module'], item['mode']
        accepted = item['accepted']
        folder = stage / 'verification' / run['attempt'] / module.split('.')[-1]
        assert accepted['path'] == str(folder / (mode + '-accepted.json'))
        assert path_pins[accepted['path']] == accepted
        assert item['disposition'] == 'executed'
        for name in (mode + '-accepted.json', mode + '-command.json',
                     mode + '-result.json', mode + '.log'):
            full = str(folder / name)
            assert full in path_pins
            expected_step_paths.add(full)
        if mode == 'owned':
            full = str(folder / 'owned-declarations.json')
            assert full in path_pins
            expected_step_paths.add(full)
        first.setdefault(mode, {'module': module, 'accepted': accepted,
            'expected_argv_from_original_context': expected_argv(context, module, mode, spec['tool_rel'])})

    original = REPO / spec['tool_rel']
    baseline_manifest = json.loads((original / 'BASELINE_EVIDENCE.json').read_text())
    baseline_names = ['BASELINE_EVIDENCE.json', 'SUPPLIER_REGISTRY.json'] + [
        row['relative_path'] for row in baseline_manifest['members']]
    assert len(baseline_names) == len(set(baseline_names)) == 156
    baseline_pins = []
    for name in baseline_names:
        identity = fp(original / name)
        assert same(identity, members[spec['tool_rel'] + '/' + name]), name
        baseline_pins.append(identity)
    baseline = verify_baseline(original)
    assert baseline['full_supplier_kernel_closed_in_combined_evidence'] is True
    assert baseline['old_Lean_commands_executed'] == 0

    supplier_registry = json.loads((HERE / 'SUPPLIER_REGISTRY.json').read_text())
    registry = {row['module']: row for row in supplier_registry['suppliers']}
    for row in context['suppliers']:
        assert registry[row['module']] == row
    for row in context['targets']:
        module = row['module']
        assert registry[module]['source'] == row['source']
        assert registry[module]['project_imports'] == row['project_imports']
        assert same(registry[module]['object'], members['objects/' + module.replace('.', '/') + '.olean'])
        assert same(fp(REPO / (module.replace('.', '/') + '.lean')), row['source'])

    runtime_pins = json.loads((HERE / 'RUNTIME_COMPATIBILITY_PINS.json').read_text())
    for row in runtime_pins['files']:
        assert same(fp(HERE / row['relative_path']), row)
    summaries = {host: json.loads((HERE / f'runtime-evidence/runtime-{host}-SUMMARY.json').read_text())
                 for host in ('P1', 'P2')}
    logical = lambda x: [{k: v for k, v in row.items() if k != 'physical_root'} for row in x['roots']]
    assert logical(summaries['P1']) == logical(summaries['P2']) and len(summaries['P2']['roots']) == 10
    for host in ('P1', 'P2'):
        task = json.loads((HERE / f'runtime-evidence/runtime-{host}-MCP_TASK.json').read_text())
        assert task['status'] == 'succeeded' and task['exit_code'] == 0
    rows_context = metadata(HERE, plan, 'rows15')[1]['context']
    assert rows_context['runtime'] == context['runtime']
    assert rows_context['suppliers'] == context['suppliers']
    for key, value in rows_context['environment'].items():
        if key != 'LEAN_PATH':
            assert value == context['environment'][key]

    return {'schema': 'cell05_genuine_local_metadata_contract_review_v1',
        'status': 'PASS_REAL_LOCAL_METADATA_AND_BASELINE_NOT_FULL_FIELDS_RECEIPT_ACCEPTANCE',
        'original_plan': fp(HERE / 'SUPPLIER_PLAN.json'),
        'original_run': spec['run'], 'original_success': spec['success'],
        'original_archive': spec['archive'], 'original_export_manifest': spec['export_manifest'],
        'frozen_paths_bound_to_exact_export_or_external_pins': len(frozen),
        'external_original_path_roles': len(external),
        'ordered_accepted_seal_pins': 219,
        'declared_step_artifact_paths': len(expected_step_paths),
        'real_local_baseline_files_rehashed': len(baseline_pins), 'baseline': baseline,
        'all_original_73_field_sources_rehashed': True,
        'current_runtime_summary_roots_equal': 10,
        'historical_runtime_inventory_retroactively_claimed': False,
        'three_actual_metadata_mode_samples': first,
        'missing_local_fields_receipt_bodies_fabricated': False,
        'complete_fields73_receipt_body_validation_executed': False,
        'P2_full_runtime_snapshot_or_current_cloud_objects_accessed': False,
        'Lean_commands': 0}


if __name__ == '__main__':
    print(json.dumps(main(), indent=2))
