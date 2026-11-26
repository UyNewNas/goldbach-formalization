#!/usr/bin/env python3
"""Read the published receipt capsule. This module never starts Lean."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import sys

sys.dont_write_bytecode = True
from receipt_support import parse_owned


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def same(a, b):
    return all(a.get(key) == b.get(key) for key in ('bytes', 'sha256'))


def verify_baseline(here):
    here = Path(here)
    registry = json.loads((here / 'SUPPLIER_REGISTRY.json').read_text())
    manifest = json.loads((here / 'BASELINE_EVIDENCE.json').read_text())
    files = {}
    for row in manifest['members']:
        rel = PurePosixPath(row['relative_path'])
        assert not rel.is_absolute() and '..' not in rel.parts and rel.parts[0] == 'baseline'
        assert row['relative_path'] not in files
        data = (here / rel).read_bytes()
        assert same(pin(data), row), row['relative_path']
        files[row['relative_path']] = data
    assert len(files) == manifest['capsule_members'] == 154

    def raw(family, member):
        return files['baseline/' + family + '/' + member]

    def read(family, member):
        return json.loads(raw(family, member))

    export = read('pilot', 'ACCEPTED_EXPORT_MANIFEST.json')
    main_members = {row['member']: row for row in export['members']}
    assert len(main_members) == 111
    success = read('pilot', export['success_member'])
    run_member = str(PurePosixPath(export['success_member']).with_name('RUN.json'))
    run = read('pilot', run_member)
    assert all(success.get(key) == value for key, value in run.items())
    assert success['status'] == 'succeeded' and success['accepted_targets'] == 6
    assert success['frozen_inputs_unchanged'] and not success['suppliers_recompiled']
    assert not success['whole_geometry_decoded'] and not success['P2_6_complete']
    stage = PurePosixPath(run['stage'])
    supplied = {row['module']: row for row in registry['suppliers']}
    old_targets = set(registry['accepted_old_owners'])
    assert len(supplied) == 15 and len(old_targets) == 6

    def pilot_file(identity):
        member = str(PurePosixPath(identity['path']).relative_to(stage))
        assert same(identity, main_members[member]), member
        data = raw('pilot', member)
        assert same(pin(data), identity), member
        return data

    seen, total_owned = set(), 0
    objects = {}
    for record in success['records']:
        result = json.loads(pilot_file(record.get('receipt') or record['reused_successful_receipt']))
        module, mode = result['module'], result['mode']
        key = (module, mode)
        assert module in old_targets and mode in ('normal', 'kernel', 'owned') and key not in seen
        seen.add(key)
        assert result['status'] == 'succeeded' and result['exit_code'] == 0
        assert all(result.get(k) == v for k, v in run.items())
        record_path = PurePosixPath((record.get('receipt') or record['reused_successful_receipt'])['path'])
        cmd_member = str(record_path.with_name(mode + '-command.json').relative_to(stage))
        command = read('pilot', cmd_member)
        assert all(result.get(k) == v for k, v in command.items())
        expected_source = str(stage / 'project' / (module.replace('.', '/') + '.lean'))
        expected_object = str(stage / 'objects' / (module.replace('.', '/') + '.olean'))
        assert result['source']['path'] == expected_source and result['object']['path'] == expected_object
        assert same(result['source'], supplied[module]['source'])
        assert same(result['object'], supplied[module]['object'])
        objects.setdefault(module, result['object'])
        assert result['object'] == objects[module]
        log = pilot_file(result['log']).decode()
        binary = result['argv'][0]
        common = [str(PurePosixPath(binary).with_name('lean')), '-j1',
                  f'-M{run["rss_limit_bytes"] // 1024**2}', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=0']
        if mode == 'normal':
            assert result['object_before'] is None
            assert result['argv'] == common + ['-o', expected_object, module.replace('.', '/') + '.lean']
        elif mode == 'kernel':
            assert result['object_before'] == result['object']
            assert result['argv'] == [str(PurePosixPath(binary).with_name('leanchecker')), '--verbose', module]
            assert log.strip() == 'replaying ' + module
        else:
            assert result['object_before'] == result['object']
            audit = str(stage / 'tools/p26/scalable/owned-audits' / (module.split('.')[-1] + '.lean'))
            assert result['audit_source']['path'] == audit and result['argv'] == common + [audit]
            pilot_file(result['audit_source'])
            owned = json.loads(pilot_file(result['owned_declarations']))
            assert parse_owned(log, module) == owned
            assert owned['owned_declaration_count'] == result['owned_declaration_count']
            total_owned += owned['owned_declaration_count']
    assert seen == {(m, mode) for m in old_targets for mode in ('normal', 'kernel', 'owned')}
    assert total_owned == 2054
    before = read('raw05-context', 'BEFORE.json')
    assert before == read('raw05-context', 'AFTER.json')
    addon = read('raw05-context', 'RESULT.json')
    command = read('raw05-context', 'COMMAND.json')
    addon_manifest = read('raw05-context', 'EXPORT_MANIFEST.json')
    assert addon['status'] == addon_manifest['status'] == 'PASS_RAW05_KERNEL_IN_PILOT_CONTEXT'
    assert addon['exit_code'] == 0 and addon['frozen_sources_objects_sidecars_context_unchanged']
    assert addon['baseline_18_steps_and_archive_unchanged'] and not addon['historical_evidence_rewritten']
    assert addon['normal_commands'] == 0 and addon['kernel_commands'] == 1
    assert not addon['six_new_owners_replayed']
    for name, field in [('COMMAND.json', 'command'), ('kernel.log', 'log'), ('BEFORE.json', 'before'), ('AFTER.json', 'after')]:
        assert same(pin(raw('raw05-context', name)), addon[field])
    assert raw('raw05-context', 'RUN.json') == raw('pilot', run_member)
    assert command['complete_baseline_run'] == run
    assert command['cwd'] == run['cwd'] and command['LEAN_PATH'] == run['LEAN_PATH']
    target = 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05'
    assert command['argv'] == [before['leanchecker_binary']['path'], '--verbose', target]
    assert raw('raw05-context', 'kernel.log').decode().strip() == 'replaying ' + target
    assert registry['runtime_binaries'] == {k: before[k] for k in ('lean_binary', 'leanchecker_binary')}
    pairs = set()
    for group in before['nine_supplier_sources_objects_and_sidecars']:
        key = group['module'], group['kind']
        assert key not in pairs and key[1] in ('source', 'object') and len(group['files']) == 1
        pairs.add(key)
        assert same(group['files'][0], supplied[key[0]][key[1]])
    assert len(pairs) == 18 and len({m for m, _ in pairs}) == 9
    assert same(before['baseline_archive'], manifest['archives']['pilot'])
    assert same(addon_manifest['original_raw05_historical_archive'], manifest['archives']['raw05-history'])
    history = read('raw05-history', 'previous-p1-evidence/runs/attempt-00000/RESULT.json')
    assert history['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
    assert history['module'] == target and history['accepted_owners'] == history['normal_passed'] == [target]
    normal = read('raw05-history', 'previous-p1-evidence/normal/' + target + '/NORMAL_PASS.json')
    assert normal['module'] == target and normal['normal_command']['exit_code'] == 0
    outputs = normal['source_plus_five_outputs']
    assert same(outputs[target.replace('.', '/') + '.lean'], supplied[target]['source'])
    assert same(outputs['.lake/build/lib/lean/' + target.replace('.', '/') + '.olean'], supplied[target]['object'])
    raw_input = next(row for row in history['loader_inputs'] if row['family'] == 'geometry' and row['cell'] == 5)
    input_member = 'original-input/eighth-third-minorant-extension-20261009-a23-s23_low-05-cell.witness.json'
    assert same(pin(raw('raw05-history', input_member)), raw_input)
    assert raw_input['bytes'] == 201042
    return {'status': 'PASS_PUBLISHED_RECEIPTS_AND_CONTEXT_JOIN', 'capsule_members': 154,
            'accepted_old_steps': 18, 'accepted_old_owned_declarations': 2054,
            'supplier_count': 15, 'raw05_current_context_kernel_addendum_checked': True,
            'full_supplier_kernel_closed_in_combined_evidence': True,
            'original_pilot_closed_boolean_alone_is_insufficient': True,
            'old_Lean_commands_executed': 0}
