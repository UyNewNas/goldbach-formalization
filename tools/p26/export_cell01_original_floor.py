#!/usr/bin/env python3
"""Read-only export of the accepted Cell01 row000 original-floor bridge.

Verify three new proof chains and preserve all 71 reused proof chains. Existing
supplier objects are rehashed against the accepted snapshot, never archived or
rebuilt. No Lean process, Git write, or status-file modification occurs.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
import tarfile

TARGET = 'ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge'
DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/cell01-row000-original-floor')
DEFAULT_ATTEMPT = '20261126T045413255133Z-03f42f40'
DRIVER_SHA = 'e325a2101f75cb6c21a96d9d9914b1e33e10082651d65475e050025ae68ff258'
REGISTRY_SHA = '7ed4fc67248825e55eeb921eb80a3bf7ae0bac141471763bfaa1edd89eadc867'
EXPECTED_RECEIPTS = {
    'normal': 'd88039d7f4a172f8e667cfd3949cd43e2b10fed0715a9b64aeddaacc98511587',
    'kernel': 'a2832fe6eea2341d9730f575e2d960e58a6002ca16cf931abaf34526c19e2b42',
    'owned': 'f68930a9f23cbeebb348032ae75d4f2a1c0c5701d62bbc2867a7ed05b1de2354'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def fingerprint(path):
    digest, size = hashlib.sha256(), 0
    with Path(path).open('rb') as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b''):
            digest.update(chunk)
            size += len(chunk)
    return {'bytes': size, 'sha256': digest.hexdigest()}


def same(a, b):
    return all(a.get(key) == b.get(key) and key in a and key in b for key in ('bytes', 'sha256'))


def read(path):
    return json.loads(Path(path).read_text())


def object_body(path):
    return str(path).endswith(('.olean', '.olean.server', '.olean.private', '.ir'))


class Collector:
    def __init__(self, stage):
        self.stage, self.files = stage, {}

    def add(self, path, role, expected=None, member=None, original_path=None):
        path = Path(path).absolute()
        need(path.is_file() and path.resolve() == path, f'Missing or symlinked evidence: {path}')
        need(path.is_relative_to(self.stage.parent), f'Evidence escapes continuation stages: {path}')
        member = member or path.relative_to(self.stage).as_posix()
        need(member and not Path(member).is_absolute() and '..' not in Path(member).parts,
             'Unsafe archive member')
        pin = fingerprint(path)
        need(expected is None or same(pin, expected), f'Evidence fingerprint differs: {path}')
        row = self.files.setdefault(member, {'path': str(path), 'archive_member': member,
                                            **pin, 'roles': []})
        need(row['path'] == str(path) and same(row, pin), 'Conflicting evidence member')
        if role not in row['roles']:
            row['roles'].append(role)
        if original_path is not None:
            need(row.get('recorded_original_path', original_path) == original_path,
                 'Conflicting original evidence path')
            row['recorded_original_path'] = original_path
        return {'archive_member': member, **pin}

    def pin(self, reference, role):
        return self.add(reference['path'], role, reference)

    def json_pin(self, reference, role):
        self.pin(reference, role)
        return read(reference['path'])

    def tree(self, directory, role):
        for path in sorted(Path(directory).rglob('*')):
            if path.is_file():
                self.add(path, role)

    def prior_export(self, export, label):
        prefix = 'prior-evidence/' + label + '/'
        manifest_ref = self.add(export.manifest_pin['path'], 'prior_export_manifest', export.manifest_pin,
                                prefix + 'EXPORT_MANIFEST.json')
        omitted = []
        for member, row in export.by_member.items():
            if object_body(member):
                omitted.append({'archive_member_in_prior_export': member,
                    'bytes': row['bytes'], 'sha256': row['sha256'], 'recorded_original_path': row['path']})
                continue
            self.add(export.root / member, 'preserved_prior_evidence', row, prefix + member, row['path'])
        return {'manifest': manifest_ref, 'member_prefix': prefix, 'omitted_supplier_object_bodies': omitted}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--attempt', default=DEFAULT_ATTEMPT)
    ap.add_argument('--archive', type=Path)
    ap.add_argument('--manifest', type=Path)
    ap.add_argument('--task-metadata', type=Path)
    args = ap.parse_args()
    stage = args.stage.resolve()
    attempt = stage / 'attempts' / args.attempt
    need(args.attempt == DEFAULT_ATTEMPT and attempt.resolve().parent == stage / 'attempts',
         'Unexpected accepted attempt')
    archive_path = args.archive or stage.parent / 'cell01-row000-original-floor-completed-evidence.tar.xz'
    manifest_path = args.manifest or stage.parent / 'cell01-row000-original-floor-completed-manifest.json'
    need(not archive_path.exists() and not manifest_path.exists(), 'Refusing to replace an earlier export')
    collector = Collector(stage)
    result_path = attempt / 'RESULT.json'
    result = read(result_path)
    need(result['status'] == 'PASS_CELL01_ROW000_ORIGINAL_FLOOR' and result['module'] == TARGET and
         result['new_proof_commands'] == 3 and result['supplier_proof_commands'] == 0 and
         result['cell01_row'] == 0 and result['remaining_cell01_rows_outside_this_owner'] == 143 and
         not result['P2_6_complete_claimed'], 'Accepted result boundary differs')
    collector.add(result_path, 'accepted_result')
    run = collector.json_pin(result['context'], 'accepted_runtime_context')
    need(run['attempt'] == args.attempt and run['stage'] == str(stage) and run['target'] == TARGET and
         run['project'] == str(attempt / 'project') and run['canonical_project_suppliers'] == 1111,
         'Accepted runtime paths/count differ')
    need(run['driver']['sha256'] == DRIVER_SHA and run['registry']['sha256'] == REGISTRY_SHA,
         'Unexpected accepted driver or registry')
    collector.pin(run['driver'], 'accepted_driver')
    registry = collector.json_pin(run['registry'], 'accepted_registry')
    spec = importlib.util.spec_from_file_location('accepted_row000_driver', run['driver']['path'])
    driver = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(driver)
    shared = driver.load_helper(stage / 'Cell00OriginalFloor_continue.py', registry['shared_driver'], 'accepted_shared')
    owned_helper = driver.load_helper(stage / 'export_cell01_row000.py', registry['owned_parser'], 'accepted_owned_parser')
    for name, key in [('Cell00OriginalFloor_continue.py', 'shared_driver'),
                      ('export_cell01_row000.py', 'owned_parser'),
                      ('Cell00OriginalFloor_EXTERNAL_PINS.json', 'external_pins')]:
        collector.add(stage / name, 'accepted_helper_or_runtime_pins', registry[key])
    need(shared.LEAN_COMMIT in run['lean_version'] and
         run['package_revisions'] == {'mathlib': shared.MATHLIB_COMMIT, **shared.EXTERNAL_COMMITS},
         'Accepted toolchain/package pins differ')
    need(run['LEAN_PATH'].split(':')[0] == str(attempt / 'objects') and
         not run['old_supplier_normal_recompilation'] and not run['old_supplier_kernel_replay'] and
         not run['cloud_lean_source_generation'], 'Accepted execution boundary differs')
    inputs = collector.json_pin(run['inputs'], 'complete_input_and_namespace_snapshot')
    frozen = driver.Frozen(shared)
    snapshot = {row['path']: row for row in inputs['files']}
    need(len(snapshot) == len(inputs['files']), 'Duplicate frozen input path')
    for row in inputs['files']:
        frozen.add(row['path'], row, row['root'])
    namespace = inputs['canonical_modules']
    need(len(namespace) == 1111 and TARGET not in namespace and
         not any(name.endswith(('ArchiveCore', 'ArchivePackedInputs')) for name in namespace),
         'Unexpected canonical supplier inventory')
    union = {row['module']: row for row in inputs['project_object_union'] if row['path'].endswith('.olean')}
    need(len(union) == 1111 and set(union) == set(namespace), 'Incomplete single-namespace object union')
    for module, row in namespace.items():
        for key in ('source', 'object'):
            need(same(snapshot[row[key]['path']], row[key]), 'Canonical supplier absent from frozen snapshot')
        need(same(union[module], row['object']) and union[module]['origin'] == row['object']['path'],
             'Canonical object union differs')
    for row in inputs['project_object_union']:
        need(same(snapshot[row['path']], row), 'Staged object/sidecar absent from input snapshot')
    need(len(inputs['external_modules']) == 515 and inputs['P3_proof_steps_reused'] == 66 and
         inputs['P3_owned_declarations_reused'] == 313, 'Accepted external/prior-proof boundary differs')

    p1_root = Path(registry['supplier_stages']['cell00'])
    p3_root = Path(registry['supplier_stages']['p3_completed'])
    p1 = driver.AcceptedExport(p1_root, stage / 'CELL00_ORIGINAL_FLOOR_EXPORT_MANIFEST.json',
                               registry['p1_export_manifest'], frozen)
    p3 = driver.AcceptedExport(p3_root, p3_root / 'CELL01_ROW000_EXPORT_MANIFEST.json',
                               registry['p3_export_manifest'], frozen)
    p1_verified = driver.verify_p1_suppliers(p1)
    p3_verified = driver.verify_p3(p3, owned_helper)
    need(len(p1_verified['records']) == 5 and p3_verified['proof_steps'] == 66,
         'Expected all 71 prior accepted proof chains')
    for row in p3_verified['supplier_rows']:
        need(same(namespace[row['module']]['source'], row['source']) and
             same(namespace[row['module']]['object'], row['object']), 'P3 supplier byte context differs')
    for row in p1_verified['records']:
        need(same(namespace[row['module']]['source'], row['source']) and
             same(namespace[row['module']]['object'], row['object']), 'P1 supplier byte context differs')
    old_evidence = {'P1_cell00': collector.prior_export(p1, 'P1-cell00'),
                    'P3_row000': collector.prior_export(p3, 'P3-row000')}
    prior_chains = []
    for module, owner in p3.manifest['owners'].items():
        for mode, ref in owner['steps'].items():
            prior_chains.append({'module': module, 'mode': mode,
                'receipt': {'archive_member': old_evidence['P3_row000']['member_prefix'] + ref['archive_member'],
                            'bytes': ref['bytes'], 'sha256': ref['sha256']},
                'source': owner['source'], 'object': owner['object'], 'provider': 'P3_row000'})
    for row in p1_verified['records']:
        relative = Path(row['receipt']['path']).relative_to(p1_root).as_posix()
        prior_chains.append({'module': row['module'], 'mode': row['mode'],
            'receipt': {'archive_member': old_evidence['P1_cell00']['member_prefix'] + relative,
                        'bytes': row['receipt']['bytes'], 'sha256': row['receipt']['sha256']},
            'source': row['source'], 'object': row['object'], 'provider': 'P1_cell00'})
    need(len(prior_chains) == 71, 'Prior chain index is incomplete')
    addendum = collector.add(stage / 'SUPPLIER_KERNEL_COMPLETION.json', 'same_byte_kernel_completion_addendum',
                             registry['supplier_kernel_completion'])
    for name, key in [('GEOMETRY01_ACCEPTED_PINNED_CLOSURE.json', 'geometry_pins'),
                      ('Moment01_SUPPLIERS.json', 'moment_manifest')]:
        collector.add(stage / name, 'accepted_supplier_pin_manifest', registry[key])
    original_geometry = registry['geometry_original_input']
    collector.add(Path(registry['supplier_stages']['geometry01']) / original_geometry['archive_member'],
                  'original_geometry01_literal_input', original_geometry,
                  'literal-inputs/' + Path(original_geometry['archive_member']).name)
    original_moment = read(stage / 'Moment01_SUPPLIERS.json')['original_input']
    collector.add(Path(registry['supplier_stages']['moment01']) / original_moment['archive_member'],
                  'original_moment01_literal_input', original_moment,
                  'literal-inputs/' + Path(original_moment['archive_member']).name)

    target = registry['target']
    need(target['module'] == TARGET and len(result['records']) == 3, 'Wrong new owner inventory')
    owner, duration = {'module': TARGET, 'steps': {}}, 0.0
    for mode, record in zip(('normal', 'kernel', 'owned'), result['records']):
        need(record['module'] == TARGET and record['mode'] == mode and
             record['receipt']['sha256'] == EXPECTED_RECEIPTS[mode], 'Unexpected new accepted receipt')
        accepted = collector.json_pin(record['receipt'], 'accepted_' + mode + '_receipt')
        need(accepted['module'] == TARGET and accepted['mode'] == mode and accepted['status'] == 'succeeded' and
             accepted['all_frozen_inputs_unchanged'] and accepted['context'] == result['context'],
             'New proof receipt/context differs')
        source = collector.pin(accepted['source'], 'accepted_new_source')
        obj = collector.pin(accepted['object'], 'accepted_new_object')
        need(same(source, target['source']) and same(accepted['source'], result['source']) and
             same(accepted['object'], result['object']), 'New source/object changed across phases')
        need(accepted['source']['path'] == str(attempt / 'project' / shared.module_path(TARGET, '.lean')) and
             accepted['object']['path'] == str(attempt / 'objects' / shared.module_path(TARGET, '.olean')),
             'New owner outside its isolated namespace')
        command_result = collector.json_pin(accepted['command_result'], 'accepted_' + mode + '_result')
        command = collector.json_pin(command_result['command'], 'accepted_' + mode + '_command')
        need(command_result['status'] == 'succeeded' and command_result['exit_code'] == 0 and
             command_result['error'] is None and not command_result['timed_out'] and
             all(command_result.get(key) == value for key, value in command.items()), 'New command chain differs')
        need(command_result['source'] == accepted['source'] and command_result['module'] == TARGET and
             command_result['mode'] == mode and command_result['input_fingerprints'] == run['inputs'] and
             command_result['LEAN_PATH'] == run['LEAN_PATH'] and command_result['cwd'] == run['project'] and
             command_result['log'] == accepted['log'], 'New proof command bindings differ')
        log = collector.pin(accepted['log'], 'accepted_' + mode + '_log')
        argv = command_result['argv']
        if mode == 'normal':
            need(command_result['object_before'] is None and argv[0] == run['lean_binary']['path'] and
                 argv[-3:] == ['-o', accepted['object']['path'], str(shared.module_path(TARGET, '.lean'))],
                 'New normal command target/output differs')
        else:
            need(command_result['object_before'] == accepted['object'], 'Checked new object changed')
            if mode == 'kernel':
                need(argv == [run['leanchecker_binary']['path'], '--verbose', TARGET],
                     'New kernel command is not independent replay')
            else:
                audit = collector.pin(accepted['audit_source'], 'fixed_complete_owned_audit')
                need(same(audit, target['audit']) and command_result['audit_source'] == accepted['audit_source'] and
                     argv[0] == run['lean_binary']['path'] and argv[-1] == accepted['audit_source']['path'],
                     'Owned audit command/source differs')
                parsed = owned_helper.parse_owned(Path(accepted['log']['path']).read_text(), TARGET)
                owned = collector.json_pin(accepted['owned_declarations'], 'complete_new_owned_inventory')
                need(parsed == owned and parsed['owned_declaration_count'] == accepted['owned_declaration_count'] and
                     parsed['axioms_union'] == accepted['axioms_union'], 'New complete owned inventory differs')
                owner.update({'audit': audit, 'owned_declarations': collector.pin(accepted['owned_declarations'],
                    'complete_new_owned_inventory'), 'owned_declaration_count': parsed['owned_declaration_count'],
                    'axioms_union': parsed['axioms_union']})
        sidecars = [collector.pin(ref, 'new_object_sidecar') for ref in accepted['object_sidecars']]
        owner.update({'source': source, 'object': obj, 'object_sidecars': sidecars})
        owner['steps'][mode] = collector.pin(record['receipt'], 'new_owner_' + mode + '_receipt')
        duration += command_result['finished_unix'] - command_result['started_unix']
    collector.tree(attempt / 'runtime', 'successful_runtime_pin_commands')
    collector.add(Path(__file__), 'read_only_exporter')
    metadata_path = args.task_metadata or stage / 'P1_TASK_EXPORT_OBSERVATION.json'
    task = read(metadata_path)
    need(task['task_id'] == 'job_92789d0200b843e5877899a14738a10e' and
         task['status'] == 'succeeded' and task['exit_code'] == 0, 'Unexpected MCP success metadata')
    task_ref = collector.add(metadata_path, 'MCP_task_observation')
    new_object_members = {owner['object']['archive_member'],
                          *[ref['archive_member'] for ref in owner['object_sidecars']]}
    need({name for name in collector.files if object_body(name)} == new_object_members,
         'An old supplier object entered the export')
    frozen.unchanged()
    report = {'schema': 'p26_cell01_row000_original_floor_completed_export_v1',
        'status': 'PASS_CELL01_ROW000_ORIGINAL_FLOOR', 'stage': str(stage), 'successful_attempt': args.attempt,
        'owner': owner, 'accepted_new_owners': 1, 'accepted_new_proof_commands': 3,
        'normal': 1, 'kernel': 1, 'owned_audit': 1, 'owned_declarations': owner['owned_declaration_count'],
        'summed_proof_command_seconds': duration, 'MCP_task_metadata': task_ref,
        'MCP_runtime_seconds': task['runtime_seconds'], 'MCP_memory_peak_bytes': task['memory_peak_bytes'],
        'MCP_memory_peak_source': task['memory_peak_source'], 'MCP_cpu_time_seconds': task['cpu_time_seconds'],
        'MCP_cpu_time_source': task['cpu_time_source'], 'prior_evidence': old_evidence,
        'prior_accepted_proof_chains': prior_chains, 'prior_accepted_proof_chain_count': 71,
        'prior_owned_declarations': p3_verified['owned_declarations'] + p1_verified['prefix']['owned_declaration_count'],
        'supplier_kernel_completion': addendum,
        'supplier_boundary': {'canonical_project_modules': 1111, 'P3_original_suppliers_matched': 398,
            'external_modules': 515, 'supplier_object_bodies_included': False,
            'supplier_objects_rehashed_by_exporter': True, 'supplier_proof_commands': 0,
            'full_supplier_kernel_closed_at_original_P3_run': False,
            'historical_P3_records_unchanged': True, 'same_byte_P1_kernel_addendum_retained': True},
        'cell01_rows_in_this_owner': [0], 'remaining_cell01_rows_outside_this_owner': 143,
        'Lean_invoked_by_exporter': False, 'P2_6_complete_claimed': False,
        'files': [collector.files[name] for name in sorted(collector.files)]}
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    with manifest_path.open('x') as output:
        output.write(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    with archive_path.open('xb') as raw:
        with tarfile.open(fileobj=raw, mode='w:xz', dereference=True) as archive:
            for row in report['files']:
                path = Path(row['path'])
                need(same(fingerprint(path), row), 'Evidence changed before export')
                info = archive.gettarinfo(str(path), arcname=row['archive_member'])
                need(info.isreg(), 'Only regular-file archive members are allowed')
                with path.open('rb') as source:
                    archive.addfile(info, source)
            info = archive.gettarinfo(str(manifest_path), arcname='CELL01_ORIGINAL_FLOOR_EXPORT_MANIFEST.json')
            with manifest_path.open('rb') as source:
                archive.addfile(info, source)
    print(json.dumps({'archive': {'path': str(archive_path), **fingerprint(archive_path)},
        'manifest': {'path': str(manifest_path), **fingerprint(manifest_path)},
        'exported_files': len(report['files']), 'accepted_new_owners': 1,
        'accepted_new_proof_commands': 3, 'owned_declarations': owner['owned_declaration_count'],
        'prior_accepted_proof_chains': 71, 'supplier_object_bodies_included': False,
        'Lean_invoked_by_exporter': False}), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(f'EXPORT_FAILED: {type(error).__name__}: {error}', file=sys.stderr)
        raise SystemExit(1)
