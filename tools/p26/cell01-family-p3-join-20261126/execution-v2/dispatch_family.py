#!/usr/bin/env python3
"""Run the exact new eleven-owner family after the actual all-join preflight."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
PACKAGE = Path('/workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-preparation-v3')
CONTROL = Path('/workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-execution-v2')
INPUTS = Path('/workspace/p26-cell01-family-p3-inputs-557a12f3bcd7')
STAGE = Path('/workspace/p26-cell01-family-p3-stage-557a12f3bcd7')
PILOT = 'family11-interface-pilot-v2'
COMPLETE = 'family11-complete-v2'
MANIFEST = {'bytes': 11935, 'sha256': '2e5595cbea2c0de2df6724535bdb32b3557b46a50de012206669cd9c468c0f95'}
CONFIG = {'bytes': 3325, 'sha256': '60d612998b468f878904dfa557e0059af9f7d76102830296040cd99045c39388'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def canonical(path):
    path = Path(path)
    need(path.is_absolute() and '..' not in path.parts and not path.is_symlink()
         and path.resolve() == path, 'Noncanonical execution path')
    return path


def pin(path, expected=None):
    path = canonical(path)
    need(path.is_file(), 'Missing regular execution input: ' + str(path))
    digest, size = hashlib.sha256(), 0
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
            size += len(block)
    actual = {'path': str(path), 'bytes': size, 'sha256': digest.hexdigest()}
    if expected is not None:
        need(all(actual[k] == expected[k] for k in ('bytes', 'sha256')), 'Execution input pin differs: ' + str(path))
    return actual


def read(path):
    return json.loads(canonical(path).read_text())


def write(name, value):
    path = canonical(CONTROL / name)
    need(path.parent == CONTROL, 'Unexpected dispatcher metadata path')
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')
    return pin(path)


def checked_package():
    manifest_ref = pin(PACKAGE / 'PREPARATION_PACKAGE_MANIFEST.json', MANIFEST)
    manifest = read(manifest_ref['path'])
    need(manifest['destination'] == str(PACKAGE) and manifest['Lean_commands'] == 0
         and manifest['supplier_objects_included'] is False
         and manifest['row001_historical_bodies_included'] is False,
         'Unexpected preparation package scope')
    expected = {row['member']: row for row in manifest['files']}
    need(len(expected) == len(manifest['files']) == 58, 'Preparation payload count differs')
    refs = [manifest_ref]
    for name, expected_pin in expected.items():
        path = canonical(PACKAGE / name)
        need(path.is_relative_to(PACKAGE), 'Preparation member escapes package')
        refs.append(pin(path, expected_pin))
    actual = set()
    for path in PACKAGE.rglob('*'):
        canonical(path)
        if path.is_file():
            actual.add(path.relative_to(PACKAGE).as_posix())
    need(actual == set(expected) | {'PREPARATION_PACKAGE_MANIFEST.json'}, 'Preparation package has extra or missing files')
    return refs


def require_preflight(summary, targets):
    need(summary['schema'] == 'p26_family_p3_existing_suppliers_preflight_v1'
         and summary['status'] == 'PASS_ALL_ELEVEN_EXISTING_SUPPLIER_JOINS_NO_PROOFS'
         and summary['supplier_union'] == 791 and summary['new_owner_count'] == 11
         and summary['expected_later_new_steps'] == 33
         and summary['Lean_commands'] == summary['supplier_proof_commands'] == summary['new_proof_credit'] == 0
         and summary['row001_bodies_exported'] is False and summary['P2_6_complete_claimed'] is False
         and summary['future_stage'] == str(STAGE) and summary['later_rss_gib'] == 12
         and summary['external_provider_modules'] == 515
         and summary['existing_external_modules_reused'] == 505
         and summary['old_external_modules_transferred'] == 10,
         'Actual complete 791-supplier preflight PASS is required')
    checks = summary['owner_checks']
    need([row['module'] for row in checks] == targets
         and [row['old_suppliers'] for row in checks] == [625, 663, *([642] * 8), 791]
         and [row['full_project_closure'] for row in checks] == [626, 665, *([644] * 8), 802]
         and all(row['supplier_proof_commands'] == 0 for row in checks),
         'Preflight must cover every exact original owner closure')


def require_result(result, targets, complete):
    count = 33 if complete else 3
    expected = [(module, mode) for module in targets for mode in ('normal', 'kernel', 'owned')][:count]
    need(result['status'] == ('PASS_CELL01_ORIGINAL_FLOOR_FAMILY_11' if complete else 'PAUSED_ACCEPTED_PREFIX')
         and result['accepted_steps'] == count and result['accepted_owners'] == (11 if complete else 1)
         and result['new_proof_commands'] == (30 if complete else 3)
         and result['supplier_proof_commands'] == 0 and result['P2_6_complete_claimed'] is False
         and [(r['module'], r['mode']) for r in result['records']] == expected,
         'Frozen runner did not preserve the exact new-owner accepted prefix')
    need([row['reused'] for row in result['records']] == ([True] * 3 + [False] * 30 if complete else [False] * 3),
         'Pilot steps were recomputed or completion reuse differs')


def check_new_records(F, result, frozen):
    owned = 0
    for row in result['records']:
        ref = row['receipt']
        F.within(STAGE, ref['path'], True)
        frozen.add(ref['path'], ref)
        seal = F.read(ref['path'])
        need(seal['status'] == 'succeeded' and seal['module'] == row['module'] and seal['mode'] == row['mode'],
             'Accepted new-owner receipt differs from the result')
        anchor = STAGE / 'accepted' / F.stem(row['module']) / (row['mode'] + '.json')
        need(F.read(anchor) == {k: row[k] for k in ('module', 'mode', 'receipt')}, 'New-owner anchor differs')
        frozen.add(anchor)
        for object_ref in [seal['object'], *seal['object_sidecars']]:
            F.within(STAGE, object_ref['path'], True)
            frozen.add(object_ref['path'], object_ref)
        if row['mode'] == 'owned':
            owned += seal['owned_declaration_count']
    return owned


def run_phase(name, argv, frozen):
    frozen.check()
    write(name + '-STARTED.json', {'argv': argv, 'supplier_proof_commands': 0})
    print(json.dumps({'phase': name + '_started', 'argv': argv, 'supplier_proof_commands': 0}), flush=True)
    completed = subprocess.run(argv, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    write(name + '-PROCESS.json', {'exit_code': completed.returncode})
    need(completed.returncode == 0, 'Frozen runner stopped during ' + name + '; preserve all original evidence')
    frozen.check()


def main():
    need(canonical(Path(__file__).absolute()).parent == CONTROL, 'Wrong fixed dispatcher control root')
    for root in (PACKAGE, CONTROL, INPUTS, STAGE):
        canonical(root)
    need(not STAGE.exists(), 'EXISTING_PROOF_STAGE_REQUIRES_INSPECTION_NO_AUTOMATIC_RETRY')
    need(not (CONTROL / 'RUN.json').exists(), 'EXISTING_DISPATCH_REQUIRES_INSPECTION_NO_AUTOMATIC_RETRY')
    package_refs = checked_package()
    config_ref = pin(PACKAGE / 'INPUT_CONFIG.json', CONFIG)
    config = read(config_ref['path'])
    need(config['stage'] == str(STAGE) and config['output'] == str(INPUTS), 'Fixed stage/input roots differ')
    sys.path.insert(0, str(PACKAGE))
    from join_common import load_executor
    F = load_executor(PACKAGE / 'frozen-executor/family_run.py')
    for root in (PACKAGE, CONTROL, INPUTS):
        F.disjoint(STAGE, root)
    frozen = F.E.Frozen()
    for ref in [*package_refs, config_ref, pin(Path(__file__).absolute())]:
        frozen.add(ref['path'], ref)
    preflight_ref = frozen.add(INPUTS / 'PREFLIGHT.json')
    summary = F.read(preflight_ref['path'])
    targets = F.FAMILY_ORDER
    require_preflight(summary, targets)
    source_archive = Path(config['source_archive'])
    need(summary['source_archive'] == F.fp(source_archive) and F.same(summary['source_archive'], F.SOURCE_ARCHIVE),
         'Preflight names another source archive')
    runtime_ref = summary['runtime']
    need(runtime_ref['path'] == str(INPUTS / 'RUNTIME.json'), 'Unexpected runtime locator')
    frozen.add(runtime_ref['path'], runtime_ref)
    runtime = F.read(runtime_ref['path'])
    need(len(runtime['external_imports']) == len(set(runtime['external_imports'])) == 11517
         and len(runtime['external_modules']) == 11517
         and {row['module'] for row in runtime['external_modules']} == set(runtime['external_imports'])
         and runtime['mode'] == 'complete_tree', 'Incomplete 11517-module runtime boundary')
    external_root = config['runtime']['external_provider']['destination']
    need(summary['complete_external_provider'] == external_root
         and runtime['runtime_roots'] == summary['runtime_roots']
         and external_root in runtime['runtime_roots']
         and F.same(runtime['accepted_module_context'],
                    {'bytes': 12878196, 'sha256': 'b36a9153969abb3cbac96c3d74bea3e0c366ca3a673cdfe7456a7e655f2241c0'}),
         'Runtime does not bind the accepted context and complete external provider')
    frozen.add(runtime['accepted_module_context']['path'], runtime['accepted_module_context'])
    joins, supplier_union = [], set()
    need(len(summary['joins']) == 11, 'Missing preflight owner joins')
    for module, ref, check in zip(targets, summary['joins'], summary['owner_checks']):
        expected = INPUTS / 'joins' / (F.stem(module) + '.json')
        need(ref['path'] == str(expected), 'Join path/order differs')
        frozen.add(expected, ref)
        join = F.read(expected)
        names = [row['module'] for row in join['suppliers']]
        need(join['schema'] == 'p26_family_owner_join_v1' and join['module'] == module
             and 'accepted_owner' not in join
             and len(names) == len(set(names)) == check['old_suppliers']
             and set(join['external_imports']) == set(runtime['external_imports']), 'Wrong immutable owner join')
        supplier_union.update(names)
        joins.append(expected)
    need(len(supplier_union) == 791 and not supplier_union.intersection(targets), 'Wrong old-supplier union')
    write('RUN.json', {'schema': 'p26_cell01_family11_dispatch_v1', 'preflight': preflight_ref,
                      'runtime': runtime_ref, 'joins': summary['joins'], 'source_archive': summary['source_archive'],
                      'package_manifest': package_refs[0], 'dispatcher': pin(Path(__file__).absolute()),
                      'new_owner_scope': targets, 'rss_gib': 12, 'supplier_proof_commands': 0,
                      'input_files': [frozen.files[p] for p in sorted(frozen.files)]})
    common = [sys.executable, '-B', str(PACKAGE / 'frozen-executor/family_run.py'),
              '--stage', str(STAGE), '--source-root', config['source_root'],
              '--source-archive', str(source_archive), '--runtime', runtime_ref['path'],
              '--rss-gib', '12', '--wall-seconds', '1800']
    # The first phase requests only the independent interface. All eleven joins
    # were checked above; the complete phase uses the same fixed files.
    run_phase('pilot', common + ['--join', str(joins[0]), '--attempt', PILOT, '--max-new-steps', '3'], frozen)
    pilot_ref = frozen.add(STAGE / 'attempts' / PILOT / 'RESULT.json')
    pilot = F.read(pilot_ref['path'])
    require_result(pilot, targets, False)
    check_new_records(F, pilot, frozen)
    write('PILOT_ACCEPTED.json', {'result': pilot_ref, 'accepted_steps': 3, 'accepted_owners': 1,
                                'new_proof_commands': 3, 'supplier_proof_commands': 0})
    print(json.dumps({'phase': 'pilot_accepted', 'accepted_steps': 3, 'accepted_owners': 1,
                      'supplier_proof_commands': 0}), flush=True)
    join_args = [part for path in joins for part in ('--join', str(path))]
    run_phase('complete', common + join_args + ['--attempt', COMPLETE, '--max-new-steps', '30'], frozen)
    result_ref = frozen.add(STAGE / 'attempts' / COMPLETE / 'RESULT.json')
    result = F.read(result_ref['path'])
    require_result(result, targets, True)
    owned = check_new_records(F, result, frozen)
    need(result['records'][:3] == [{**row, 'reused': True} for row in pilot['records']],
         'Completion replaced an original pilot receipt')
    evidence = result['evidence']
    need(evidence['archive_readback'] == 'EXACT_REGULAR_UNIQUE_INVENTORY_SIZE_SHA256_VERIFIED'
         and evidence['archive']['path'] == str(STAGE / 'evidence' / (COMPLETE + '.tar.xz')),
         'Frozen exporter did not produce the expected exact archive')
    frozen.add(evidence['archive']['path'], evidence['archive'])
    with tarfile.open(evidence['archive']['path'], 'r:xz') as stream:
        manifest = json.load(stream.extractfile('MANIFEST.json'))
    need(manifest['schema'] == 'p26_cell01_family_11_evidence_v1' and manifest['new_owners'] == targets
         and manifest['accepted_steps'] == 33 and manifest['supplier_proof_commands'] == 0
         and manifest['old_supplier_bodies_included'] is False
         and manifest['row001_receipt_bodies_included'] is False and manifest['P2_6_complete_claimed'] is False,
         'New-owner export scope differs')
    frozen.check()
    final = {'status': 'PASS_ELEVEN_NEW_CELL01_OWNERS_AND_EXACT_EXPORT', 'result': result_ref,
             'accepted_owners': 11, 'accepted_steps': 33, 'owned_declarations': owned,
             'pilot_steps_reused': 3, 'new_proof_commands': 33, 'supplier_proof_commands': 0,
             'evidence': evidence, 'row001_receipt_bodies_exported': False,
             'archive_automatically_transferred': False, 'P2_6_complete_claimed': False}
    write('SUCCESS.json', final)
    print(json.dumps(final, sort_keys=True), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        stopped = {'status': 'DISPATCH_STOPPED_PRESERVE_ORIGINAL_EVIDENCE',
                   'error': type(error).__name__ + ': ' + str(error), 'automatic_retry': False,
                   'supplier_proof_commands': 0, 'P2_6_complete_claimed': False}
        if canonical(CONTROL).is_dir() and not (CONTROL / 'STOPPED.json').exists():
            write('STOPPED.json', stopped)
        print(json.dumps(stopped), file=sys.stderr, flush=True)
        raise
