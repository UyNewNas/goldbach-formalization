#!/usr/bin/env python3
"""Export the completed Cell00 continuation and its exact backfill evidence.

Read-only with respect to sources, objects and receipts. No Lean invocation.
The 704-module supplier cache and external package caches are represented by
their precise pin manifests and snapshots, not copied into this small export.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tarfile


DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/cell00')
DEFAULT_ATTEMPT = '20261126T033929994898Z-c8ce14a3'
DEFAULT_BACKFILL = '20261126T033233770413Z-82b28550'
TARGETS = ('ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix',
           'ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge')
BACKFILL = ('ImbalancedChen.P2OriginalSaving19CharacterCore00',
            'ImbalancedChen.P2Winner9HomogeneousRecurrence')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


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
    return (isinstance(a, dict) and isinstance(b, dict) and
            all(key in a and key in b and a[key] == b[key]
                for key in ('bytes', 'sha256')))


def read(path):
    return json.loads(Path(path).read_text())


def parse_owned(text, module):
    buckets = {'INVENTORY': [], 'DECL': [], 'COMPLETE': []}
    for line in text.splitlines():
        for marker, values in buckets.items():
            prefix = 'P26_CELL00_AUDIT_' + marker + ' '
            if line.startswith(prefix):
                values.append(json.loads(line[len(prefix):]))
    need(len(buckets['INVENTORY']) == len(buckets['COMPLETE']) == 1,
         'Missing or duplicate owned inventory/completion')
    inventory, complete = buckets['INVENTORY'][0], buckets['COMPLETE'][0]
    names, declarations = inventory['names'], buckets['DECL']
    need(inventory['module'] == complete['module'] == module, 'Owned module mismatch')
    need(names and len(names) == len(set(names)), 'Empty or duplicate owned inventory')
    need(sorted(row['name'] for row in declarations) == sorted(names), 'Incomplete owned inventory')
    need(complete['count'] == len(names), 'Owned completion count mismatch')
    for row in declarations:
        need(row['module'] == module and row['type'] and '⋯' not in row['type'], 'Truncated owned type')
        need(not row['unsafe'] and not row['partial'] and not row['axiom'], 'Unsafe/partial/axiom owner')
        need(set(row['axioms']) <= ALLOWED, 'Forbidden owned transitive axiom')
    return {'module': module, 'count': len(names), 'inventory': inventory,
            'declarations': declarations,
            'axioms_union': sorted({ax for row in declarations for ax in row['axioms']})}


class Collector:
    def __init__(self, stage):
        self.stage, self.files, self.historical_resolutions = stage, {}, []

    def add(self, path, role, expected=None):
        path = Path(path).absolute()
        need(path.is_file() and path.resolve() == path, f'Missing or symlinked evidence: {path}')
        need(path.is_relative_to(self.stage), f'Evidence escapes stage: {path}')
        member = path.relative_to(self.stage).as_posix()
        need(member and '..' not in Path(member).parts, 'Unsafe archive member')
        pin = fingerprint(path)
        if expected is not None:
            need(same(pin, expected), f'Fingerprint mismatch: {path}')
        row = self.files.setdefault(member, {'path': str(path), 'archive_member': member,
                                             **pin, 'roles': []})
        need(same(row, pin), f'Evidence changed while collecting: {path}')
        if role not in row['roles']:
            row['roles'].append(role)
        return {'archive_member': member, **pin}

    def pin(self, reference, role, historical=False):
        path = Path(reference['path'])
        if historical and (not path.is_file() or not same(fingerprint(path), reference)):
            revision = self.stage / 'revisions/verifier-v2-before-namespace-repair'
            matches = [p for p in revision.rglob(path.name)
                       if p.is_file() and same(fingerprint(p), reference)]
            need(len(matches) == 1, f'No unique frozen historical version: {path}')
            actual = matches[0]
            self.historical_resolutions.append({'recorded_path': str(path),
                'exported_archive_member': actual.relative_to(self.stage).as_posix(),
                'sha256': reference['sha256']})
            path = actual
        return self.add(path, role, reference)

    def json_pin(self, reference, role, historical=False):
        pin = self.pin(reference, role, historical)
        return read(self.stage / pin['archive_member'])

    def tree(self, directory, role):
        directory = Path(directory)
        if directory.exists():
            for path in sorted(directory.rglob('*')):
                if path.is_file():
                    self.add(path, role)


def supplier_boundary(stage, run, verifier, inputs, union, collector):
    manifest = collector.json_pin({**verifier['cell00_manifest'], 'path': str(stage / 'MANIFEST.json')},
                                  'supplier_pin_manifest')
    analytic = collector.json_pin({**verifier['analytic_pins'],
        'path': str(stage / 'HIGHER_MOMENTS_PINNED_CLOSURE.json')}, 'analytic_pin_manifest')
    freeze = collector.json_pin(run['analytic_freeze'], 'analytic_freeze')
    external = collector.json_pin(run['external_source_pins'], 'external_source_pins')
    need(manifest['project_modules'] == 480, 'Cell00 supplier count differs')
    need(sorted(manifest['normal_only_modules']) == sorted(BACKFILL), 'Wrong backfill boundary')
    need(analytic['module_count'] == len(analytic['rows']) == 224, 'Analytic supplier count differs')
    need(freeze['status'] == 'exact_accepted_suppliers_frozen' and
         freeze['analytic_modules'] == len(freeze['analytic_rows']) == 224, 'Invalid analytic freeze')
    need(freeze['pins_sha256'] == verifier['analytic_pins']['sha256'] and
         freeze['cell00_manifest_sha256'] == verifier['cell00_manifest']['sha256'], 'Freeze pin mismatch')
    need(freeze['proof_sources_generated'] is False and freeze['accepted_modules_recompiled'] is False,
         'Supplier generation/recompilation boundary changed')
    object_pins, source_pins = {}, {}
    for row in manifest['files']:
        if row['role'] in ('project_source', 'project_object'):
            target = source_pins if row['role'] == 'project_source' else object_pins
            need(row['module'] not in target, 'Duplicate supplier pin')
            target[row['module']] = {'path': str(stage / row['archive_path']), **fingerprint_fields(row)}
    need(len(source_pins) == len(object_pins) == 480, 'Incomplete Cell00 source/object pins')
    frozen_analytic = {row['module']: row for row in freeze['analytic_rows']}
    for row in analytic['rows']:
        module, frozen = row['module'], frozen_analytic[row['module']]
        need(module not in object_pins, 'Overlapping analytic supplier')
        need(all(frozen[key] == row[key] for key in
                 ('source_sha256', 'object_sha256', 'originalpath', 'bytes')), 'Analytic freeze row differs')
        source_pins[module] = {'path': frozen['frozen_source'], 'sha256': row['source_sha256']}
        object_pins[module] = {'path': frozen['frozen_object'], 'bytes': row['bytes'],
                               'sha256': row['object_sha256']}
    snapshots = {row['path']: row for row in inputs['files']}
    need(len(snapshots) == len(inputs['files']), 'Duplicate input snapshot paths')
    for row in list(source_pins.values()) + list(object_pins.values()):
        actual = snapshots.get(row['path'])
        need(actual is not None and all(actual[key] == value for key, value in row.items()
                                      if key in ('bytes', 'sha256')), 'Supplier/input snapshot mismatch')
    mains = {row['module']: row for row in union if row['path'].endswith('.olean')}
    need(len(mains) == 704 and set(mains) == set(object_pins), 'Incomplete project object union')
    for module, row in mains.items():
        need(same(row, object_pins[module]) and row['origin'] == object_pins[module]['path'],
             'Union source/object pin mismatch')
        need(same(snapshots.get(row['path'], {}), row), 'Union absent from frozen input snapshot')
    need(run['supplier_modules'] == 704 and run['supplier_normal_recompilation'] is False,
         'Wrong successful supplier boundary')
    need(run['cloud_lean_source_generation'] is False, 'Cloud generated Lean source')
    need(run['LEAN_PATH'].split(':')[0] == str(Path(run['project']).parent / 'objects'),
         'Successful run did not use its single project namespace')
    need(external['module_count'] == len(external['rows']) == run['external_module_count'] == 515,
         'Incomplete external source pin inventory')
    need(external['package_pins'] == verifier['external_package_pins'], 'External package pin mismatch')
    external_rows = {row['module']: row for row in inputs['external_modules']}
    need(len(external_rows) == 515, 'Incomplete external object snapshot')
    for row in external['rows']:
        actual = external_rows[row['module']]
        need(actual['package'] == row['package'] and
             actual['source']['sha256'] == row['source_sha256'], 'External source snapshot differs')
    return {'cell00_modules': 480, 'analytic_modules': 224, 'unique_project_suppliers': 704,
            'external_modules': 515, 'large_supplier_caches_included': False,
            'supplier_cache_storage': 'Existing source/object caches are saved separately; exact pins and full input/union snapshots are included here.',
            'cache_objects_rehashed_by_exporter': False}


def fingerprint_fields(row):
    return {key: row[key] for key in ('bytes', 'sha256')}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--attempt', default=DEFAULT_ATTEMPT)
    ap.add_argument('--backfill-attempt', default=DEFAULT_BACKFILL)
    ap.add_argument('--archive', type=Path)
    ap.add_argument('--manifest', type=Path)
    args = ap.parse_args()
    stage = args.stage.resolve()
    attempt, prior = stage / 'attempts' / args.attempt, stage / 'attempts' / args.backfill_attempt
    need(attempt.resolve().parent == prior.resolve().parent == stage / 'attempts', 'Unsafe attempt path')
    destination = args.archive or stage.parent / 'cell00-original-floor-evidence.tar.xz'
    manifest_path = args.manifest or stage.parent / 'cell00-original-floor-evidence-manifest.json'
    need(not destination.exists() and not manifest_path.exists(), 'Refusing to overwrite an earlier export')
    collect = Collector(stage)
    result, old_result = read(attempt / 'RESULT.json'), read(prior / 'RESULT.json')
    need(result['status'] == 'PASS_NORMAL_KERNEL_FULL_OWNED', 'Selected attempt is not accepted')
    need(old_result['status'] == 'FAILED_STOPPED', 'Expected preserved old failed attempt')
    run = collect.json_pin(result['context'], 'successful_runtime_context')
    old_run = read(prior / 'RUN.json')
    need(run['stage'] == old_run['stage'] == str(stage), 'Attempt stage mismatch')
    verifier = collect.json_pin(run['verifier'], 'successful_verifier')
    collect.pin(run['driver'], 'successful_driver')
    collect.pin(old_run['driver'], 'preserved_v2_driver', historical=True)
    collect.pin(old_run['verifier'], 'preserved_v2_verifier', historical=True)
    need(set(row['module'] for row in verifier['targets']) == set(TARGETS), 'Wrong new owners')
    need(result['new_owners'] == list(TARGETS) and result['kernel_backfills'] == list(BACKFILL),
         'Wrong accepted result inventory')
    inputs = collect.json_pin(run['input_fingerprints'], 'successful_input_snapshot')
    union = collect.json_pin(run['project_object_union'], 'successful_project_union')
    boundary = supplier_boundary(stage, run, verifier, inputs, union, collect)
    for root, label in [(attempt, 'successful_attempt'), (prior, 'preserved_old_attempt')]:
        for name in ['RUN.json', 'RESULT.json', 'INPUT_FINGERPRINTS.json', 'PROJECT_OBJECT_UNION.json']:
            if (root / name).is_file():
                collect.add(root / name, label + '_control')
        for name in ['steps', 'runtime', 'reused-backfills']:
            collect.tree(root / name, label + '_' + name)
    revision = stage / 'revisions/verifier-v2-before-namespace-repair'
    need(revision.is_dir(), 'Missing preserved v2 driver/verifier revision')
    collect.tree(revision, 'preserved_verifier_v2_revision')
    for row in verifier['targets']:
        relative = row['module'].replace('.', '/') + '.lean'
        collect.add(stage / 'new-sources' / relative, 'canonical_new_source', row['source'])
        collect.add(stage / 'audits' / row['audit_file'], 'canonical_owned_audit', row['audit'])

    plan = [(module, 'kernel') for module in BACKFILL]
    plan += [(module, mode) for module in TARGETS for mode in ('normal', 'kernel', 'owned')]
    need(run['plan'] == [list(item) for item in plan], 'Successful plan differs')
    need(len(result['records']) == 8, 'Expected exactly eight accepted proof steps')
    owners, backfills, counted, elapsed = {}, {}, set(), 0.0
    for index, (record, expected) in enumerate(zip(result['records'], plan)):
        module, mode = expected
        need((record['module'], record['mode']) == expected and record['index'] == index,
             'Accepted step order mismatch')
        accepted = collect.json_pin(record['receipt'], 'accepted_' + mode + '_receipt')
        need(accepted['status'] == 'succeeded' and accepted['all_frozen_inputs_unchanged'],
             'Unaccepted or changed-input proof step')
        need((accepted['module'], accepted['mode']) == expected, 'Receipt module/mode differs')
        source = collect.pin(accepted['source'], 'accepted_' + module.split('.')[-1] + '_source')
        obj = collect.pin(accepted['object'], 'accepted_' + module.split('.')[-1] + '_object')
        for sidecar in accepted.get('object_sidecars', []):
            collect.pin(sidecar, 'accepted_object_sidecar')
        command = collect.json_pin(accepted['command_result'], 'accepted_command_result')
        invocation = collect.json_pin(command['command'], 'accepted_command')
        need(all(command.get(key) == value for key, value in invocation.items()),
             'Command/result metadata differs')
        need(same(command['source'], accepted['source']), 'Command/source binding differs')
        if mode != 'normal':
            need(same(command['object_before'], accepted['object']), 'Verified object changed')
        log = collect.pin(command['log'], 'accepted_' + mode + '_log')
        need(command['status'] == 'succeeded' and command['exit_code'] == 0 and
             not command.get('timed_out') and command.get('error') is None, 'Proof command did not succeed')
        need(same(command['log'], accepted['log']), 'Accepted log binding differs')
        context = old_run if module in BACKFILL else run
        need(command['LEAN_PATH'] == context['LEAN_PATH'], 'Command/runtime path mismatch')
        collect.pin(command['input_fingerprints'], 'proof_input_snapshot')
        need(same(command['input_fingerprints'], context['input_fingerprints']), 'Input/runtime binding differs')
        if mode == 'kernel':
            need(command['argv'] == [context['leanchecker_binary']['path'], '--verbose', module],
                 'Not the independent kernel command')
        else:
            need(command['argv'][0] == context['lean_binary']['path'], 'Wrong Lean executable')
        if module in BACKFILL:
            need(record.get('reused') is True, 'Backfill was rerun instead of reused')
            wrapper_path = attempt / 'reused-backfills' / (module.split('.')[-1] + '.json')
            wrapper = read(wrapper_path)
            need(wrapper['reused'] and wrapper['status'] == 'succeeded' and
                 wrapper['same_logical_source_object_runtime_context'], 'Invalid backfill reuse binding')
            need(wrapper['receipt'] == record['receipt'] and same(wrapper['source'], accepted['source']) and
                 same(wrapper['object'], accepted['object']), 'Backfill bytes changed')
            for key in ['source', 'object', 'previous_result', 'previous_run', 'previous_inputs']:
                collect.pin(wrapper[key], 'reused_backfill_' + key)
            backfills[module] = {'source': source, 'object': obj,
                'kernel_receipt': collect.pin(record['receipt'], 'backfill_kernel_receipt'), 'log': log}
        else:
            target_pin = next(row for row in verifier['targets'] if row['module'] == module)
            need(same(source, target_pin['source']), 'Accepted owner differs from frozen source')
            owner = owners.setdefault(module, {'source': source, 'object': obj, 'steps': {}})
            need(same(owner['source'], source) and same(owner['object'], obj), 'Owner changed across steps')
            owner['steps'][mode] = collect.pin(record['receipt'], 'new_owner_' + mode + '_receipt')
            if mode == 'normal':
                need('-o' in command['argv'] and command['argv'][command['argv'].index('-o') + 1] ==
                     accepted['object']['path'], 'Normal output object differs')
            if mode == 'owned':
                audit = collect.pin(accepted['audit_source'], 'accepted_owned_audit_source')
                need(same(audit, target_pin['audit']), 'Accepted audit differs from frozen source')
                need(command['argv'][-1] == accepted['audit_source']['path'], 'Owned audit command differs')
                parsed = parse_owned((stage / log['archive_member']).read_text(), module)
                need(parsed == accepted['owned'], 'Owned JSON/log inventory differs')
                owner.update({'audit': audit, 'owned_declaration_count': parsed['count'],
                              'axioms_union': parsed['axioms_union']})
        key = accepted['command_result']['path']
        if key not in counted:
            counted.add(key)
            elapsed += command['finished_unix'] - command['started_unix']
    need(set(owners) == set(TARGETS) and set(backfills) == set(BACKFILL), 'Incomplete acceptance inventory')
    need(all(set(row['steps']) == {'normal', 'kernel', 'owned'} for row in owners.values()),
         'Incomplete new-owner verification modes')
    failed_normal = []
    for path in sorted((prior / 'steps').glob('*/result.json')):
        receipt = read(path)
        if receipt.get('mode') == 'normal' and receipt['status'] != 'succeeded':
            collect.pin(receipt['command'], 'preserved_failed_normal_command')
            collect.pin(receipt['log'], 'preserved_failed_normal_log')
            failed_normal.append(collect.add(path, 'preserved_failed_normal_result'))
    need(failed_normal, 'Missing preserved failed normal command evidence')
    for member in collect.files:
        if member.endswith('.olean'):
            need(any(member.endswith(module.replace('.', '/') + '.olean')
                     for module in TARGETS + BACKFILL), 'Bulk supplier object selected accidentally')

    files = [collect.files[name] for name in sorted(collect.files)]
    report = {'schema': 'p26_cell00_original_floor_completed_export_v1',
              'status': 'PASS_NORMAL_KERNEL_FULL_OWNED', 'stage': str(stage),
              'successful_attempt': args.attempt, 'backfill_attempt': args.backfill_attempt,
              'new_owners': owners, 'kernel_backfills': backfills,
              'new_normal_steps': 2, 'new_kernel_steps': 2, 'new_owned_steps': 2,
              'reused_kernel_steps': 2, 'accepted_proof_steps': 8,
              'owned_declarations': sum(row['owned_declaration_count'] for row in owners.values()),
              'summed_proof_command_seconds': elapsed, 'supplier_boundary': boundary,
              'historical_file_resolutions': collect.historical_resolutions,
              'preserved_failed_normal_results': failed_normal,
              'P2_6_complete_claimed': False, 'Lean_invoked_by_exporter': False,
              'files': files, 'manifest_self_hash_is_in_stdout_metadata': True}
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    with manifest_path.open('x') as output:
        output.write(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open('xb') as raw:
        with tarfile.open(fileobj=raw, mode='w:xz', dereference=True) as archive:
            for row in files:
                path = Path(row['path'])
                need(same(fingerprint(path), row), f'File changed before export: {path}')
                info = archive.gettarinfo(str(path), arcname=row['archive_member'])
                need(info.isreg(), 'Only regular-file archive entries are allowed')
                with path.open('rb') as source:
                    archive.addfile(info, source)
            info = archive.gettarinfo(str(manifest_path), arcname='CELL00_ORIGINAL_FLOOR_EXPORT_MANIFEST.json')
            with manifest_path.open('rb') as source:
                archive.addfile(info, source)
    print(json.dumps({'archive': {'path': str(destination), **fingerprint(destination)},
                      'manifest': {'path': str(manifest_path), **fingerprint(manifest_path)},
                      'exported_files': len(files), 'new_owners': 2, 'reused_kernel_steps': 2,
                      'accepted_proof_steps': 8, 'owned_declarations': report['owned_declarations'],
                      'preserved_failed_normal_results': len(failed_normal),
                      'bulk_supplier_cache_included': False}), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(f'EXPORT_FAILED: {type(error).__name__}: {error}', file=sys.stderr)
        raise SystemExit(1)
