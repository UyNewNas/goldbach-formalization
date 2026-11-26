#!/usr/bin/env python3
"""Export the accepted 22-owner Cell01 row000 pilot without invoking Lean.

The successful v3 driver, complete 66 command/log/result receipts, owned
inventories, selected sources/objects/audits, and exact supplier pin manifests
are included. The 398 supplier object bodies remain in their separate caches.
The historical pending Recurrence kernel boundary is preserved for a separate
same-SHA P1 receipt addendum; the held original-floor bridge is not a target.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tarfile


DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/cell01-row000')
DEFAULT_ATTEMPT = '20261126T034646622466Z'
V3_DRIVER_SHA = 'a57d67eb49e5a71c507af022afc38bb7c850bdfe73f52780200cdc4cc63a2a05'
V3_VERIFIER_SHA = '086ed606fa666c7ccf97cb51d3fccb1123640b9fce38d1fd7cc3c570d8a8984b'
LEAN_COMMIT = '62eed1db4d67327ec8120be05f1a1b0847d74561'
MATHLIB_COMMIT = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PACKAGES = ['LeanSearchClient', 'Qq', 'aesop', 'batteries', 'importGraph', 'plausible', 'proofwidgets']
PENDING = ['ImbalancedChen.P2Winner9HomogeneousRecurrence']
HELD = 'ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge'


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
            all(key in a and key in b and a[key] == b[key] for key in ('bytes', 'sha256')))


def read(path):
    return json.loads(Path(path).read_text())


def parse_owned(text, module):
    buckets = {'INVENTORY': [], 'DECL': [], 'COMPLETE': []}
    for line in text.splitlines():
        for marker, values in buckets.items():
            prefix = 'P26_GEOMETRY01_AUDIT_' + marker + ' '
            if line.startswith(prefix):
                values.append(json.loads(line[len(prefix):]))
    need(len(buckets['INVENTORY']) == len(buckets['COMPLETE']) == 1,
         'Missing or duplicate complete ownership inventory')
    inv, done = buckets['INVENTORY'][0], buckets['COMPLETE'][0]
    declarations, names = buckets['DECL'], inv['environment']
    need(inv['module'] == done['module'] == module, 'Owned module mismatch')
    need(names and len(names) == len(set(names)), 'Empty or duplicate owned inventory')
    need(sorted(names) == sorted(inv['serialized']), 'Serialized/environment inventory differs')
    need(sorted(row['name'] for row in declarations) == sorted(names), 'Incomplete owned declarations')
    need(done['count'] == len(names), 'Owned completion count differs')
    for row in declarations:
        need(row['module'] == module and row['type'] and '⋯' not in row['type'], 'Truncated owned type')
        need(not row['unsafe'] and not row['partial'] and not row['axiom'], 'Unsafe/partial/new axiom owner')
        need(set(row['axioms']) <= ALLOWED, 'Forbidden owned transitive axiom')
    return {'module': module, 'owned_declaration_count': len(names),
            'axioms_union': sorted({ax for row in declarations for ax in row['axioms']}),
            'inventory': inv, 'declarations': declarations, 'complete': done}


class Collector:
    def __init__(self, stage):
        self.stage, self.files, self.historical_resolutions = stage, {}, []

    def add(self, path, role, expected=None, member=None):
        path = Path(path).absolute()
        need(path.is_file() and path.resolve() == path, f'Missing or symlinked evidence: {path}')
        if member is None:
            need(path.is_relative_to(self.stage), f'Evidence escapes stage: {path}')
            member = path.relative_to(self.stage).as_posix()
        else:
            need(path.is_relative_to(self.stage.parent), f'External pin escapes continuation root: {path}')
        need(member and not Path(member).is_absolute() and '..' not in Path(member).parts,
             'Unsafe archive member')
        pin = fingerprint(path)
        if expected is not None:
            need(same(pin, expected), f'Fingerprint mismatch: {path}')
        row = self.files.setdefault(member, {'path': str(path), 'archive_member': member,
                                             **pin, 'roles': []})
        need(row['path'] == str(path) and same(row, pin), f'Conflicting evidence member: {member}')
        if role not in row['roles']:
            row['roles'].append(role)
        return {'archive_member': member, **pin}

    def pin(self, reference, role, historical=False):
        path = Path(reference['path'])
        if historical and (not path.is_file() or not same(fingerprint(path), reference)):
            matches = [p for root in ('revisions', 'verifier-history')
                       for p in (self.stage / root).rglob(path.name)
                       if p.is_file() and same(fingerprint(p), reference)]
            need(len(matches) == 1, f'No unique preserved verifier version: {path}')
            path = matches[0]
            self.historical_resolutions.append({'recorded_path': reference['path'],
                'archive_member': path.relative_to(self.stage).as_posix(), 'sha256': reference['sha256']})
        return self.add(path, role, reference)

    def json_pin(self, reference, role, historical=False):
        pin = self.pin(reference, role, historical)
        return read(self.files[pin['archive_member']]['path'])

    def tree(self, directory, role):
        if Path(directory).exists():
            for path in sorted(Path(directory).rglob('*')):
                if path.is_file():
                    self.add(path, role)


def supplier_boundary(stage, run, supplier, installation, targets, collect):
    rows = {row['module']: row for row in supplier['suppliers']}
    need(len(rows) == len(supplier['suppliers']) == supplier['existing_supplier_count'] == 398,
         'Expected exactly 398 unique suppliers')
    need(supplier['new_targets'] == len(targets) == 22 and supplier['project_closure_count'] == 420,
         'Finite closure count differs')
    need(not set(rows).intersection(targets) and HELD not in rows, 'New/held owner enters supplier set')
    need(supplier['same_name_source_and_object_conflicts'] == [], 'Supplier hash conflict')
    need(supplier['source_generation_on_cloud'] is False, 'Cloud generated supplier source')
    need(supplier['normal_only_suppliers'] == run['pending_supplier_kernel'] == PENDING,
         'Historical pending kernel boundary differs')
    need(run['full_supplier_kernel_closed'] is False, 'Unexpected historical supplier closure claim')
    need([row['label'] for row in supplier['packages']] == ['cell00', 'geometry01', 'moment01'],
         'Unexpected supplier packages')
    package_pins = []
    for package in supplier['packages']:
        root = (stage / package['relative_root']).resolve()
        need(root == stage.parent / package['label'], 'Supplier root escapes sibling stage')
        manifest = package['manifest']
        member = Path(manifest['archive_member'])
        need(not member.is_absolute() and '..' not in member.parts, 'Unsafe supplier manifest member')
        exported = collect.add(root / member, 'supplier_package_pin_manifest', manifest,
                               'supplier-pins/' + package['label'] + '/' + member.as_posix())
        package_pins.append({'label': package['label'], 'manifest': exported,
                             'package': package['package'],
                             'completion_evidence_pin_count': len(package.get('completion_evidence', []))})
    need(installation['single_project_object_root'] == str(stage / 'objects') and
         installation['supplier_modules'] == 398 and installation['suppliers_recompiled'] is False,
         'Wrong installed supplier namespace')
    entries = {(row['module'], row['kind']): row for row in installation['entries']}
    need(len(entries) == len(installation['entries']) == 796, 'Incomplete supplier installation snapshot')
    for module, row in rows.items():
        relative, origin = Path(module.replace('.', '/')), row['locations'][0]
        origin_root = (stage / origin['relative_root']).resolve()
        need(origin_root.name in {'cell00', 'geometry01', 'moment01'} and
             origin_root.parent == stage.parent, 'Unexpected installed supplier origin')
        for kind, suffix, directory in [('source', '.lean', 'project'), ('object', '.olean', 'objects')]:
            item = entries[(module, kind)]
            need(same(item['source'], row[kind]) and same(item['installed'], row[kind]),
                 'Installed supplier differs from source/object pins')
            need(item['source']['path'] == str(origin_root / origin[kind + '_member']) and
                 item['installed']['path'] == str(stage / directory / relative.with_suffix(suffix)),
                 'Installed supplier path differs')
            need(item['method'] in {'hardlink', 'cross_filesystem_copy', 'existing_identical'},
                 'Unexpected supplier installation method')
    need(run['LEAN_PATH'].split(':')[0] == str(stage / 'objects'), 'Missing single project namespace')
    need(run['required_mathlib_packages'] == PACKAGES, 'Wrong required package list')
    package_roots = run['mathlib_package_object_roots']
    need(all(any(Path(root).as_posix().endswith('/' + name + '/.lake/build/lib/lean')
                 for root in package_roots) for name in PACKAGES), 'Missing required package object root')
    need(run['cloud_source_generation'] is False and run['suppliers_recompiled'] is False,
         'Cloud generated sources or repeated suppliers')
    return {'existing_supplier_modules': 398, 'new_owner_modules': 22,
            'finite_project_closure': 420, 'installation_entries': 796,
            'package_pins': package_pins, 'large_supplier_caches_included': False,
            'supplier_cache_storage': 'Separate accepted packages retain the 398 source/object bodies; this export retains their exact manifests and installation snapshot.',
            'cache_objects_rehashed_by_exporter': False,
            'full_supplier_kernel_closed_at_run': False,
            'pending_supplier_kernel_at_run': run['pending_supplier_kernel'],
            'same_SHA_P1_kernel_receipt_addendum_required': True,
            'historical_pending_job_hint_is_not_kernel_evidence': True}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--attempt', default=DEFAULT_ATTEMPT)
    ap.add_argument('--archive', type=Path)
    ap.add_argument('--manifest', type=Path)
    args = ap.parse_args()
    stage = args.stage.resolve()
    attempt = stage / 'verification' / args.attempt
    need(attempt.resolve().parent == stage / 'verification', 'Unsafe attempt path')
    destination = args.archive or stage.parent / 'cell01-row000-completed-evidence.tar.xz'
    manifest_path = args.manifest or stage.parent / 'cell01-row000-completed-evidence-manifest.json'
    need(not destination.exists() and not manifest_path.exists(), 'Refusing to overwrite an earlier export')
    collect = Collector(stage)
    result, run = read(attempt / 'SUCCESS.json'), read(attempt / 'RUN.json')
    need(result['status'] == 'succeeded' and result['accepted_targets'] == 22 and
         result['frozen_inputs_unchanged'], 'Selected attempt is not accepted')
    need(all(result.get(key) == value for key, value in run.items()), 'Success/runtime metadata differs')
    need(run['attempt'] == args.attempt and run['stage'] == str(stage) and
         run['cwd'] == str(stage / 'project'), 'Successful run path mismatch')
    need('4.33.0-rc1' in run['lean_version'] and LEAN_COMMIT in run['lean_version'] and
         run['mathlib_commit'] == MATHLIB_COMMIT, 'Runtime pins differ')
    need(run['driver']['sha256'] == V3_DRIVER_SHA and
         run['verifier_manifest']['sha256'] == V3_VERIFIER_SHA, 'Not the accepted v3 verifier')
    verifier = collect.json_pin(run['verifier_manifest'], 'accepted_v3_verifier', historical=True)
    collect.pin(run['driver'], 'accepted_v3_driver', historical=True)
    collect.pin(run['mature_helper'], 'accepted_mature_helper')
    supplier = collect.json_pin(run['supplier_manifest'], 'finite_supplier_manifest')
    installation = collect.json_pin(run['supplier_installation'], 'supplier_installation_snapshot')
    for key in ('driver', 'mature_helper'):
        need(same(run[key], verifier[key]), 'Verifier/runtime helper pin mismatch')
    need(same(run['supplier_manifest'], verifier['supplier_manifest']), 'Verifier/supplier pin mismatch')
    targets = {row['module']: row for row in verifier['targets']}
    need(len(targets) == len(verifier['targets']) == 22 and HELD not in targets,
         'Wrong finite target set')
    need([row['module'] for row in verifier['held_targets']] == [HELD] and
         run['held_targets'] == verifier['held_targets'], 'Held analytic bridge differs')
    boundary = supplier_boundary(stage, run, supplier, installation, targets, collect)
    collect.tree(attempt, 'accepted_run_evidence')
    for directory in ('verifier-history', 'revisions', 'evidence/source-pilot'):
        collect.tree(stage / directory, 'preserved_' + directory.replace('/', '_'))
    if (stage / 'cloud_order.txt').is_file():
        order = (stage / 'cloud_order.txt').read_text().splitlines()
        need([line.strip() for line in order if line.strip()] == list(targets), 'Cloud target order differs')
        collect.add(stage / 'cloud_order.txt', 'frozen_cloud_order')
    preserved_failed_runs = []
    for other in sorted((stage / 'verification').iterdir()):
        if other.is_dir() and other != attempt and (other / 'STOPPED.json').is_file():
            collect.tree(other, 'preserved_failed_run')
            preserved_failed_runs.append(other.name)

    plan = [(module, mode) for module in targets for mode in ('normal', 'kernel', 'owned')]
    need(len(result['records']) == len(plan) == 66, 'Expected exactly 66 accepted proof commands')
    owners, seen_receipts, duration, peak = {}, set(), 0.0, 0
    for record, expected in zip(result['records'], plan):
        module, mode = expected
        need((record['module'], record['mode']) == expected and record.get('status') == 'succeeded',
             'Accepted command order/status differs')
        receipt_pin = record['receipt']
        need(receipt_pin['path'] not in seen_receipts, 'Duplicate accepted command receipt')
        seen_receipts.add(receipt_pin['path'])
        receipt = collect.json_pin(receipt_pin, 'accepted_' + mode + '_result')
        need(receipt['status'] == 'succeeded' and receipt['exit_code'] == 0 and
             (receipt['module'], receipt['mode']) == expected, 'Unaccepted proof command')
        need(all(receipt.get(key) == value for key, value in run.items()), 'Command/runtime context differs')
        command_path = Path(receipt_pin['path']).with_name(mode + '-command.json')
        command = read(command_path)
        collect.add(command_path, 'accepted_' + mode + '_command')
        need(all(receipt.get(key) == value for key, value in command.items()), 'Command/result metadata differs')
        item = targets[module]
        relative = module.replace('.', '/')
        source = collect.pin(receipt['source'], 'accepted_new_source')
        obj = collect.pin(receipt['object'], 'accepted_new_object')
        need(receipt['source']['path'] == str(stage / 'project' / (relative + '.lean')) and
             receipt['object']['path'] == str(stage / 'objects' / (relative + '.olean')),
             'New source/object outside canonical target paths')
        need(same(source, item['source']), 'Accepted owner differs from frozen source')
        log = collect.pin(receipt['log'], 'accepted_' + mode + '_log')
        owner = owners.setdefault(module, {'source': source, 'object': obj, 'steps': {}})
        need(same(owner['source'], source) and same(owner['object'], obj), 'Owner changed across checks')
        owner['steps'][mode] = collect.pin(receipt_pin, 'new_owner_' + mode + '_receipt')
        argv = receipt['argv']
        if mode == 'normal':
            need(receipt['object_before'] is None and Path(argv[0]).name == 'lean' and '-o' in argv and
                 argv[argv.index('-o') + 1] == receipt['object']['path'] and
                 argv[-1] == relative + '.lean', 'Normal command does not match frozen target')
            need(set(receipt['printed_axioms']) <= ALLOWED, 'Forbidden printed normal axiom')
            owner['lean_binary_path'] = argv[0]
        else:
            need(same(receipt['object_before'], receipt['object']), 'Checked object changed')
            if mode == 'kernel':
                need(argv == [str(Path(owner['lean_binary_path']).with_name('leanchecker')), '--verbose', module],
                     'Not the independent kernel command')
            else:
                audit = collect.pin(receipt['audit_source'], 'accepted_owned_audit')
                need(same(audit, item['audit']) and argv[0] == owner['lean_binary_path'] and
                     argv[-1] == receipt['audit_source']['path'], 'Owned audit command/source differs')
                parsed = parse_owned(Path(receipt['log']['path']).read_text(), module)
                owned = collect.json_pin(receipt['owned_declarations'], 'complete_owned_inventory')
                need(parsed == owned and parsed['owned_declaration_count'] == receipt['owned_declaration_count'],
                     'Owned inventory/log/count differs')
                owner.update({'audit': audit, 'owned_declarations': collect.pin(receipt['owned_declarations'],
                    'complete_owned_inventory'), 'owned_declaration_count': parsed['owned_declaration_count'],
                    'axioms_union': parsed['axioms_union']})
        duration += receipt['elapsed_seconds']
        peak = max(peak, receipt['peak_rss_bytes'])
    need(set(owners) == set(targets) and all(set(row['steps']) == {'normal', 'kernel', 'owned'}
         for row in owners.values()), 'Incomplete accepted owner inventory')
    for member in collect.files:
        if member.endswith('.olean'):
            need(member in {row['object']['archive_member'] for row in owners.values()},
                 'Bulk supplier object selected accidentally')
    files = [collect.files[name] for name in sorted(collect.files)]
    report = {'schema': 'p26_cell01_row000_completed_export_v1', 'status': 'succeeded',
              'stage': str(stage), 'successful_attempt': args.attempt,
              'accepted_targets': 22, 'normal': 22, 'kernel': 22, 'owned_audit': 22,
              'accepted_proof_commands': 66, 'owners': owners,
              'owned_declarations': sum(row['owned_declaration_count'] for row in owners.values()),
              'peak_rss_bytes': peak, 'summed_step_seconds': duration,
              'supplier_boundary': boundary, 'held_targets': verifier['held_targets'],
              'preserved_failed_runs': preserved_failed_runs,
              'historical_file_resolutions': collect.historical_resolutions,
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
            info = archive.gettarinfo(str(manifest_path), arcname='CELL01_ROW000_EXPORT_MANIFEST.json')
            with manifest_path.open('rb') as source:
                archive.addfile(info, source)
    print(json.dumps({'archive': {'path': str(destination), **fingerprint(destination)},
                      'manifest': {'path': str(manifest_path), **fingerprint(manifest_path)},
                      'exported_files': len(files), 'accepted_targets': 22,
                      'normal': 22, 'kernel': 22, 'owned': 22,
                      'owned_declarations': report['owned_declarations'],
                      'peak_rss_bytes': peak, 'summed_step_seconds': duration,
                      'full_supplier_kernel_closed_at_run': False,
                      'bulk_supplier_cache_included': False}), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(f'EXPORT_FAILED: {type(error).__name__}: {error}', file=sys.stderr)
        raise SystemExit(1)
