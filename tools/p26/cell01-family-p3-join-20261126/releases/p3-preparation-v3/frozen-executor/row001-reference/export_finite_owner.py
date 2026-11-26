#!/usr/bin/env python3
"""Strictly export one accepted finite row, without running Lean or Git.

The export retains frozen candidate inputs, previous supplier receipts,
original fixtures, the same new source/object and all three command chains.
The 399 supplier object bodies are excluded. --check-only also works against
an extracted export whose original absolute paths are remapped to that root.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys
import tarfile

from Geometry01Decoding_verify import parse_owned


DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/cell01-row001-finite')
DEFAULT_ATTEMPT = '20261126-row001-v1'
MODULE = 'ImbalancedChen.P2OriginalSaving19Cell01Row001Finite'
RECEIPTS = {
    'normal': 'b3f8c1335e97725c4e09b1a6aec1d7a890272da18cf364aef689abbcc57ea627',
    'kernel': '0fc629ae4e2d811a1b5993e2bba07e82ef5579e0229b4a043afb21fb4642cace',
    'owned': 'b8eb4d0d0bff25b4e0761c2a42672ddf525a439b7b505e16ec8b01c2d90b0b62',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def fp(path):
    digest, size = hashlib.sha256(), 0
    with Path(path).open('rb') as stream:
        for raw in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(raw)
            size += len(raw)
    return {'bytes': size, 'sha256': digest.hexdigest()}


def same(a, b):
    return (isinstance(a, dict) and isinstance(b, dict) and
            all(key in a and key in b and a[key] == b[key] for key in ('bytes', 'sha256')))


def read(path):
    return json.loads(Path(path).read_text())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    ap.add_argument('--attempt', default=DEFAULT_ATTEMPT)
    ap.add_argument('--archive', type=Path)
    ap.add_argument('--manifest', type=Path)
    ap.add_argument('--check-only', action='store_true')
    args = ap.parse_args()
    stage = args.stage.resolve()
    attempt = stage / 'verification' / args.attempt
    need(attempt.resolve().parent == stage / 'verification', 'Unsafe attempt path')
    run, success = read(attempt / 'RUN.json'), read(attempt / 'SUCCESS.json')
    original = Path(run['stage'])
    files = {}

    def add(path, role, pin=None):
        path = Path(path).absolute()
        need(path.is_file() and path.resolve() == path and path.is_relative_to(stage),
             'Missing, escaped or symlinked evidence: ' + str(path))
        member = path.relative_to(stage).as_posix()
        actual = fp(path)
        if pin is not None:
            need(same(actual, pin), 'Evidence fingerprint differs: ' + member)
        row = files.setdefault(member, {'archive_member': member, **actual, 'roles': []})
        need(same(row, actual), 'Evidence changed: ' + member)
        if role not in row['roles']:
            row['roles'].append(role)
        return {'archive_member': member, **actual}

    def local(reference):
        path = Path(reference['path'])
        need(path.is_relative_to(original), 'Receipt path escapes original stage')
        return stage / path.relative_to(original)

    def pinned(reference, role):
        path = local(reference)
        add(path, role, reference)
        return path

    need(success['status'] == 'succeeded' and success['accepted_targets'] == 1 and
         success['frozen_inputs_unchanged'] is True, 'Run did not succeed')
    need(all(success.get(key) == value for key, value in run.items()), 'Success/RUN differs')
    need(run['target_module'] == MODULE and run['original_ordinal'] == 1, 'Wrong target row')
    need(run['accepted_supplier_count'] == 399 and run['full_supplier_kernel_closed'] is True and
         run['cloud_source_generation'] is False and run['suppliers_recompiled'] is False,
         'Supplier boundary differs')
    need(run['LEAN_PATH'].split(':')[0] == str(original / 'objects') and
         run['cwd'] == str(original / 'project'), 'Not a single isolated project namespace')
    need('62eed1db4d67327ec8120be05f1a1b0847d74561' in run['lean_version'] and
         run['mathlib_commit'] == 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1', 'Wrong runtime pin')
    verifier = read(pinned(run['verifier_manifest'], 'accepted_verifier'))
    supplier = read(pinned(run['supplier_manifest'], 'accepted_supplier_pins'))
    for key in ('driver', 'mature_helper'):
        pinned(run[key], 'accepted_' + key)
        need(same(run[key], verifier[key]), 'Verifier helper pin differs')
    need(same(run['supplier_manifest'], verifier['supplier_manifest']), 'Supplier/verifier pin differs')
    need(len(verifier['targets']) == 1 and verifier['targets'][0]['module'] == MODULE, 'Target manifest differs')
    target = verifier['targets'][0]
    for item in verifier['frozen_evidence']:
        member = Path(item['archive_member'])
        need(not member.is_absolute() and '..' not in member.parts, 'Unsafe frozen member')
        add(stage / member, 'frozen_inputs_and_historical_evidence', item)
    package = read(stage / 'PACKAGE_MANIFEST.json')
    add(stage / 'PACKAGE_MANIFEST.json', 'historical_candidate_package_manifest')
    for item in package['files']:
        member = Path(item['archive_member'])
        need(not member.is_absolute() and '..' not in member.parts, 'Unsafe package member')
        add(stage / member, 'historical_frozen_package_file', item)
    installation = read(pinned(run['supplier_installation'], 'supplier_installation'))
    inputs = read(pinned(run['input_fingerprints'], 'full_input_snapshot'))
    snapshots = {item['path']: item for item in inputs['files']}
    need(len(snapshots) == len(inputs['files']), 'Duplicate frozen input path')
    suppliers = {item['module']: item for item in supplier['suppliers']}
    need(len(suppliers) == len(supplier['suppliers']) == 399 and supplier['normal_only_suppliers'] == [],
         'Invalid supplier inventory')
    entries = {(item['module'], item['kind']): item for item in installation['entries']}
    need(len(entries) == len(installation['entries']) == 798 and installation['supplier_modules'] == 399 and
         installation['suppliers_recompiled'] is False, 'Incomplete supplier installation')
    for module, item in suppliers.items():
        for kind in ('source', 'object'):
            entry = entries[(module, kind)]
            need(same(entry['source'], item[kind]) and same(entry['installed'], item[kind]),
                 'Installed supplier SHA differs')
            for pin in (entry['source'], entry['installed']):
                need(same(snapshots.get(pin['path']), pin), 'Supplier absent from frozen snapshot')
    completion = read(stage / supplier['kernel_completion']['archive_member'])
    prior_kernel = read(stage / supplier['kernel_receipt']['archive_member'])
    prior_result = read(stage / supplier['kernel_result']['archive_member'])
    recurrence = suppliers['ImbalancedChen.P2Winner9HomogeneousRecurrence']
    need(completion['supplier_kernel_closed_in_combined_evidence'] is True and
         completion['remaining_pending_supplier_kernel_modules'] == [], 'Incomplete kernel addendum')
    for key in ('source', 'object'):
        need(same(completion[key], recurrence[key]) and same(prior_kernel[key], recurrence[key]),
             'Kernel addendum differs from current supplier bytes')
    need(prior_kernel['status'] == prior_result['status'] == 'succeeded' and prior_result['exit_code'] == 0 and
         same(prior_kernel['command_result'], supplier['kernel_result']) and
         same(prior_kernel['log'], supplier['kernel_log']) and same(prior_result['log'], supplier['kernel_log']),
         'Broken historical kernel chain')
    need(len(success['records']) == 3, 'Expected exactly three accepted commands')
    owner, steps, duration, peak, inventory = {}, {}, 0.0, 0, None
    for record, mode in zip(success['records'], ('normal', 'kernel', 'owned')):
        need(record['module'] == MODULE and record['mode'] == mode and record['status'] == 'succeeded',
             'Wrong accepted mode order/status')
        need(record['receipt']['sha256'] == RECEIPTS[mode], 'Unexpected successful receipt identity')
        result = read(pinned(record['receipt'], 'accepted_' + mode + '_result'))
        need(result['status'] == 'succeeded' and result['exit_code'] == 0 and
             all(result.get(key) == value for key, value in run.items()), 'Command/runtime status differs')
        command = read(pinned(result['command'], 'accepted_' + mode + '_command'))
        need(all(result.get(key) == value for key, value in command.items()), 'Command/result metadata differs')
        log_path = pinned(result['log'], 'accepted_' + mode + '_log')
        source = add(pinned(result['source'], 'accepted_source'), 'accepted_source', target['source'])
        obj = add(pinned(result['object'], 'accepted_object'), 'accepted_object')
        need(result['source']['path'] == str(original / 'project' / (MODULE.replace('.', '/') + '.lean')) and
             result['object']['path'] == str(original / 'objects' / (MODULE.replace('.', '/') + '.olean')),
             'Noncanonical source/object target')
        if owner:
            need(same(owner['source'], source) and same(owner['object'], obj), 'Target changed between modes')
        else:
            owner = {'source': source, 'object': obj}
        argv = result['argv']
        if mode == 'normal':
            need(result['object_before'] is None and argv[0] == run['lean_binary']['path'] and
                 argv[argv.index('-o') + 1] == result['object']['path'] and
                 argv[-1] == MODULE.replace('.', '/') + '.lean', 'Wrong normal command')
            need(set(result['printed_axioms']) <= ALLOWED, 'Forbidden printed axiom')
        else:
            need(same(result['object_before'], result['object']), 'Object changed while checked')
            if mode == 'kernel':
                need(argv == [run['leanchecker_binary']['path'], '--verbose', MODULE], 'Wrong independent kernel command')
            else:
                audit = add(pinned(result['audit_source'], 'accepted_owned_audit'), 'accepted_owned_audit', target['audit'])
                need(argv[0] == run['lean_binary']['path'] and argv[-1] == result['audit_source']['path'],
                     'Wrong owned command')
                inventory = read(pinned(result['owned_declarations'], 'complete_owned_inventory'))
                parsed = parse_owned(log_path.read_text(), MODULE)
                need(parsed == inventory and parsed['owned_declaration_count'] == result['owned_declaration_count'],
                     'Owned log/inventory/count differs')
                owner['audit'] = audit
        steps[mode] = {'receipt': add(local(record['receipt']), 'accepted_' + mode + '_result'),
                       'elapsed_seconds': result['elapsed_seconds'], 'peak_rss_bytes': result['peak_rss_bytes']}
        duration += result['elapsed_seconds']
        peak = max(peak, result['peak_rss_bytes'])
    for path in sorted(attempt.rglob('*')):
        if path.is_file():
            add(path, 'complete_successful_attempt')
    for other in sorted((stage / 'verification').iterdir()):
        if other.is_dir() and other != attempt and (other / 'STOPPED.json').is_file():
            for path in sorted(other.rglob('*')):
                if path.is_file():
                    add(path, 'preserved_failed_attempt')
    for member in files:
        if member.endswith('.olean'):
            need(member == owner['object']['archive_member'], 'Supplier object accidentally selected')
    report = {'schema': 'p26_cell01_row001_finite_completed_export_v1', 'status': 'PASS_NORMAL_KERNEL_FULL_OWNED',
        'original_stage': str(original), 'attempt': args.attempt, 'module': MODULE, 'original_ordinal': 1,
        'owner': owner, 'steps': steps, 'normal': 1, 'kernel': 1, 'owned': 1,
        'owned_declarations': inventory['owned_declaration_count'], 'axioms_union': inventory['axioms_union'],
        'summed_step_seconds': duration, 'sampled_Lean_process_tree_peak_bytes': peak,
        'supplier_modules': 399, 'full_supplier_kernel_closed': True, 'supplier_object_bodies_included': False,
        'historical_candidate_evidence_preserved': True, 'Lean_invoked_by_exporter': False,
        'integral_claimed': False, 'P2_6_complete_claimed': False,
        'files': [files[name] for name in sorted(files)]}
    if args.check_only:
        print(json.dumps({key: value for key, value in report.items() if key != 'files'}, indent=2))
        return
    destination = args.archive or stage.parent / 'cell01-row001-finite-completed-evidence.tar.xz'
    manifest = args.manifest or stage.parent / 'cell01-row001-finite-completed-evidence-manifest.json'
    need(not destination.exists() and not manifest.exists(), 'Refusing to overwrite an export')
    with manifest.open('x') as stream:
        stream.write(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    with destination.open('xb') as raw:
        with tarfile.open(fileobj=raw, mode='w:xz') as archive:
            for member, pin in sorted(files.items()):
                path = stage / member
                need(same(fp(path), pin), 'Evidence changed before export')
                info = archive.gettarinfo(str(path), arcname=member)
                need(info.isreg(), 'Only regular archive files are allowed')
                with path.open('rb') as incoming:
                    archive.addfile(info, incoming)
            archive.add(manifest, arcname='COMPLETED_EXPORT_MANIFEST.json', recursive=False)
    print(json.dumps({'archive': {'path': str(destination), **fp(destination)},
        'manifest': {'path': str(manifest), **fp(manifest)}, 'files': len(files),
        'owned_declarations': inventory['owned_declaration_count'], 'summed_step_seconds': duration,
        'sampled_Lean_process_tree_peak_bytes': peak, 'Lean_invoked': False}), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(f'EXPORT_FAILED: {type(error).__name__}: {error}', file=sys.stderr)
        raise SystemExit(1)
