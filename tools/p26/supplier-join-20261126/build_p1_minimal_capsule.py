#!/usr/bin/env python3
"""Create an immutable minimal exact-byte supplier capsule, without Lean.

Inputs are explicitly enumerated pins. Only requested objects, fourteen
requested sources, and their metadata manifest become archive members.
No row001 file, archive, log, or receipt may be accessed.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import importlib.util
import io
import json
import lzma
import os
import stat
import sys
import tarfile
import time

sys.dont_write_bytecode = True
MODES = ('normal', 'kernel', 'owned')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
WATCHED = {}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def canonical(path):
    p = Path(path).absolute()
    need('row001' not in str(p).lower(), 'ROW001_OUTSIDE_CAPSULE_SCOPE')
    need('..' not in p.parts and not p.is_symlink() and p.resolve() == p,
         'Noncanonical or symlinked path: ' + str(p))
    return p


def fp(path):
    p = canonical(path)
    before = p.stat()
    need(stat.S_ISREG(before.st_mode), 'Not a regular file: ' + str(p))
    h = hashlib.sha256()
    with p.open('rb') as incoming:
        for block in iter(lambda: incoming.read(1024 * 1024), b''):
            h.update(block)
    after = p.stat()
    need((before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns),
         'File changed during hash: ' + str(p))
    return {'path': str(p), 'bytes': after.st_size, 'sha256': h.hexdigest()}


def same(a, b):
    return isinstance(a, dict) and isinstance(b, dict) and all(
        a.get(key) == b.get(key) for key in ('bytes', 'sha256'))


def watch(path, expected=None, exact=True):
    actual = fp(path)
    if expected is not None:
        need(same(actual, expected), 'Pinned bytes changed: ' + str(path))
        if exact and 'path' in expected:
            need(actual['path'] == expected['path'], 'Pinned path changed: ' + str(path))
    before = WATCHED.setdefault(actual['path'], actual)
    need(before == actual, 'Input changed: ' + str(path))
    return actual


def read_json(path):
    p = canonical(path)
    need(p.suffix == '.json', 'JSON expected')
    watch(p)
    return json.loads(p.read_text())


def body(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()


def write_new(path, data):
    p = canonical(path)
    with p.open('xb') as output:
        output.write(data)


def load_module(name, expected):
    watch(expected['path'], expected)
    spec = importlib.util.spec_from_file_location(name, expected['path'])
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def empty_sidecars(obj):
    path = canonical(obj['path'])
    candidates = (Path(str(path) + '.server'), Path(str(path) + '.private'), path.with_suffix('.ir'))
    need(not any(p.exists() or p.is_symlink() for p in candidates),
         'Unpinned object sidecar: ' + str(path))


def prefix_validation(request, items, driver):
    stage = canonical(request['prefix_stage'])
    root = stage / 'verification' / request['prefix_attempt']
    run_path, partial_path = root / 'RUN.json', root / 'PARTIAL.json'
    run, partial = read_json(run_path), read_json(partial_path)
    ordinals = request['prefix_expected_ordinals']
    need(ordinals == list(range(98, 107)), 'Unexpected prefix selection')
    need(partial['status'] == 'BUDGET_PAUSE' and partial['completed_rows'] == ordinals
         and partial['remaining_ordinals'] == list(range(107, 144))
         and partial['batch_complete'] is False and partial['frozen_inputs_unchanged'] is True,
         'Prefix is not the exact preserved successful nine-row prefix')
    need(not (root / 'SUCCESS.json').exists() and not (root / 'STOPPED.json').exists(),
         'Contradictory prefix terminal markers')
    need(all(partial.get(key) == value for key, value in run.items()), 'RUN/PARTIAL context differs')
    need(run['selected_ordinals'] == list(range(98, 144)) and run['batch_label'] == 'C',
         'Original C invocation selection changed')
    for key in ('lean_binary', 'leanchecker_binary', 'input_fingerprints',
                'supplier_installation', 'supplier_manifest', 'verifier_manifest',
                'driver', 'mature_helper'):
        watch(run[key]['path'], run[key])
    for key in ('prefix_export_manifest', 'prefix_export_review'):
        watch(request[key]['path'], request[key])
    records = partial['records']
    ordered = [(f'ImbalancedChen.P2OriginalSaving19Cell01Row{n:03d}Finite', mode)
               for n in ordinals for mode in MODES]
    need([(r['module'], r['mode']) for r in records] == ordered, 'Prefix triple coverage differs')
    result_rows = []
    for n in ordinals:
        module = f'ImbalancedChen.P2OriginalSaving19Cell01Row{n:03d}Finite'
        item = items[module]
        row_path = root / module.split('.')[-1] / 'ROW_ACCEPTED.json'
        row = read_json(row_path)
        source = watch(item['source']['path'], item['source'])
        obj = watch(item['object_path'], row['object'])
        audit = watch(row['audit']['path'], row['audit'])
        empty_sidecars(obj)
        need(row['status'] == 'PASS_NORMAL_KERNEL_FULL_OWNED' and row['module'] == module
             and row['original_ordinal'] == n and row['source'] == source
             and row['object'] == obj and row['owned_declaration_count'] == 292
             and row['runtime_context_sha256'] == run['runtime_context_sha256'],
             'Prefix ROW_ACCEPTED differs: ' + module)
        chain = []
        for mode in MODES:
            record = records[len(result_rows) * 3 + len(chain)]
            reference = record.get('receipt') or record.get('reused_successful_receipt')
            need(reference is not None, 'Missing prefix result reference')
            expected_path = row_path.parent / (mode + '-result.json')
            need(reference['path'] == str(expected_path), 'Unexpected prefix receipt location')
            watch(expected_path, reference)
            result = driver.validated_receipt(expected_path, module, mode, source, obj, audit, run)
            need(result is not None and result['status'] == 'succeeded'
                 and result['exit_code'] == 0 and result['original_ordinal'] == n,
                 'Original strict receipt validator rejected: ' + module + ' / ' + mode)
            for key in ('command', 'log', 'input_fingerprints', 'supplier_installation'):
                watch(result[key]['path'], result[key])
            if mode == 'kernel':
                need(Path(result['log']['path']).read_text().strip() == 'replaying ' + module,
                     'Kernel log target differs')
            if mode == 'owned':
                watch(result['owned_declarations']['path'], result['owned_declarations'])
                inventory = driver.parse_owned(Path(result['log']['path']).read_text(), module)
                need(inventory['owned_declaration_count'] == 292 and
                     set(inventory['axioms_union']) <= ALLOWED,
                     'Complete owned inventory differs')
            chain.append(reference)
        need(row['chain'] == chain, 'ROW_ACCEPTED chain differs')
        item['object_expected'] = {key: obj[key] for key in ('bytes', 'sha256')}
        item['object_candidates'] = [obj]
        result_rows.append({'module': module, 'ordinal': n, 'source': source, 'object': obj,
                            'row_acceptance': fp(row_path), 'chain': chain,
                            'owned_declaration_count': 292})
    return {'status': 'PASS_EXACT_NINE_ROW_ORIGINAL_RECEIPT_CHAINS',
            'run': fp(run_path), 'partial': fp(partial_path), 'rows': result_rows,
            'validated_receipts': 27, 'owned_declarations': 2628,
            'runtime_context_sha256': run['runtime_context_sha256'],
            'full_C_batch_claimed': False, 'receipt_bodies_in_archive': False}


def generic_validation(request, item, generic_driver, owned_helper):
    context_pin = watch(request['generic_context']['path'], request['generic_context'])
    context = read_json(context_pin['path'])
    source = watch(item['source']['path'], item['source'])
    obj = watch(item['object_candidates'][0]['path'], item['object_expected'], exact=False)
    empty_sidecars(obj)
    audit = watch(context['audit']['path'], context['audit'])
    stage = canonical(request['generic_stage'])
    chains = []
    for record in request['generic_receipts']:
        reference = record['receipt']
        watch(reference['path'], reference)
        seal = generic_driver.validate_step(reference['path'], stage, context_pin,
                                            source, audit, Path(obj['path']), owned_helper)
        need(seal['mode'] == record['mode'] and seal['object'] == obj
             and seal['object_sidecars'] == [], 'Generic exact accepted object differs')
        for key in ('run', 'command', 'command_result', 'log', 'before', 'after'):
            watch(seal[key]['path'], seal[key])
        if record['mode'] == 'owned':
            for key in ('owned_declarations', 'module_byte_context'):
                watch(seal[key]['path'], seal[key])
        chains.append({'mode': record['mode'], 'receipt': reference})
    need([r['mode'] for r in chains] == list(MODES), 'Generic triple differs')
    return {'status': 'PASS_ORIGINAL_GENERIC_THREE_CHAINS', 'source': source, 'object': obj,
            'context': context_pin, 'records': chains, 'receipt_bodies_in_archive': False}


def main():
    started = time.monotonic()
    ap = argparse.ArgumentParser()
    ap.add_argument('--request', required=True, type=Path)
    args = ap.parse_args()
    request = read_json(args.request)
    root = canonical(request['destination_root'])
    need(root.is_dir(), 'Upload root is missing')
    items = {item['module']: item for item in request['items']}
    need(len(items) == len(request['items']) == request['expected_module_count'] == 189,
         'Wrong or duplicate supplier selection')
    need(all('row001' not in json.dumps(item).lower() for item in items.values()), 'Blocked row001 input')
    need(sorted(m for m, item in items.items() if item['include_source_body']) ==
         request['source_body_modules'] and len(request['source_body_modules']) == 14,
         'Wrong source-body selection')
    for item in items.values():
        need(item['expected_sidecars'] == [], 'Unexpected requested sidecars')
        for pin in [item['source'], *item.get('object_candidates', [])]:
            path = canonical(pin['path'])
            need(not path.is_relative_to(root) and not root.is_relative_to(path), 'Input/output overlap')
    validators = request['fixed_validator_scripts']
    helper = load_module('Geometry01Decoding_verify', validators['batch_helper'])
    driver = load_module('p26_capsule_original_batch_driver', validators['batch_driver'])
    generic_driver = load_module('p26_capsule_original_generic_driver', validators['generic_driver'])
    print(json.dumps({'phase': 'validating_original_receipts', 'finite_rows': [98, 106]}), flush=True)
    prefix = prefix_validation(request, items, driver)
    generic = generic_validation(request, items['ImbalancedChen.P2OriginalSaving19OriginalFloorTransport'],
                                 generic_driver, helper)
    members, module_records = [], []
    for module, item in sorted(items.items()):
        source = watch(item['source']['path'], item['source'])
        obj = None
        for candidate in item['object_candidates']:
            if Path(candidate['path']).is_file():
                actual = fp(candidate['path'])
                if same(actual, item['object_expected']):
                    obj = watch(candidate['path'], item['object_expected'], exact=False)
                    break
        need(obj is not None, 'Restore exact object before packaging: ' + module)
        empty_sidecars(obj)
        for record in item.get('existing_receipt_pins', []):
            pin = record['receipt']
            watch(pin['path'], pin)
            seal = read_json(pin['path'])
            need(seal['module'] == module and seal['mode'] == record['mode']
                 and seal['status'] == 'succeeded' and same(seal['source'], source)
                 and same(seal['object'], obj), 'Row000 accepted seal differs')
        rel = module.replace('.', '/')
        members.append({'member': 'objects/' + rel + '.olean', 'kind': 'object',
                        'module': module, 'original': obj})
        if item['include_source_body']:
            members.append({'member': 'sources/' + rel + '.lean', 'kind': 'source',
                            'module': module, 'original': source})
        module_records.append({'module': module, 'kind': item['kind'], 'source': source,
                               'object': obj, 'sidecars': [],
                               'source_body_included': item['include_source_body'],
                               'accepted_object_candidates': item['object_candidates']})
    members.sort(key=lambda row: row['member'])
    need(len(members) == 203 and len({row['member'] for row in members}) == 203,
         'Wrong payload inventory')
    out = canonical(root / request['capsule_name'])
    out.mkdir(exist_ok=False)
    script_pin = fp(Path(__file__).absolute())
    manifest = {'schema': 'p26_minimal_p3_missing189_object_capsule_v1',
                'object_count': 189, 'source_body_count': 14, 'sidecar_count': 0,
                'payload_file_count': 203, 'modules': module_records, 'members': members,
                'source_body_modules': request['source_body_modules'],
                'input_source_manifest': request['input_source_manifest'],
                'input_supplier_delta': request['input_supplier_delta'],
                'builder': script_pin, 'request': fp(args.request),
                'receipt_validation': {'C_prefix': prefix, 'generic': generic},
                'compiler_or_proof_commands_executed': False,
                'row001_files_accessed': False, 'receipt_or_log_bodies_included': False}
    manifest_data = body(manifest)
    manifest_path = out / 'MANIFEST.json'
    write_new(manifest_path, manifest_data)
    archive = out / 'objects-and-missing-sources.tar.xz'
    print(json.dumps({'phase': 'compressing', 'preset': 6,
                      'object_bytes': sum(row['object']['bytes'] for row in module_records),
                      'source_body_bytes': sum(row['original']['bytes'] for row in members if row['kind'] == 'source'),
                      'payload_files': 203}), flush=True)
    with archive.open('xb') as raw:
        with lzma.LZMAFile(raw, mode='wb', format=lzma.FORMAT_XZ, preset=6) as compressed:
            with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.PAX_FORMAT) as tar:
                for member in members:
                    info = tarfile.TarInfo(member['member'])
                    info.size, info.mode, info.mtime = member['original']['bytes'], 0o444, 0
                    with canonical(member['original']['path']).open('rb') as incoming:
                        tar.addfile(info, incoming)
                info = tarfile.TarInfo('MANIFEST.json')
                info.size, info.mode, info.mtime = len(manifest_data), 0o444, 0
                tar.addfile(info, io.BytesIO(manifest_data))
    expected = {row['member']: row['original'] for row in members}
    expected['MANIFEST.json'] = {'bytes': len(manifest_data),
                                 'sha256': hashlib.sha256(manifest_data).hexdigest()}
    seen, readback_bytes = set(), 0
    with tarfile.open(archive, mode='r:xz') as tar:
        for member in tar:
            name = member.name
            rel = PurePosixPath(name)
            need(member.isfile() and name not in seen and name in expected
                 and not rel.is_absolute() and '..' not in rel.parts,
                 'Invalid/duplicate/unexpected archive member: ' + name)
            wanted = expected[name]
            need(member.size == wanted['bytes'], 'Archive member size differs: ' + name)
            h, size = hashlib.sha256(), 0
            with tar.extractfile(member) as incoming:
                for block in iter(lambda: incoming.read(1024 * 1024), b''):
                    h.update(block)
                    size += len(block)
            need(size == wanted['bytes'] and h.hexdigest() == wanted['sha256'],
                 'Archive member digest differs: ' + name)
            seen.add(name)
            readback_bytes += size
    need(seen == set(expected) and len(seen) == 204, 'Incomplete readback inventory')
    for path, pin in WATCHED.items():
        need(fp(path) == pin, 'Input changed after packing: ' + path)
    summary = {'schema': 'p26_minimal_missing189_capsule_summary_v1',
               'status': 'PASS_EXACT_MINIMAL_CAPSULE_READBACK', 'archive': fp(archive),
               'manifest': fp(manifest_path), 'builder': script_pin, 'request': fp(args.request),
               'object_count': 189, 'source_body_count': 14, 'sidecar_count': 0,
               'payload_members': 203, 'archive_members': 204,
               'payload_bytes': sum(row['original']['bytes'] for row in members),
               'object_bytes': sum(row['object']['bytes'] for row in module_records),
               'source_body_bytes': sum(row['original']['bytes'] for row in members if row['kind'] == 'source'),
               'readback_member_bytes': readback_bytes, 'all_archive_members_size_sha256_verified': True,
               'watched_original_files_unchanged_after_pack': len(WATCHED),
               'prefix_accepted_rows': list(range(98, 107)), 'prefix_receipts_validated': 27,
               'prefix_complete_owned_declarations': 2628, 'generic_receipts_validated': 3,
               'prefix_object_pins': [row['object'] for row in prefix['rows']],
               'compression': 'XZ / LZMA2 preset 6, single stream',
               'elapsed_seconds': round(time.monotonic() - started, 3),
               'compiler_or_proof_commands_executed': False,
               'row001_files_accessed': False, 'old_files_written': False,
               'receipt_or_log_bodies_included': False,
               'capsule_role': 'Exact object/source transport only; original accepted evidence remains at its original P1 locations.'}
    write_new(out / 'SUMMARY.json', body(summary))
    print(json.dumps(summary, sort_keys=True, separators=(',', ':')), flush=True)


if __name__ == '__main__':
    main()
