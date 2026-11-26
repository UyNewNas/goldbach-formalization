#!/usr/bin/env python3
"""Run frozen Cell01 owners in order; accepted suppliers and stages are never rerun."""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import io
import json
import os
import re
import sys
import tarfile
import uuid

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
VENDOR = {
    'GenericFloor_verify_v2.py': 'c79685cd3a5d10ff29a34eb335720c6cda52316028a8c5691074900652058965',
    'evidence_store.py': 'ec28ae1dc08266fd38fd4d154b8812b1e99e298685d3e61c21cfbc38fa528c32',
    'Cell00OriginalFloor_continue.py': '3bc31712aa136963335b2b1d1ab707fbcd4388e3b08c028fbfaabffb810d2a96',
    'export_cell01_row000.py': '4113667629d137e0f47b73b4551710380fb5a9c123a21b9853f352ae62869c07',
}


def load_vendor(filename):
    path = HERE / 'vendor' / filename
    if hashlib.sha256(path.read_bytes()).hexdigest() != VENDOR[filename]:
        raise RuntimeError('Changed reviewed helper: ' + filename)
    spec = importlib.util.spec_from_file_location('p26_family_' + path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


E = load_vendor('evidence_store.py')
V = load_vendor('GenericFloor_verify_v2.py')
SHARED = load_vendor('Cell00OriginalFloor_continue.py')
OWNED = load_vendor('export_cell01_row000.py')
need, canonical, within, disjoint = E.need, E.canonical, E.within, E.disjoint
fp, same, read, pinned = E.fp, E.same, E.read, E.pinned
MODES = ('normal', 'kernel', 'owned')
SOURCE_ARCHIVE = {'bytes': 122656, 'sha256': '457b87938ea4f363ab9ef8a6049173c5577f922bd5a133213ccfdd026001dce5'}
SOURCE_MANIFEST = {'bytes': 406865, 'sha256': 'b5fa17d1eaeaaf0a40bb5cf8aa8b9b1fd0fd449be24e103eea2e838993c42cdc'}
ROW000 = 'ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge'
ALLOWED = E.ALLOWED_AXIOMS
INTERFACE = 'ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface'
FAMILY_ORDER = [INTERFACE, *['ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock%03d_%03d' % (n, n + 15)
                for n in range(0, 144, 16)], 'ImbalancedChen.P2OriginalSaving19Cell01AllOriginalFloorBridge']
PILOT_CODE = {'bytes': 1265, 'sha256': '93dc12100f58e29cfe32cfd66b22c2333e9866cf8f5558aa8be06f62327b2c84'}
ROW001_RECEIPTS = {
    'normal': 'b3f8c1335e97725c4e09b1a6aec1d7a890272da18cf364aef689abbcc57ea627',
    'kernel': '0fc629ae4e2d811a1b5993e2bba07e82ef5579e0229b4a043afb21fb4642cace',
    'owned': 'b8eb4d0d0bff25b4e0761c2a42672ddf525a439b7b505e16ec8b01c2d90b0b62',
}
GENERIC = 'ImbalancedChen.P2OriginalSaving19OriginalFloorTransport'
GENERIC_CONTEXT = {'bytes': 19921, 'sha256': '3c16bf1d1df5be47d34de40756bc89514fd1e66ab1d3ed66215c14876db4fc28'}
GENERIC_OBJECT = {'bytes': 120672, 'sha256': '7affb7b9a94589a3463b00f84663c4c5fdc659445cd93769c00fc0a13edc4266'}
GENERIC_SEALS = {
    'normal': {'bytes': 2872, 'sha256': '800f8ae831bbcfe9478e7cc8334a870ce05b293d7b90d932805d99f2579da226'},
    'kernel': {'bytes': 2787, 'sha256': 'd0f2f9b0cc796755c4a6ba8ccc656f5386de16be5da160cbe27647898997073d'},
    'owned': {'bytes': 3405, 'sha256': '29663c4f100c88f23f0c76db96a4febb97786f801f1fa4f12a00050a4f599157'},
}


def write(stage, path, value):
    E.write_new(stage, path, value)
    return fp(path)


def keep(stage, path, value):
    if Path(path).exists():
        need(read(path) == value, 'Frozen metadata changed: ' + str(path))
        return fp(path)
    return write(stage, path, value)


def relative(module, suffix='.olean'):
    return V.module_relative(module, suffix)


def stem(module):
    return module.split('.')[-1]


def execution_environment(run):
    return {'PATH': str(Path(run['lean']).parent) + ':/usr/bin:/bin', 'LEAN_PATH': run['LEAN_PATH'],
            'LEAN_NUM_THREADS': '1', 'OMP_NUM_THREADS': '1', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}


def preserve_failed_normal(stage, attempt, module, folder, obj):
    """Keep known failed outputs out of the accepted namespace; never touch a success."""
    result_path = within(stage, folder / 'result.json')
    if not result_path.exists():
        return []
    result = read(result_path)
    need(result.get('status') != 'succeeded' and result.get('exit_code') != 0 and
         result.get('mode') == 'normal' and result.get('module') == module and
         result.get('object_before') is None, 'Failed-output preservation cannot touch successful evidence')
    saved = []
    for source in [obj, *V.sidecar_paths(obj)]:
        if source.exists():
            original = fp(within(stage, source, True))
            destination = within(stage, stage / 'rejected-objects' / attempt.name / stem(module) / source.name)
            destination.parent.mkdir(parents=True, exist_ok=True)
            need(not destination.exists(), 'Refusing to replace preserved failed output')
            os.rename(source, destination)
            saved.append({'original': original, 'preserved': pinned(destination, original)})
    if saved:
        write(stage, attempt / 'FAILED_NORMAL_OUTPUTS.json', {'status': 'FAILED_UNACCEPTED_BYTES_PRESERVED',
              'module': module, 'result': fp(result_path), 'files': saved, 'accepted': False})
    return saved


def sidecar_signature(items):
    result = {}
    for item in items:
        name = Path(item['path']).name
        suffix = next((s for s in ('.olean.server', '.olean.private', '.ir') if name.endswith(s)), None)
        need(suffix is not None and suffix not in result, 'Unknown or duplicate object sidecar')
        result[suffix] = (item['bytes'], item['sha256'])
    return result


def source_catalog(root, archive, frozen):
    root, archive = canonical(root, True), canonical(archive, True)
    frozen.add(archive, SOURCE_ARCHIVE)
    manifest_pin = frozen.add(root / 'metadata/SOURCE_MANIFEST.json', SOURCE_MANIFEST)
    package = read(root / 'PACKAGE_MANIFEST.json')
    frozen.add(root / 'PACKAGE_MANIFEST.json')
    expected = {'PACKAGE_MANIFEST.json'}
    for row in package['files']:
        member = Path(row['member'])
        need(not member.is_absolute() and '..' not in member.parts and row['member'] not in expected,
             'Unsafe or duplicate source-package member')
        expected.add(row['member'])
        frozen.add(within(root, root / member, True), row)
    actual = set()
    for path in root.rglob('*'):
        canonical(path, True)
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
    need(actual == expected, 'Source extraction has missing or extra bodies')
    # The advertised archive must contain exactly the same regular payloads.
    seen = set()
    with tarfile.open(archive, 'r:xz') as tar:
        for member in tar:
            need(member.isfile() and member.name in expected and member.name not in seen,
                 'Source archive has an unsafe, duplicate, or nonregular member')
            seen.add(member.name)
            data = tar.extractfile(member).read()
            need(same({'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()},
                      fp(root / member.name)), 'Source extraction/archive mismatch')
    need(seen == expected, 'Incomplete source archive')
    catalog = read(manifest_pin['path'])
    targets = [row['module'] for row in catalog['targets']]
    rows = {row['module']: row for row in catalog['project_source_closure']}
    need(len(targets) == len(set(targets)) == 11 and len(rows) == 802 and
         catalog['old_supplier_count'] == 791, 'Wrong frozen eleven-owner family')
    order = [line.split() for line in (root / 'metadata/cloud_order.txt').read_text().splitlines()
             if line.strip() and not line.lstrip().startswith('#')]
    need(order == [[module, mode] for module in targets for mode in MODES], 'Wrong frozen proof order')
    return catalog, targets, rows


def closure(module, rows):
    found, active = set(), set()
    def visit(name):
        need(name in rows and name not in active, 'Missing or cyclic project source closure: ' + name)
        if name in found:
            return
        active.add(name)
        for parent in rows[name]['project_imports']:
            visit(parent)
        active.remove(name)
        found.add(name)
    visit(module)
    return found


def index_records(index, module):
    """A selected prefix cannot give acceptance to an unexecuted tail."""
    records = index.get('records')
    need(isinstance(records, list), 'Missing immutable acceptance index')
    if 'completed_rows' in index:
        completed = index['completed_rows']
        selected = index['selected_ordinals']
        need(completed == selected[:len(completed)] and len(completed) == len(set(completed)) and
             index.get('frozen_inputs_unchanged') is True, 'Invalid completed row prefix')
        expected = [('ImbalancedChen.P2OriginalSaving19Cell01Row%03dFinite' % n, mode)
                    for n in completed for mode in MODES]
        need([(r.get('module'), r.get('mode')) for r in records] == expected,
             'Acceptance index does not cover the exact completed row-major triples')
        if index.get('status') == 'BUDGET_PAUSE':
            need(index.get('batch_complete') is False and
                 index.get('remaining_ordinals') == selected[len(completed):], 'Invalid paused selection')
        else:
            need(index.get('status') == 'succeeded' and index.get('batch_complete') is True and
                 completed == selected, 'Incomplete successful finite selection')
    elif index.get('target_module') == E.ROW001:
        need(module == E.ROW001 and index.get('status') == 'succeeded' and index.get('original_ordinal') == 1 and
             index.get('accepted_targets') == 1 and index.get('frozen_inputs_unchanged') is True and
             [(r.get('module'), r.get('mode')) for r in records] == [(E.ROW001, m) for m in MODES],
             'Incomplete original row001 successful index')
    elif index.get('status') in {'PAUSED_ACCEPTED_PREFIX', 'PROOFS_ACCEPTED_EXPORT_PENDING',
                                 'PASS_CELL01_ORIGINAL_FLOOR_FAMILY_11'}:
        need(index.get('accepted_steps') == len(records) and 0 <= len(records) <= 33 and
             index.get('accepted_owners') == len(records) // 3 and
             [(r.get('module'), r.get('mode')) for r in records] ==
             [(m, mode) for m in FAMILY_ORDER for mode in MODES][:len(records)] and
             index.get('P2_6_complete_claimed') is False, 'Invalid imported family acceptance prefix')
        if index['status'] in {'PROOFS_ACCEPTED_EXPORT_PENDING', 'PASS_CELL01_ORIGINAL_FLOOR_FAMILY_11'}:
            need(len(records) == 33, 'Full-family success requires all 33 accepted steps')
    else:
        need(index.get('status') in {'PASS_CELL01_ROW000_ORIGINAL_FLOOR',
             'PASS_GENERIC_ORIGINAL_FLOOR_TRANSPORT', 'PASS_OWNER_NORMAL_KERNEL_FULL_OWNED',
             'PASS_CELL01_ORIGINAL_FLOOR_FAMILY_11'}, 'Unrecognized accepted historical index')
    selected = [r for r in records if r.get('module', index.get('module', module)) == module]
    need([r['mode'] for r in selected] == list(MODES), 'Missing or duplicate indexed supplier modes')
    result = []
    for row in selected:
        keys = [k for k in ('receipt', 'reused_successful_receipt') if k in row]
        need(len(keys) == 1 and row.get('status', 'succeeded') == 'succeeded', 'Ambiguous or failed indexed step')
        result.append({'mode': row['mode'], 'receipt': row[keys[0]]})
    return result


def old_chain(provenance, module, source, obj, runtime, store, rows):
    """Read original raw bodies; never rewrite their paths and never invoke Lean."""
    index = store.json(provenance['index'])
    expected = index_records(index, module)
    need(provenance['records'] == expected, 'Supplier chains differ from immutable acceptance index')
    run = store.json(provenance['run'])
    input_ref = provenance['input']
    inputs = store.json(input_ref)
    need(run.get('inputs', run.get('input_fingerprints')) == input_ref, 'Historical input/run binding differs')
    imported_context = None
    for record in expected:
        mode = record['mode']
        seal = store.json(record['receipt'])
        result_ref = seal.get('command_result', record['receipt'])
        result = store.json(result_ref)
        command_ref = result['command']
        command = store.json(command_ref)
        log_ref = seal.get('log', result['log'])
        text = store.text(log_ref)
        need(seal.get('status') == result.get('status') == 'succeeded' and
             result.get('exit_code') == 0 and result.get('error') is None and
             not result.get('timed_out', False) and not result.get('validation_error'), 'Failed historical command')
        need(seal['module'] == result['module'] == module and seal['mode'] == result['mode'] == mode and
             same(seal['source'], source) and same(seal.get('object', result.get('object')), obj),
             'Historical source/object/module identity conflict')
        need(result['log'] == log_ref and all(result.get(k) == v for k, v in command.items()),
             'Broken historical command/result/log chain')
        need(seal.get('command', command_ref) == command_ref and
             ('context' not in command or command['context'] == seal.get('context')),
             'Historical accepted seal/command context differs')
        need(command['module'] == module and command['mode'] == mode and
             same(command['source'], source) and command['input_fingerprints'] == input_ref,
             'Historical command input provenance differs')
        context_ref = seal.get('context', provenance['run'])
        context = store.json(context_ref)
        actual_run = store.json(seal['run']) if 'run' in seal else run
        need(actual_run.get('stage_context', context_ref) == context_ref and
             context.get('inputs', context.get('input_fingerprints')) == input_ref,
             'Historical context/run chain differs')
        for key in ('lean_binary', 'leanchecker_binary'):
            need(same(context[key], runtime[key]), 'Historical compiler/checker bytes differ')
        need(command['LEAN_PATH'] == context['LEAN_PATH'] and
             command.get('cwd', context.get('cwd', context.get('project'))) ==
             context.get('project', context.get('cwd')), 'Historical working directory/search path differs')
        argv = command['argv']
        if mode == 'kernel':
            need(argv == [context['leanchecker_binary']['path'], '--verbose', module] and
                 same(command['object_before'], obj), 'Historical check is not exact stock leanchecker')
            need(text.strip() == 'replaying ' + module, 'Historical kernel log identifies another object')
        else:
            need(argv[0] == context['lean_binary']['path'] and len(argv) >= 6 and argv[1] == '-j1' and
                 re.fullmatch(r'-M[1-9][0-9]*', argv[2]) and
                 argv[3:5] == ['-DmaxRecDepth=1000000', '-DmaxHeartbeats=0'],
                 'Unexpected historical Lean command')
            if mode == 'normal':
                need(len(argv) == 8 and argv[-3:] == ['-o', seal['object']['path'],
                     module.replace('.', '/') + '.lean'] and command['object_before'] is None,
                     'Historical normal source/output differs')
                axioms = {a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                          for a in group.split(',') if a.strip()}
                need(axioms <= ALLOWED, 'Forbidden historical normal axiom')
            else:
                audit_ref = seal.get('audit_source', seal.get('audit', command.get('audit_source')))
                need(audit_ref is not None and len(argv) == 6 and argv[-1] == audit_ref['path'] and
                     same(command['object_before'], obj), 'Historical owned audit command differs')
                store.resolve(audit_ref)
                inventory = OWNED.parse_owned(text, module)
                owned_ref = seal.get('owned_declarations', result.get('owned_declarations'))
                need(owned_ref is not None and inventory == store.json(owned_ref),
                     'Historical complete inventory/type/axiom evidence differs')
                names = V.parsed_imports(text, closure(module, rows))
                if 'module_byte_context' in seal:
                    byte_rows = store.json(seal['module_byte_context'])
                    need({r['module'] for r in byte_rows} == set(names) and len(byte_rows) == len(names),
                         'Historical imported-module byte inventory differs')
                    imported_context = seal['module_byte_context']
        for key in ('before', 'after'):
            if key in seal:
                check = store.json(seal[key])
                need(check['status'] == 'ALL_FROZEN_BYTES_UNCHANGED' and check['context'] == context_ref and
                     check['inputs'] == input_ref and check['runtime_trees'] == context['runtime_trees'],
                     'Historical frozen-byte seal is incomplete')
    return {'module': module, 'source': source, 'object': obj, 'records': expected,
            'index': provenance['index'], 'run': provenance['run'], 'input': input_ref,
            'module_byte_context': imported_context,
            'status': 'EXACT_EXISTING_THREE_MODE_CHAIN_RECHECKED'}, inputs


class Row001InPlaceStore(E.EvidenceStore):
    """Read protected raw bodies only at their original same-host paths; never relocate them."""
    def resolve(self, original):
        original = E.identity(original)
        if not E.row001_body_allowed(original['path']):
            path = canonical(original['path'], True)
            need(path.is_relative_to(Path(E.ROW001_ORIGIN)) and not path.name.endswith(('.tar', '.xz', '.zip')),
                 'Only original same-host row001 receipt bodies may be read')
            self.allowed_current(path)
            self.frozen.add(path, original)
            return path
        return super().resolve(original)


def make_store(stage, join, frozen):
    in_place = [row for row in join['suppliers'] if row.get('kind') == 'same_host_row001']
    need(not in_place or len(in_place) == 1 and in_place[0]['module'] == E.ROW001 and
         in_place[0]['provenance'].get('in_place') is True, 'Invalid same-host row001 declaration')
    store_type = Row001InPlaceStore if in_place else E.EvidenceStore
    store = store_type(stage, join['read_roots'], frozen)
    for binding in join.get('bindings', []):
        store.register(binding['original'], binding['current_path'])
    return store


def verify_row001_in_place(row, runtime, store, rows):
    """No archive opens, copies, exports, subprocesses, or new proof commands."""
    need(type(store) is Row001InPlaceStore and row['module'] == E.ROW001, 'Same-host exception is row001 only')
    origin = Path(E.ROW001_ORIGIN)
    expected_source = origin / 'project' / relative(E.ROW001, '.lean')
    expected_object = origin / 'objects' / relative(E.ROW001)
    need(row['source']['path'] == str(expected_source) and row['object']['path'] == str(expected_object) and
         row['source']['sha256'] == E.ROW001_SOURCE_SHA and row['object']['sha256'] == E.ROW001_OBJECT_SHA,
         'Row001 same-host source/object must be at the independently accepted original paths')
    provenance = row['provenance']
    attempt = origin / 'verification/20261126-row001-v1'
    need(provenance['run']['path'] == str(attempt / 'RUN.json') and
         provenance['index']['path'] == str(attempt / 'SUCCESS.json') and
         Path(provenance['input']['path']).is_relative_to(origin), 'Row001 original attempt/input locator differs')
    for record in provenance['records']:
        need(record['receipt']['sha256'] == ROW001_RECEIPTS[record['mode']], 'Changed original row001 receipt')
    validation, inputs = old_chain(provenance, E.ROW001, row['source'], row['object'], runtime, store, rows)
    run = store.json(provenance['run'])
    need(run['accepted_supplier_count'] == 399 and run['full_supplier_kernel_closed'] is True and
         run['cloud_source_generation'] is False and run['suppliers_recompiled'] is False,
         'Original row001 supplier boundary differs')
    supplier, installation = store.json(run['supplier_manifest']), store.json(run['supplier_installation'])
    suppliers = {item['module']: item for item in supplier['suppliers']}
    entries = {(item['module'], item['kind']): item for item in installation['entries']}
    need(len(suppliers) == len(supplier['suppliers']) == 399 and supplier['normal_only_suppliers'] == [] and
         len(entries) == len(installation['entries']) == 798 and installation['supplier_modules'] == 399 and
         installation['suppliers_recompiled'] is False, 'Incomplete original row001 supplier installation')
    snapshots = {ref['path']: ref for ref in inputs['files']}
    need(len(snapshots) == len(inputs['files']), 'Duplicate original row001 input identity')
    count = 0
    for module, item in suppliers.items():
        need(module in rows and same(item['source'], rows[module]), 'Row001 same-name supplier source conflict')
        for kind in ('source', 'object'):
            entry = entries[(module, kind)]
            for key in ('source', 'installed'):
                ref = entry[key]
                need(same(ref, item[kind]) and same(snapshots.get(ref['path']), ref),
                     'Original row001 supplier installation/snapshot mismatch')
                store.allowed_current(ref['path'])
                store.frozen.add(ref['path'], ref)
                count += 1
    need(count == 1596, 'Incomplete same-host live supplier pair verification')
    for ref in inputs['files']:
        store.allowed_current(ref['path'])
        store.frozen.add(ref['path'], ref)
    def original_member(ref):
        member = Path(ref['archive_member'])
        need(not member.is_absolute() and '..' not in member.parts, 'Unsafe row001 historical addendum member')
        path = within(origin, origin / member, True)
        store.frozen.add(path, ref)
        return read(path)
    completion = original_member(supplier['kernel_completion'])
    prior = original_member(supplier['kernel_receipt'])
    result = original_member(supplier['kernel_result'])
    recurrence = suppliers['ImbalancedChen.P2Winner9HomogeneousRecurrence']
    need(completion['supplier_kernel_closed_in_combined_evidence'] is True and
         completion['original_P3_records_unchanged'] is True and
         completion['remaining_pending_supplier_kernel_modules'] == [] and
         all(same(completion[k], recurrence[k]) and same(prior[k], recurrence[k]) for k in ('source', 'object')),
         'Original row001 historical same-byte addendum is incomplete')
    need(prior['status'] == result['status'] == 'succeeded' and result['exit_code'] == 0 and
         same(prior['command_result'], supplier['kernel_result']) and
         same(prior['log'], supplier['kernel_log']) and same(result['log'], supplier['kernel_log']),
         'Original row001 historical kernel result/log binding differs')
    log_member = Path(supplier['kernel_log']['archive_member'])
    need(not log_member.is_absolute() and '..' not in log_member.parts, 'Unsafe historical kernel log member')
    store.frozen.add(within(origin, origin / log_member, True), supplier['kernel_log'])
    owned_result = store.json(provenance['records'][2]['receipt'])
    inventory = OWNED.parse_owned(store.text(owned_result['log']), E.ROW001)
    need(inventory['owned_declaration_count'] == 292, 'Original row001 complete declaration count differs')
    return {**validation, 'status': 'EXACT_SAME_HOST_ROW001_CHAIN_RECHECKED',
            'supplier_modules': 399, 'live_source_object_pin_checks': count,
            'owned_declarations': 292, 'axioms_union': inventory['axioms_union'],
            'receipt_bodies_checked_same_host': True, 'receipt_bodies_exported': False,
            'archive_opened': False, 'Lean_commands': 0}


def validate_join(stage, join, module, rows, targets, runtime, frozen, canonical_authority=None):
    need(join['schema'] == 'p26_family_owner_join_v1' and join['module'] == module,
         'Wrong per-owner supplier join')
    required = closure(module, rows) - set(targets)
    supplied = {r['module']: r for r in join['suppliers']}
    need(len(supplied) == len(join['suppliers']) and set(supplied) == required,
         'Join must contain the exact actual old-supplier closure of this owner')
    store = make_store(stage, join, frozen)
    canonical_inputs, validations = {}, []
    for name, group in join.get('canonical_contexts', {}).items():
        need(canonical_authority is not None and all(same(group[key], canonical_authority[old]) for key, old in
             [('run', 'original_RUN'), ('input', 'original_INPUT'), ('result', 'original_RESULT')]),
             'Canonical authority differs from the fixed source-package 23rd evidence pins')
        old_result = store.json(group['result'])
        need(old_result['status'] == 'PASS_CELL01_ROW000_ORIGINAL_FLOOR', 'Wrong original canonical authority')
        provenance = {**group, 'index': group['result']}
        validation, inputs = old_chain(provenance, ROW000, old_result['source'], old_result['object'],
                                       runtime, store, rows)
        need(len(inputs['canonical_modules']) == 1111 and group.get('closure_refs'),
             'Canonical original closure/addenda are missing')
        original_files = inputs['files']
        for ref in group['closure_refs']:
            need(any(same(ref, item) and ref['path'] == item['path'] for item in original_files),
                 'Unbound canonical closure/addendum locator')
            store.resolve(ref)
        addendum = inputs['supplier_kernel_addendum']
        need(addendum in group['closure_refs'], 'Historical same-byte kernel addendum must be retained')
        completion = store.json(addendum)
        need(completion['supplier_kernel_closed_in_combined_evidence'] is True and
             completion['original_P3_records_unchanged'] is True and
             completion['remaining_pending_supplier_kernel_modules'] == [], 'Incomplete canonical kernel closure')
        canonical_inputs[name] = inputs
        validations.append(validation)
    for name in sorted(required):
        row = supplied[name]
        need(same(row['source'], rows[name]), 'Same-name source conflict: ' + name)
        for ref in [row['source'], row['object'], *row['sidecars']]:
            store.allowed_current(ref['path'])
            frozen.add(ref['path'], ref)
        actual_sidecars = [fp(p) for p in V.sidecar_paths(Path(row['object']['path'])) if p.exists()]
        need(sidecar_signature(actual_sidecars) == sidecar_signature(row['sidecars']),
             'Supplier has missing or unpinned sidecars: ' + name)
        kind = row['kind']
        if kind == 'canonical':
            inputs = canonical_inputs[row['canonical_context']]
            original = inputs['canonical_modules'][name]
            union = [r for r in inputs['project_object_union'] if r['module'] == name]
            objects = [r for r in union if r['path'].endswith('.olean')]
            need(len(objects) == 1 and same(row['source'], original['source']) and
                 same(row['object'], original['object']) and same(objects[0], row['object']) and
                 sidecar_signature([r for r in union if r is not objects[0]]) == sidecar_signature(row['sidecars']),
                 'Canonical source/object/union-sidecar conflict: ' + name)
        elif kind == 'three_mode':
            need(name != E.ROW001, 'Row001 is remote-summary-only')
            if name == GENERIC:
                need(same(row['object'], GENERIC_OBJECT) and
                     [r['mode'] for r in row['provenance']['records']] == list(MODES) and
                     all(same(r['receipt'], GENERIC_SEALS[r['mode']]) and
                         same(store.json(r['receipt'])['context'], GENERIC_CONTEXT)
                         for r in row['provenance']['records']),
                     'Generic supplier differs from the actual accepted generic-v2-r14 history')
            validation, _ = old_chain(row['provenance'], name, row['source'], row['object'],
                                      runtime, store, rows)
            validations.append(validation)
        elif kind == 'remote_verified_predecessor':
            validations.append(E.verify_row001_remote(row['provenance'], rows[name], row['object'],
                row['sidecars'], runtime['leanchecker_binary'], store))
        elif kind == 'same_host_row001':
            validations.append(verify_row001_in_place(row, runtime, store, rows))
        else:
            raise RuntimeError('Unknown supplier acceptance kind: ' + str(kind))
    need(any(same(item.get('module_byte_context'), runtime['accepted_module_context']) for item in validations),
         'External runtime inventory is not bound to an accepted owned chain')
    return supplied, validations


def validate_runtime(runtime, frozen, stage):
    need(runtime['schema'] == 'p26_family_runtime_v1' and runtime.get('mode', 'complete_tree') == 'complete_tree',
         'Only the reviewed complete-tree runtime mode is supported')
    roots = [canonical(r, True) for r in runtime['runtime_roots']]
    lib = canonical(Path(runtime['lean_binary']['path']).parent.parent / 'lib', True)
    tree_roots = [canonical(row['root'], True) for row in runtime['runtime_trees']]
    need(set(roots + [lib]) <= set(tree_roots), 'Every search root and toolchain lib must have a full-tree seal')
    for root in set(roots + tree_roots):
        disjoint(stage, root)
        need(not (root / 'ImbalancedChen').exists(), 'Unbounded project namespace fallback')
    for key in ('lean_binary', 'leanchecker_binary'):
        disjoint(stage, Path(runtime[key]['path']).parent.parent)
        frozen.add(runtime[key]['path'], runtime[key])
    for ref in runtime.get('native_library_files', []):
        disjoint(stage, ref['path'])
        frozen.add(ref['path'], ref)
    need([V.tree_signature(root) for root in tree_roots] == runtime['runtime_trees'],
         'Runtime full-tree identity changed')
    ext = {row['module']: row for row in runtime['external_modules']}
    need(len(ext) == len(runtime['external_modules']) and all(not name.startswith('ImbalancedChen.') for name in ext),
         'Duplicate/project runtime module')
    for row in ext.values():
        for ref in [row['object'], *row['sidecars']]:
            frozen.add(ref['path'], ref)
    accepted = frozen.add(runtime['accepted_module_context']['path'], runtime['accepted_module_context'])
    old = {row['module']: row for row in read(accepted['path']) if not row['module'].startswith('ImbalancedChen.')}
    need(all(name in old and same(row['object'], old[name]['object']) and
             sidecar_signature(row['sidecars']) == sidecar_signature(old[name]['sidecars'])
             for name, row in ext.items()), 'Runtime modules are not the same accepted imported bytes')
    expected = runtime['external_imports']
    need(len(expected) == len(set(expected)) and set(expected) <= set(ext), 'Incomplete frozen external import list')
    actual = V.module_byte_context(list(ext), [*roots, lib / 'lean'])
    need(actual == [ext[name] for name in sorted(ext)], 'Runtime provider precedence or module sidecars differ')
    return roots, lib


def source_install(stage, root, catalog, targets, frozen):
    for row in catalog['targets']:
        destination = stage / 'project' / relative(row['module'], '.lean')
        V.install_link(stage, root / 'sources' / row['path'], destination, row)
        frozen.add(destination, row)
    for row in catalog['full_owned_audits']:
        destination = stage / 'audit' / (stem(row['module']) + '.lean')
        V.install_link(stage, root / 'metadata/audits' / Path(row['path']).name, destination, row)
        frozen.add(destination, row)


def load_context(stage, module, rows, targets, runtime, frozen):
    path = stage / 'contexts' / (stem(module) + '.json')
    context = read(path)
    need(context['schema'] == 'p26_family_owner_context_v1' and context['module'] == module and
         context['stage'] == str(stage) and context['project'] == str(stage / 'project') and
         context['objects'] == str(stage / 'objects') and same(context['source'], rows[module]) and
         context['source'] == fp(stage / 'project' / relative(module, '.lean')) and
         context['runtime'] == runtime and context['project_modules'] == sorted(closure(module, rows)),
         'Existing owner context changed; restore its exact input snapshot')
    expected_audit = stage / 'audit' / (stem(module) + '.lean')
    need(context['audit'] == fp(expected_audit), 'Existing owner audit changed')
    frozen.add(path)
    frozen.add(context['inputs']['path'], context['inputs'])
    snapshot = read(context['inputs']['path'])
    need(snapshot['supplier_modules'] == sorted(closure(module, rows) - set(targets)),
         'Existing owner supplier closure differs')
    for root in snapshot['read_roots']:
        disjoint(stage, root)
    for ref in snapshot['files']:
        p = canonical(ref['path'], True)
        need(p.is_relative_to(stage) or any(p.is_relative_to(canonical(r)) for r in snapshot['read_roots']),
             'Historical frozen input escapes its declared provider roots')
        frozen.add(p, ref)
    return context, fp(path)


def create_context(stage, module, join_path, root, rows, targets, runtime, runtime_roots, lib, frozen):
    join_path = canonical(join_path, True)
    join = read(join_path)
    disjoint(stage, join_path)
    frozen.add(join_path)
    supplied, validations = validate_join(stage, join, module, rows, targets, runtime, frozen,
                                          read(root / 'metadata/SUPPLIER_DELTA.json'))
    installed = []
    for name, row in sorted(supplied.items()):
        for ref, destination in [(row['source'], stage / 'project' / relative(name, '.lean')),
                                  (row['object'], stage / 'objects' / relative(name))]:
            installed.append(V.install_link(stage, ref['path'], destination, ref))
            frozen.add(destination, ref)
        for side in row['sidecars']:
            suffix = next(s for s in ('.olean.server', '.olean.private', '.ir') if side['path'].endswith(s))
            destination = stage / 'objects' / relative(name, suffix)
            installed.append(V.install_link(stage, side['path'], destination, side))
            frozen.add(destination, side)
    # Every source is checked at the exact pinned bytes; source manifests are not acceptance.
    for name in supplied:
        text = (stage / 'project' / relative(name, '.lean')).read_text()
        imports = set(re.findall(r'^import\s+(ImbalancedChen\.[A-Za-z0-9_.]+)', text, re.M))
        need(imports == set(rows[name]['project_imports']), 'Supplier source closure disagrees with source pins')
    roots = [*join['read_roots'], str(HERE), str(root)]
    for ref in frozen.files.values():
        path = Path(ref['path'])
        if path.is_relative_to(stage) or any(path.is_relative_to(Path(provider)) for provider in roots):
            continue
        provider = path.parent if not stage.is_relative_to(path.parent) else path
        roots.append(str(provider))
    roots = list(dict.fromkeys(roots))
    for provider in roots:
        disjoint(stage, provider)
    snapshot = {'schema': 'p26_family_owner_inputs_v1', 'module': module, 'join': fp(join_path),
        'read_roots': roots, 'supplier_modules': sorted(supplied), 'suppliers': list(supplied.values()),
        'supplier_validation': validations, 'installed_files': installed,
        'files': [frozen.files[k] for k in sorted(frozen.files)], 'supplier_commands': 0}
    input_pin = write(stage, stage / 'inputs' / (stem(module) + '.json'), snapshot)
    source = fp(stage / 'project' / relative(module, '.lean'))
    audit = fp(stage / 'audit' / (stem(module) + '.lean'))
    context = {'schema': 'p26_family_owner_context_v1', 'module': module, 'stage': str(stage),
        'executor_generation': 2,
        'project': str(stage / 'project'), 'objects': str(stage / 'objects'), 'source': source, 'audit': audit,
        'inputs': input_pin, 'runtime': runtime, 'lean_binary': runtime['lean_binary'],
        'leanchecker_binary': runtime['leanchecker_binary'], 'runtime_trees': runtime['runtime_trees'],
        'runtime_roots': [r['root'] for r in runtime['runtime_trees']],
        'project_modules': sorted(closure(module, rows)),
        'new_dependencies': [name for name in targets if name != module and name in closure(module, rows)],
        'module_search_roots': list(map(str, [stage / 'objects', *runtime_roots, lib / 'lean'])),
        'LEAN_PATH': os.pathsep.join(map(str, [stage / 'objects', *runtime_roots])),
        'external_imports': join.get('external_imports', runtime['external_imports']),
        'source_manifest': fp(root / 'metadata/SOURCE_MANIFEST.json'),
        'source_archive': SOURCE_ARCHIVE, 'new_owner_count': 11, 'P2_6_complete_claimed': False}
    need(set(context['external_imports']) <= {r['module'] for r in runtime['external_modules']},
         'Owner external allowlist escapes frozen runtime inventory')
    context_pin = write(stage, stage / 'contexts' / (stem(module) + '.json'), context)
    frozen.add(input_pin['path'], input_pin)
    frozen.add(context_pin['path'], context_pin)
    return context, context_pin


def prerequisite_records(module, mode, context, accepted):
    wanted = [(name, m) for name in context['new_dependencies'] for m in MODES]
    wanted += [(module, m) for m in MODES[:MODES.index(mode)]]
    need(all(key in accepted for key in wanted), 'New predecessor owner lacks a complete accepted triple')
    return [{'module': name, 'mode': m, 'receipt': accepted[(name, m)]} for name, m in wanted]


def check_imported_interface(stage, context, join, frozen):
    """Import only the frozen pilot's complete triple; no partially accepted foreign owner."""
    module = context['module']
    need(module == INTERFACE and context['new_dependencies'] == [],
         'Cross-stage imported owner is restricted to the independent interface pilot')
    owner = join['accepted_owner']
    need(owner['module'] == module and same(owner['source'], context['source']) and
         same(owner['audit'], context['audit']), 'Imported pilot source/audit conflict')
    store = make_store(stage, join, frozen)
    for ref in [owner['source'], owner['object'], *owner['sidecars']]:
        store.allowed_current(ref['path'])
        frozen.add(ref['path'], ref)
    need(sidecar_signature([fp(p) for p in V.sidecar_paths(Path(owner['object']['path'])) if p.exists()]) ==
         sidecar_signature(owner['sidecars']), 'Imported pilot sidecar inventory differs')
    provenance = owner['provenance']
    pinned(context['source_manifest']['path'], SOURCE_MANIFEST)
    source_rows = {row['module']: row for row in read(context['source_manifest']['path'])['project_source_closure']}
    validation, inputs = old_chain(provenance, module, owner['source'], owner['object'],
                                  context['runtime'], store, source_rows)
    code_ref = provenance['code_manifest']
    need(same(code_ref, PILOT_CODE) and any(ref == code_ref for ref in inputs['files']),
         'Imported pilot is not bound to the frozen reviewed pilot-v1 code')
    code = store.json(code_ref)
    code_root = Path(code_ref['path']).parent
    raw = {}
    def retain(ref):
        ref = E.identity(ref)
        current = store.resolve(ref)
        raw[(ref['path'], ref['bytes'], ref['sha256'])] = (ref, current)
    for key in ('index', 'run', 'input', 'code_manifest'):
        retain(provenance[key])
    for item in code['files']:
        member = Path(item['member'])
        need(not member.is_absolute() and '..' not in member.parts, 'Unsafe original pilot code member')
        ref = {'path': str(code_root / member), 'bytes': item['bytes'], 'sha256': item['sha256']}
        need(ref in inputs['files'], 'Original pilot code body is absent from the frozen input inventory')
        retain(ref)
    original_context = None
    for record in provenance['records']:
        retain(record['receipt'])
        seal = store.json(record['receipt'])
        prerequisites = [{'module': module, 'mode': prior['mode'], 'receipt': prior['receipt']}
                         for prior in provenance['records'][:MODES.index(record['mode'])]]
        need(same(seal['audit'], owner['audit']) and seal['prerequisites'] == prerequisites,
             'Imported pilot differs from its complete independent audit')
        command = store.json(seal['command'])
        need(command['prerequisites'] == prerequisites,
             'Imported pilot command declares another prerequisite context')
        original_context = store.json(seal['context'])
        need(original_context['source_archive'] == SOURCE_ARCHIVE and
             original_context['schema'] == 'p26_family_owner_context_v1' and
             original_context['project_modules'] == context['project_modules'] and
             set(original_context['external_imports']) == set(context['external_imports']) and
             original_context['new_owner_count'] == 11 and original_context['P2_6_complete_claimed'] is False,
             'Imported pilot source-family or actual import boundary differs')
        for key in ('run', 'context', 'command', 'command_result', 'log', 'before', 'after'):
            retain(seal[key])
        if record['mode'] == 'owned':
            retain(seal['owned_declarations'])
            retain(seal['module_byte_context'])
            historical = store.json(seal['module_byte_context'])
            names = [row['module'] for row in historical if row['module'] != module]
            actual = {row['module']: row for row in V.module_byte_context(names, context['module_search_roots'])}
            actual[module] = {'module': module, 'object': owner['object'], 'sidecars': owner['sidecars']}
            need(len(historical) == len(actual) and all(row['module'] in actual and
                 same(row['object'], actual[row['module']]['object']) and
                 sidecar_signature(row['sidecars']) == sidecar_signature(actual[row['module']]['sidecars'])
                 for row in historical), 'Imported pilot actual project/runtime bytes differ after relocation')
    return owner, validation, list(raw.values())


def import_interface(stage, context, context_pin, join_path, frozen):
    """Idempotently restore local anchors to an already accepted foreign triple."""
    join = read(join_path)
    owner, validation, raw = check_imported_interface(stage, context, join, frozen)
    folder = stage / 'imports' / FILENAME_INTERFACE
    mark = {'schema': 'p26_family_imported_owner_v1', 'module': INTERFACE, 'context': context_pin,
            'join': fp(join_path), 'original_validation': validation, 'source': context['source'],
            'audit': context['audit'], 'donor_object': owner['object'], 'donor_sidecars': owner['sidecars'],
            'new_proof_commands': 0}
    mark_pin = keep(stage, folder / 'IMPORT.json', mark)
    # The recovery marker precedes object installation. Re-running this import only
    # validates/copies existing accepted bytes; it never invokes any proof command.
    obj = stage / 'objects' / relative(INTERFACE)
    V.install_link(stage, owner['object']['path'], obj, owner['object'])
    for side in owner['sidecars']:
        suffix = next(s for s in ('.olean.server', '.olean.private', '.ir') if side['path'].endswith(s))
        V.install_link(stage, side['path'], stage / 'objects' / relative(INTERFACE, suffix), side)
    members = []
    for original, current in raw:
        name = original['sha256'] + '-' + Path(original['path']).name
        destination = folder / 'original-evidence' / name
        V.install_link(stage, current, destination, original)
        members.append({'original': original, 'current': fp(destination), 'role': 'accepted_new_owner_evidence'})
    relocation = keep(stage, folder / 'RELOCATION.json', {'schema': 'p26_imported_owner_relocation_v1', 'members': members})
    state = V.object_state(stage, obj)
    for ref in [state['object'], *state['sidecars']]:
        frozen.add(ref['path'], ref)
    for record in owner['provenance']['records']:
        mode = record['mode']
        seal = {'schema': 'p26_family_imported_step_v1', 'status': 'succeeded', 'module': INTERFACE,
                'mode': mode, 'source': context['source'], 'audit': context['audit'], 'object': state['object'],
                'object_sidecars': state['sidecars'], 'context': context_pin, 'import': mark_pin,
                'relocation': relocation, 'original_receipt': record['receipt'], 'new_proof_commands': 0}
        ref = keep(stage, folder / 'steps' / mode / 'ACCEPTED_STEP.json', seal)
        keep(stage, stage / 'accepted' / FILENAME_INTERFACE / (mode + '.json'),
             {'module': INTERFACE, 'mode': mode, 'receipt': ref})
    return mark_pin


FILENAME_INTERFACE = stem(INTERFACE)


def validate_imported_step(stage, module, mode, ref, context, context_pin):
    seal = read(ref['path'])
    need(module == INTERFACE and seal['status'] == 'succeeded' and seal['module'] == module and
         seal['mode'] == mode and seal['context'] == context_pin and seal['source'] == context['source'] and
         seal['audit'] == context['audit'] and seal['new_proof_commands'] == 0, 'Invalid imported pilot seal')
    for key in ('import', 'relocation'):
        pinned(within(stage, seal[key]['path'], True), seal[key])
    marker = read(seal['import']['path'])
    need(marker['context'] == context_pin and marker['module'] == INTERFACE, 'Imported pilot marker context differs')
    frozen = E.Frozen()
    frozen.add(marker['join']['path'], marker['join'])
    owner, validation, _ = check_imported_interface(stage, context, read(marker['join']['path']), frozen)
    need(validation == marker['original_validation'] and
         owner['provenance']['records'][MODES.index(mode)]['receipt'] == seal['original_receipt'],
         'Imported pilot original acceptance differs')
    for row in read(seal['relocation']['path'])['members']:
        pinned(within(stage, row['current']['path'], True), row['current'])
        need(same(row['original'], row['current']), 'Imported pilot raw body was rewritten')
    V.check_object(stage, stage / 'objects' / relative(module), seal['object'], seal['object_sidecars'])
    return seal


def validate_step(stage, module, mode, ref, context, context_pin, accepted):
    V.TARGET = module
    pinned(within(stage, ref['path'], True), ref)
    if read(ref['path']).get('schema') == 'p26_family_imported_step_v1':
        return validate_imported_step(stage, module, mode, ref, context, context_pin)
    obj = stage / 'objects' / relative(module)
    seal = V.validate_step(ref['path'], stage, context_pin, context['source'], context['audit'], obj, OWNED)
    need(seal['mode'] == mode, 'Accepted step is stored under another mode')
    expected = prerequisite_records(module, mode, context, accepted)
    command = read(seal['command']['path'])
    if context.get('executor_generation') == 2:
        need(command['execution_environment'] == execution_environment(read(seal['run']['path'])),
             'Accepted proof environment differs from the fixed command environment')
    need(seal['prerequisites'] == command['prerequisites'] == expected,
         'Accepted proof has different prerequisite seals')
    if mode == 'kernel':
        need(Path(seal['log']['path']).read_text().strip() == 'replaying ' + module,
             'Stock leanchecker log identifies another owner')
    if mode == 'owned':
        names = V.parsed_imports(Path(seal['log']['path']).read_text(), context['project_modules'])
        need({name for name in names if not name.startswith('ImbalancedChen.')} == set(context['external_imports']),
             'Actual external import inventory differs from frozen owner context')
        runtime = {row['module']: row for row in context['runtime']['external_modules']}
        for row in read(seal['module_byte_context']['path']):
            if not row['module'].startswith('ImbalancedChen.'):
                need(row == runtime[row['module']], 'Actual external provider bytes differ')
    return seal


def scan_history(stage, targets, contexts):
    candidates = {}
    def remember(module, mode, ref):
        need(module in targets and mode in MODES, 'Unknown accepted owner/mode')
        E.identity(ref)
        pinned(within(stage, ref['path'], True), ref)
        prior = candidates.setdefault((module, mode), ref)
        need(prior == ref, 'Multiple conflicting successful steps; restore original acceptance')
    for anchor in sorted((stage / 'accepted').glob('*/*.json')):
        value = read(canonical(anchor, True))
        need(anchor.parent.name == stem(value['module']) and anchor.name == value['mode'] + '.json',
             'Acceptance anchor filename differs')
        remember(value['module'], value['mode'], value['receipt'])
    for attempt in sorted((stage / 'attempts').glob('*')):
        canonical(attempt, True)
        need(attempt.is_dir(), 'Unexpected attempt entry')
        for owner in (attempt / 'steps').glob('*'):
            module = next((m for m in targets if stem(m) == owner.name), None)
            need(module is not None, 'Unknown historical owner directory')
            for mode in MODES:
                folder = within(stage, owner / mode)
                seal, raw = folder / 'ACCEPTED_STEP.json', folder / 'result.json'
                if seal.exists():
                    remember(module, mode, fp(seal))
                elif raw.exists():
                    result = read(raw)
                    if result.get('status') == 'succeeded' or (result.get('exit_code') == 0 and
                            result.get('error') is None and not result.get('timed_out', False)):
                        raise RuntimeError('RESTORE_SUCCESS_EVIDENCE_CHAIN: successful raw result has no accepted seal')
        for filename in ('RESULT.json', 'PROOF_RESULT.json'):
            path = attempt / filename
            if not path.exists():
                continue
            index = read(path)
            records = index.get('records', [])
            expected = [(m, mode) for m in targets for mode in MODES][:len(records)]
            need(isinstance(records, list) and len(records) <= 33 and
                 [(r['module'], r['mode']) for r in records] == expected, 'Malformed surviving accepted-record index')
            for row in records:
                remember(row['module'], row['mode'], row['receipt'])
            if index.get('status') == 'PASS_CELL01_ORIGINAL_FLOOR_FAMILY_11':
                need(len(records) == 33, 'Incomplete claimed family success')
    accepted = {}
    missing = False
    for module in targets:
        for mode in MODES:
            key = (module, mode)
            if key not in candidates:
                missing = True
                continue
            need(not missing and module in contexts, 'Acceptance is not a complete ordered prefix')
            context, context_pin = contexts[module]
            validate_step(stage, module, mode, candidates[key], context, context_pin, accepted)
            accepted[key] = candidates[key]
        obj = stage / 'objects' / relative(module)
        state = V.object_state(stage, obj)
        if (module, 'normal') not in accepted:
            need(state['object'] is None and not state['sidecars'],
                 'UNRECEIPTED_OBJECT: restoration required; refusing overwrite/recompile')
    for (module, mode), ref in accepted.items():
        keep(stage, stage / 'accepted' / stem(module) / (mode + '.json'),
             {'module': module, 'mode': mode, 'receipt': ref})
    return accepted


def recheck(stage, path, context, context_pin, frozen, targets, rows):
    frozen.check()
    for folder, suffix in [('project', '.lean'), ('objects', '.olean')]:
        allowed = {relative(name, suffix).as_posix() for name in rows}
        if folder == 'objects':
            allowed |= {relative(name, s).as_posix() for name in rows for s in
                        ('.olean.server', '.olean.private', '.ir')}
        new_objects = {p for name in targets for p in
                       (stage / 'objects' / relative(name), *V.sidecar_paths(stage / 'objects' / relative(name)))}
        for file in (stage / folder).rglob('*'):
            canonical(file, True)
            if file.is_file():
                rel = file.relative_to(stage / folder).as_posix()
                need(rel in allowed and (str(file) in frozen.files or
                     file in new_objects), 'Unpinned file in project namespace')
    actual = [V.tree_signature(r) for r in context['runtime_roots']]
    need(actual == context['runtime_trees'], 'Complete runtime tree changed')
    return write(stage, path, {'status': 'ALL_FROZEN_BYTES_UNCHANGED', 'context': context_pin,
                              'inputs': context['inputs'], 'runtime_trees': actual, 'file_count': len(frozen.files)})


def archive_success(stage, attempt, contexts, accepted, targets, frozen, rows):
    """Only new owner bodies and immutable old-evidence locator manifests enter this export."""
    def final_check(label):
        current = scan_history(stage, targets, contexts)
        need(len(current) == 33 and current == accepted, 'Final 33-chain acceptance changed')
        context, context_pin = contexts[targets[-1]]
        return recheck(stage, attempt / 'checks' / (label + '.json'), context, context_pin, frozen, targets, rows)
    before = final_check('export-before')
    paths = {}
    for root in ('contexts', 'inputs', 'accepted', 'attempts', 'imports'):
        for path in sorted((stage / root).rglob('*')):
            canonical(path, True)
            if path.is_file():
                need(path.suffix in ({'.json', '.log', '.py', '.md', '.lean'} if root == 'imports' else
                                    {'.json', '.log'}), 'Unexpected history body')
                paths[path.relative_to(stage).as_posix()] = path
    for module in targets:
        obj = stage / 'objects' / relative(module)
        for path in [stage / 'project' / relative(module, '.lean'),
                     stage / 'audit' / (stem(module) + '.lean'), obj,
                     *[p for p in V.sidecar_paths(obj) if p.exists()]]:
            paths[path.relative_to(stage).as_posix()] = path
    paths['BASE.json'] = stage / 'BASE.json'
    for row in read(HERE / 'CODE_MANIFEST.json')['files']:
        paths['executor/' + row['member']] = HERE / row['member']
    paths['executor/CODE_MANIFEST.json'] = HERE / 'CODE_MANIFEST.json'
    entries = [{'member': name, **fp(path)} for name, path in sorted(paths.items())]
    manifest = {'schema': 'p26_cell01_family_11_evidence_v1', 'new_owners': targets, 'files': entries,
                'accepted_steps': 33, 'supplier_proof_commands': 0, 'old_supplier_bodies_included': False,
                'row001_receipt_bodies_included': False, 'P2_6_complete_claimed': False, 'pre_export_check': before}
    data = (json.dumps(manifest, indent=2) + '\n').encode()
    output = stage / 'evidence' / (attempt.name + '.tar.xz')
    within(stage, output.parent).mkdir(parents=True, exist_ok=True)
    with output.open('xb') as raw, tarfile.open(fileobj=raw, mode='w:xz') as tar:
        for row in entries:
            path = paths[row['member']]
            pinned(path, row)
            info = tarfile.TarInfo(row['member']); info.size = row['bytes']; info.mode = 0o644
            with path.open('rb') as stream:
                tar.addfile(info, stream)
        info = tarfile.TarInfo('MANIFEST.json'); info.size = len(data); info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
    expected = {r['member']: r for r in entries}
    expected['MANIFEST.json'] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    seen = set()
    with tarfile.open(output, 'r:xz') as tar:
        for member in tar:
            need(member.isfile() and member.name in expected and member.name not in seen,
                 'Unsafe, duplicate, or unmanifested export member')
            seen.add(member.name)
            body = tar.extractfile(member).read()
            need(member.size == len(body) and same({'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()},
                 expected[member.name]), 'Export byte readback differs')
    need(seen == set(expected), 'Incomplete exported inventory')
    after = final_check('export-after')
    for row in entries:
        pinned(paths[row['member']], row)
    return {'archive': fp(output), 'members': len(expected), 'post_export_check': after,
            'archive_readback': 'EXACT_REGULAR_UNIQUE_INVENTORY_SIZE_SHA256_VERIFIED'}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--source-archive', type=Path, required=True)
    parser.add_argument('--runtime', type=Path, required=True)
    parser.add_argument('--join', type=Path, action='append', required=True)
    parser.add_argument('--attempt', default=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ') + '-' + uuid.uuid4().hex[:8])
    parser.add_argument('--rss-gib', type=int, default=14)
    parser.add_argument('--wall-seconds', type=int, default=1800)
    parser.add_argument('--max-new-steps', type=int, default=33)
    parser.add_argument('--validate-only', action='store_true')
    args = parser.parse_args(argv)
    need(re.fullmatch(r'[A-Za-z0-9_-]+', args.attempt) and 1 <= args.rss_gib <= 24 and
         0 < args.wall_seconds <= 3300 and 0 <= args.max_new_steps <= 33, 'Invalid attempt or limits')
    stage, root = canonical(args.stage), canonical(args.source_root, True)
    for provider in (HERE, root, canonical(args.source_archive, True), canonical(args.runtime, True)):
        disjoint(stage, provider)
    frozen = E.Frozen()
    code = read(HERE / 'CODE_MANIFEST.json')
    frozen.add(HERE / 'CODE_MANIFEST.json')
    for row in code['files']:
        frozen.add(within(HERE, HERE / row['member'], True), row)
    need(any(row['member'] == 'family_run.py' for row in code['files']), 'Unfrozen executor')
    catalog, targets, rows = source_catalog(root, args.source_archive, frozen)
    runtime = read(args.runtime)
    frozen.add(args.runtime)
    runtime_roots, lib = validate_runtime(runtime, frozen, stage)
    joins = {}
    for path in args.join:
        value = read(canonical(path, True))
        need(value['module'] in targets and value['module'] not in joins, 'Unknown or duplicate owner join')
        joins[value['module']] = path
        for provider in value['read_roots']:
            disjoint(stage, provider)
        disjoint(stage, canonical(path, True))
    for context_path in (stage / 'contexts').glob('*.json'):
        context = read(canonical(context_path, True))
        snapshot = read(within(stage, context['inputs']['path'], True))
        for provider in snapshot['read_roots']:
            disjoint(stage, provider)
    # All stage/input nesting checks precede any mutation.
    source_install(stage, root, catalog, targets, frozen)
    base = {'schema': 'p26_family_stage_v1', 'stage': str(stage), 'code_manifest': fp(HERE / 'CODE_MANIFEST.json'),
            'source_archive': fp(args.source_archive), 'source_manifest': SOURCE_MANIFEST,
            'runtime': fp(args.runtime), 'targets': targets, 'P2_6_complete_claimed': False}
    frozen.add(keep(stage, stage / 'BASE.json', base)['path'])
    contexts = {}
    for module in targets:
        if (stage / 'contexts' / (stem(module) + '.json')).exists():
            contexts[module] = load_context(stage, module, rows, targets, runtime, frozen)
    import_mark = stage / 'imports' / FILENAME_INTERFACE / 'IMPORT.json'
    if import_mark.exists():
        need(INTERFACE in contexts, 'RESTORE_IMPORTED_OWNER_CONTEXT')
        marker = read(import_mark)
        frozen.add(marker['join']['path'], marker['join'])
        import_interface(stage, *contexts[INTERFACE], marker['join']['path'], frozen)
    accepted = scan_history(stage, targets, contexts)
    pending_requested = [module for module in targets if module in joins and (module, 'owned') not in accepted]
    pending_all = [module for module in targets if (module, 'owned') not in accepted]
    need(pending_requested == pending_all[:len(pending_requested)],
         'Requested owner joins must continue the exact frozen accepted prefix')
    for module in targets:
        if (module, 'normal') in accepted:
            for ref in [fp(stage / 'objects' / relative(module)),
                        *V.object_state(stage, stage / 'objects' / relative(module))['sidecars']]:
                frozen.add(ref['path'], ref)
    attempt = within(stage, stage / 'attempts' / args.attempt)
    attempt.mkdir(parents=True, exist_ok=False)
    commands, records = 0, [{'module': m, 'mode': mode, 'receipt': ref, 'reused': True}
                           for (m, mode), ref in accepted.items()]
    try:
        for module in targets:
            if (module, 'owned') in accepted:
                continue
            if module not in joins:
                break
            if module not in contexts:
                contexts[module] = create_context(stage, module, joins[module], root, rows, targets,
                                                  runtime, runtime_roots, lib, frozen)
            context, context_pin = contexts[module]
            if 'accepted_owner' in read(joins[module]):
                need(not any((module, mode) in accepted for mode in MODES),
                     'Cannot replace a partially accepted local owner with another stage')
                import_interface(stage, context, context_pin, joins[module], frozen)
                accepted = scan_history(stage, targets, contexts)
                records = [{'module': m, 'mode': mode, 'receipt': ref, 'reused': True}
                           for (m, mode), ref in accepted.items()]
                continue
            for mode in MODES:
                if (module, mode) in accepted:
                    continue
                if commands >= args.max_new_steps or args.validate_only:
                    break
                prerequisites = prerequisite_records(module, mode, context, accepted)
                V.TARGET = module
                obj = stage / 'objects' / relative(module)
                obj.parent.mkdir(parents=True, exist_ok=True)
                folder = attempt / 'steps' / stem(module) / mode
                run = {'schema': 'p26_family_owner_attempt_v1', 'stage': str(stage), 'module': module,
                       'stage_context': context_pin, 'inputs': context['inputs'], 'attempt': args.attempt,
                       'project': context['project'], 'LEAN_PATH': context['LEAN_PATH'],
                       'source': context['source'], 'audit': context['audit'], 'object_path': str(obj),
                       'lean': runtime['lean_binary']['path'], 'checker': runtime['leanchecker_binary']['path'],
                       'rss_gib': args.rss_gib, 'wall_seconds': args.wall_seconds}
                run_pin = write(stage, attempt / 'runs' / stem(module) / (mode + '.json'), run)
                frozen.add(run_pin['path'], run_pin)
                before = recheck(stage, attempt / 'checks' / (stem(module) + '-' + mode + '-before.json'),
                                 context, context_pin, frozen, targets, rows)
                live = V.object_state(stage, obj)
                if mode == 'normal':
                    need(live['object'] is None and not live['sidecars'], 'UNRECEIPTED_OBJECT')
                else:
                    normal = read(accepted[(module, 'normal')]['path'])
                    V.check_object(stage, obj, normal['object'], normal['object_sidecars'])
                env = execution_environment(run)
                metadata = {'module': module, 'mode': mode, 'run': run_pin, 'context': context_pin,
                            'source': context['source'], 'audit': context['audit'], 'object_before': live['object'],
                            'input_fingerprints': context['inputs'], 'prerequisites': prerequisites,
                            'execution_environment': env}
                print(json.dumps({'module': module, 'mode': mode, 'running': True, 'supplier_commands': 0}), flush=True)
                commands += 1
                try:
                    result = SHARED.run_command(V.expected_argv(mode, run), run['project'], env, folder,
                                                args.wall_seconds, metadata)
                except Exception:
                    if mode == 'normal' and (folder / 'result.json').exists():
                        preserve_failed_normal(stage, attempt, module, folder, obj)
                    raise
                after = recheck(stage, attempt / 'checks' / (stem(module) + '-' + mode + '-after.json'),
                                context, context_pin, frozen, targets, rows)
                state = V.object_state(stage, obj)
                need(state['object'] is not None and (mode == 'normal' or state == live), 'Missing or changed checked object')
                for ref in [state['object'], *state['sidecars']]:
                    frozen.add(ref['path'], ref)
                seal = {'status': 'succeeded', 'module': module, 'mode': mode, 'source': context['source'],
                        'audit': context['audit'], 'object': state['object'], 'object_sidecars': state['sidecars'],
                        'run': run_pin, 'context': context_pin, 'command': fp(folder / 'command.json'),
                        'command_result': fp(folder / 'result.json'), 'log': result['log'], 'before': before,
                        'after': after, 'prerequisites': prerequisites}
                text = Path(result['log']['path']).read_text()
                if mode == 'normal':
                    axioms = {a.strip() for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text)
                              for a in group.split(',') if a.strip()}
                    need(axioms <= ALLOWED, 'Forbidden normal transitive axiom')
                    seal['printed_axioms'] = sorted(axioms)
                if mode == 'owned':
                    inventory = OWNED.parse_owned(text, module)
                    names = V.parsed_imports(text, context['project_modules'])
                    seal['owned_declarations'] = write(stage, folder / 'owned-declarations.json', inventory)
                    seal['owned_declaration_count'] = inventory['owned_declaration_count']
                    seal['module_byte_context'] = write(stage, folder / 'module-byte-context.json',
                                                       V.module_byte_context(names, context['module_search_roots']))
                ref = write(stage, folder / 'ACCEPTED_STEP.json', seal)
                validate_step(stage, module, mode, ref, context, context_pin, accepted)
                keep(stage, stage / 'accepted' / stem(module) / (mode + '.json'),
                     {'module': module, 'mode': mode, 'receipt': ref})
                accepted[(module, mode)] = ref
                records.append({'module': module, 'mode': mode, 'receipt': ref, 'reused': False})
            if (module, 'owned') not in accepted:
                break
        current = scan_history(stage, targets, contexts)
        need(current == accepted, 'Accepted history changed at attempt boundary')
        status = ('PASS_CELL01_ORIGINAL_FLOOR_FAMILY_11' if len(accepted) == 33 else
                  'VALIDATED_INPUTS_NO_PROOF_COMMANDS' if args.validate_only else 'PAUSED_ACCEPTED_PREFIX')
        result = {'status': status, 'records': records, 'accepted_steps': len(accepted),
                  'accepted_owners': sum((m, 'owned') in accepted for m in targets),
                  'new_proof_commands': commands, 'supplier_proof_commands': 0,
                  'scope': 'eleven Cell01 original-floor owners only', 'P2_6_complete_claimed': False}
        if len(accepted) == 33:
            write(stage, attempt / 'PROOF_RESULT.json', {**result, 'status': 'PROOFS_ACCEPTED_EXPORT_PENDING'})
            result['evidence'] = archive_success(stage, attempt, contexts, accepted, targets, frozen, rows)
        write(stage, attempt / 'RESULT.json', result)
        print(json.dumps({**result, 'attempt': str(attempt)}), flush=True)
        return 0
    except Exception as error:
        result = {'status': 'FAILED_STOPPED', 'error': f'{type(error).__name__}: {error}',
                  'records': records, 'new_proof_commands': commands, 'supplier_proof_commands': 0,
                  'P2_6_complete_claimed': False}
        if not (attempt / 'RESULT.json').exists():
            write(stage, attempt / 'RESULT.json', result)
        print(json.dumps(result), file=sys.stderr, flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
