#!/usr/bin/env python3
"""Join the exact accepted P1 interface suppliers, then run the frozen preflight.

This is a metadata adapter for family_run.py, not a second proof validator.
It never invokes Lean and never rewrites a donor, source, audit, or accepted owner.
"""
from pathlib import Path
import argparse
import importlib.util
import json
import os
import re
import sys

sys.dont_write_bytecode = True
TARGET = 'ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface'
GENERIC = 'ImbalancedChen.P2OriginalSaving19OriginalFloorTransport'
OLD = Path('/workspace/p26-continuation-59264dd64286')
ORIGINAL = OLD / 'cell01-row000-original-floor'
GENERIC_STAGE = OLD / 'original-floor-family/generic-v2-r14'
GENERIC_ATTEMPT = GENERIC_STAGE / 'attempts/generic-v2-r14-first'
CODE_MANIFEST = {'bytes': 1265, 'sha256': '93dc12100f58e29cfe32cfd66b22c2333e9866cf8f5558aa8be06f62327b2c84'}
CONTEXT_PIN = {'path': str(GENERIC_STAGE / 'CONTEXT.json'), 'bytes': 19921,
               'sha256': '3c16bf1d1df5be47d34de40756bc89514fd1e66ab1d3ed66215c14876db4fc28'}
GENERIC_SEALS = {
    'normal': (2872, '800f8ae831bbcfe9478e7cc8334a870ce05b293d7b90d932805d99f2579da226'),
    'kernel': (2787, 'd0f2f9b0cc796755c4a6ba8ccc656f5386de16be5da160cbe27647898997073d'),
    'owned': (3405, '29663c4f100c88f23f0c76db96a4febb97786f801f1fa4f12a00050a4f599157'),
}
CLOSURE_BASENAMES = {
    'HIGHER_MOMENTS_PINNED_CLOSURE.json',
    'GEOMETRY01_ACCEPTED_PINNED_CLOSURE.json',
    'FULL_SOURCE_CLOSURE.json',
    'SUPPLIER_KERNEL_COMPLETION.json',
}


def load_executor(path):
    """Load only the immutable deployed executor and its already pinned helpers."""
    path = Path(path)
    if not path.is_absolute() or path.is_symlink():
        raise RuntimeError('An absolute immutable executor path is required')
    manifest = path.parent / 'CODE_MANIFEST.json'
    import hashlib
    data = manifest.read_bytes()
    if {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()} != CODE_MANIFEST:
        raise RuntimeError('Executor is not the reviewed pilot-v1 release')
    entries = json.loads(data)['files']
    entry = next(row for row in entries if row['member'] == 'family_run.py')
    data = path.read_bytes()
    if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
        raise RuntimeError('Executor bytes differ from the frozen release')
    spec = importlib.util.spec_from_file_location('p26_pilot_executor', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--executor', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--source-archive', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--stage', type=Path, required=True)
    parser.add_argument('--attempt', default='interface-preflight-v1')
    args = parser.parse_args(argv)
    F = load_executor(args.executor)
    output, stage = F.canonical(args.output), F.canonical(args.stage)
    root = F.canonical(args.source_root, True)
    for provider in (output, root, args.executor.parent, OLD, args.source_archive.parent):
        F.disjoint(stage, provider)
    for provider in (root, args.executor.parent, OLD, args.source_archive.parent):
        F.disjoint(output, provider)
    frozen = F.E.Frozen()
    catalog, targets, rows = F.source_catalog(root, args.source_archive, frozen)
    F.need(targets[0] == TARGET, 'The interface must remain the first owner')
    required = F.closure(TARGET, rows) - set(targets)
    delta_path = root / 'metadata/SUPPLIER_DELTA.json'
    delta = F.read(delta_path)
    canonical = {row['module']: row for row in delta['matched_canonical_suppliers']}
    F.need(len(canonical) == 646 and len(required) == 625 and
           len(required & set(canonical)) == 624 and required - set(canonical) == {GENERIC},
           'The pilot is not exactly target + 624 canonical + accepted generic')

    bindings = {}

    def add(ref):
        ref = F.E.identity(ref)
        F.need(Path(ref['path']).is_relative_to(OLD), 'Unexpected historical body outside pinned donor root')
        F.need(F.E.row001_body_allowed(ref['path']), 'Forbidden row001 receipt body')
        frozen.add(ref['path'], ref)
        key = tuple(ref[k] for k in ('path', 'bytes', 'sha256'))
        bindings[key] = {'original': ref, 'current_path': ref['path']}
        return ref

    def body(ref):
        return F.read(add(ref)['path'])

    def direct_refs(value):
        for ref in value.values():
            if isinstance(ref, dict) and {'path', 'bytes', 'sha256'} <= set(ref):
                add(ref)

    def chain(provenance, module):
        """Register exactly the historical bodies read by executor.old_chain."""
        index = body(provenance['index'])
        body(provenance['run'])
        body(provenance['input'])
        records = F.index_records(index, module)
        F.need(records == provenance['records'], 'Historical acceptance record identity differs')
        seals = {}
        for record in records:
            seal = body(record['receipt'])
            direct_refs(seal)
            result = body(seal.get('command_result', record['receipt']))
            direct_refs(result)
            command = body(result['command'])
            direct_refs(command)
            seals[record['mode']] = seal
        return seals

    def original_pin(key):
        row = delta[key]
        return {'path': str(ORIGINAL / row['member']), 'bytes': row['bytes'], 'sha256': row['sha256']}

    old_input_ref = original_pin('original_INPUT')
    old_run_ref = original_pin('original_RUN')
    old_result_ref = original_pin('original_RESULT')
    old_input = body(old_input_ref)
    old_result = body(old_result_ref)
    old_records = F.index_records(old_result, F.ROW000)
    old_provenance = {'run': old_run_ref, 'input': old_input_ref,
                      'index': old_result_ref, 'records': old_records}
    old_seals = chain(old_provenance, F.ROW000)
    closure_refs = [F.E.identity(ref) for ref in old_input['files']
                    if Path(ref['path']).name in CLOSURE_BASENAMES]
    F.need(len(closure_refs) == 4 and old_input['supplier_kernel_addendum'] in closure_refs,
           'The four historical canonical closure/addendum locators are required')
    for ref in closure_refs:
        add(ref)

    generic_context = body(CONTEXT_PIN)
    generic_index_ref = F.fp(GENERIC_ATTEMPT / 'RESULT.json')
    generic_index = body(generic_index_ref)
    generic_records = [
        {'mode': mode, 'receipt': {'path': str(GENERIC_ATTEMPT / 'steps' / mode / 'ACCEPTED_STEP.json'),
                                   'bytes': size, 'sha256': digest}}
        for mode, (size, digest) in GENERIC_SEALS.items()
    ]
    generic_provenance = {'run': F.fp(GENERIC_ATTEMPT / 'RUN.json'),
                          'input': generic_context['inputs'], 'index': generic_index_ref,
                          'records': generic_records}
    generic_seals = chain(generic_provenance, GENERIC)
    owned = generic_seals['owned']
    F.need(owned['context'] == CONTEXT_PIN and
           F.same(generic_context['source'], rows[GENERIC]), 'Generic context/source pin differs')
    accepted_module_context = owned['module_byte_context']
    module_rows = body(accepted_module_context)
    external = [row for row in module_rows if not row['module'].startswith('ImbalancedChen.')]
    F.need(len(external) == 11517, 'Accepted generic external inventory changed')
    # The interface imports the generic itself and only project modules from the
    # old row000 closure. Those two accepted audits have identical external imports.
    # This establishes both inclusions before freezing the new expected inventory.
    old_names = F.V.parsed_imports(Path(old_seals['owned']['log']['path']).read_text(),
                                   F.closure(F.ROW000, rows))
    generic_names = F.V.parsed_imports(Path(owned['log']['path']).read_text(),
                                       F.closure(GENERIC, rows))
    external_names = {row['module'] for row in external}
    F.need({n for n in old_names if not n.startswith('ImbalancedChen.')} == external_names ==
           {n for n in generic_names if not n.startswith('ImbalancedChen.')},
           'Old row000 and generic accepted external inventories differ')
    F.need(required <= F.closure(F.ROW000, rows) | F.closure(GENERIC, rows),
           'Interface supplier closure escapes the two accepted import inventories')
    target_source = root / 'sources' / rows[TARGET]['path']
    target_imports = set(re.findall(r'^import\s+([A-Za-z0-9_.]+)', target_source.read_text(), re.M))
    F.need(target_imports == set(rows[TARGET]['project_imports']) and GENERIC in target_imports,
           'Interface introduces an additional external import')
    audit_source = root / 'metadata/audits' / (F.stem(TARGET) + '.lean')
    audit_imports = set(re.findall(r'^import\s+([A-Za-z0-9_.]+)', audit_source.read_text(), re.M))
    F.need(audit_imports - {TARGET} <= external_names, 'Pilot audit introduces an unbound external import')
    runtime = {
        'schema': 'p26_family_runtime_v1', 'mode': 'complete_tree',
        'lean_binary': generic_context['lean_binary'],
        'leanchecker_binary': generic_context['leanchecker_binary'],
        'runtime_roots': generic_context['LEAN_PATH'].split(os.pathsep)[1:],
        'runtime_trees': generic_context['runtime_trees'],
        'native_library_files': [], 'external_modules': external,
        'external_imports': sorted(row['module'] for row in external),
        'accepted_module_context': accepted_module_context,
    }
    suppliers = []
    for module in sorted(required & set(canonical)):
        row = canonical[module]
        F.need(F.same(row['family_source'], rows[module]), 'Canonical selection source mismatch')
        suppliers.append({'module': module, 'source': F.E.identity(row['canonical_source_provider']),
                          'object': F.E.identity(row['accepted_object_union']),
                          'sidecars': [F.E.identity(ref) for ref in row['accepted_object_sidecars']],
                          'kind': 'canonical', 'canonical_context': 'row000_23rd'})
    suppliers.append({'module': GENERIC, 'source': generic_context['source'],
                      'object': generic_index['object'], 'sidecars': owned['object_sidecars'],
                      'kind': 'three_mode', 'provenance': generic_provenance})
    join = {
        'schema': 'p26_family_owner_join_v1', 'module': TARGET, 'read_roots': [str(OLD)],
        'bindings': [bindings[key] for key in sorted(bindings)],
        'canonical_contexts': {'row000_23rd': {
            'run': old_run_ref, 'input': old_input_ref, 'result': old_result_ref,
            'records': old_records, 'closure_refs': closure_refs}},
        'suppliers': sorted(suppliers, key=lambda row: row['module']),
        'external_imports': runtime['external_imports'],
    }
    # Metadata is create-once/read-back-identical. Validation belongs to the frozen runner.
    join_pin = F.keep(output, output / 'INTERFACE_JOIN.json', join)
    runtime_pin = F.keep(output, output / 'RUNTIME.json', runtime)
    prepared = {
        'schema': 'p26_cell01_interface_prepared_inputs_v1', 'status': 'PREPARED_FOR_EXISTING_VALIDATOR',
        'generator': F.fp(Path(__file__)), 'executor_code_manifest': F.fp(args.executor.parent / 'CODE_MANIFEST.json'),
        'source_archive': F.fp(args.source_archive), 'supplier_delta': F.fp(delta_path),
        'join': join_pin, 'runtime': runtime_pin, 'reusable_owner_stage': str(stage),
        'target': TARGET, 'source_closure': 626, 'canonical_suppliers': 624, 'generic_suppliers': 1,
        'finite_suppliers': 0, 'new_proof_commands': 0, 'supplier_proof_commands': 0,
        'generic_and_row000_external_imports_equal': True, 'external_module_count': len(external),
        'P2_6_complete_claimed': False,
    }
    F.keep(output, output / 'PREPARED_INPUTS.json', prepared)
    print(json.dumps(prepared), flush=True)
    # This exact existing path hashes the full accepted runtime, validates both old
    # three-mode chains and all 625 suppliers, and installs one persistent owner context.
    return F.main([
        '--stage', str(stage), '--source-root', str(root), '--source-archive', str(args.source_archive),
        '--runtime', str(output / 'RUNTIME.json'), '--join', str(output / 'INTERFACE_JOIN.json'),
        '--attempt', args.attempt, '--rss-gib', '14', '--wall-seconds', '1800',
        '--max-new-steps', '0', '--validate-only',
    ])


if __name__ == '__main__':
    raise SystemExit(main())
