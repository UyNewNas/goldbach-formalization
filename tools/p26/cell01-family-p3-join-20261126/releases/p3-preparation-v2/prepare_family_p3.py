#!/usr/bin/env python3
"""Install exact missing suppliers and validate eleven immutable P3 joins.

This adapter calls only read-only acceptance/runtime routines in frozen p3-v2.
It never invokes family_run.main, Lean, leanchecker, Git, or another process.
"""
from pathlib import Path, PurePosixPath
import argparse
import json
import os
import re
import sys
import tarfile

sys.dont_write_bytecode = True
from join_common import (OLD, ROW000_ROOT, GENERIC_ROOT, PREFIX_ROOT, CLOSURES,
                         TraceBodies, canonical_group, checked_local, expected,
                         identity_bytes, load_executor, need, trace_chain)
import external_runtime as X


def key(ref):
    return tuple(ref[k] for k in ('path', 'bytes', 'sha256'))


def exact_extract(F, archive_ref, manifest_ref, destination, members, manifest_member):
    """Exclusive extraction, or complete-marker readback; partial state stops."""
    archive = F.canonical(archive_ref['path'], True)
    manifest_path = F.canonical(manifest_ref['path'], True)
    destination = F.canonical(destination)
    for source in (archive, manifest_path):
        F.disjoint(destination, source)
    F.pinned(archive, archive_ref)
    F.pinned(manifest_path, manifest_ref)
    wanted = dict(members)
    need(manifest_member not in wanted, 'Duplicate extraction manifest member')
    wanted[manifest_member] = manifest_ref
    for name in wanted:
        rel = PurePosixPath(name)
        need(name and not rel.is_absolute() and '..' not in rel.parts and str(rel) == name,
             'Unsafe exact archive member')
    marker = {'schema': 'p26_exact_selected_extraction_v1', 'archive': archive_ref,
              'manifest': manifest_ref, 'destination': str(destination), 'members': len(wanted)}
    if destination.exists():
        need((destination / 'EXTRACTION.json').is_file(), 'PARTIAL_EXTRACTION_REQUIRES_RECOVERY')
        need(F.read(destination / 'EXTRACTION.json') == marker, 'Existing extraction identity differs')
    else:
        destination.mkdir(parents=True)
        seen = set()
        with tarfile.open(archive, 'r:xz') as stream:
            for member in stream:
                need(member.isfile() and member.name in wanted and member.name not in seen,
                     'Unexpected, duplicate or nonregular archive member')
                need(member.size == wanted[member.name]['bytes'], 'Archive member size differs')
                data = stream.extractfile(member).read()
                need(F.same(identity_bytes(data), wanted[member.name]), 'Archive member hash differs')
                path = F.within(destination, destination / member.name)
                path.parent.mkdir(parents=True, exist_ok=True)
                F.canonical(path)
                with path.open('xb') as output:
                    output.write(data)
                seen.add(member.name)
        need(seen == set(wanted), 'Missing exact archive members')
        F.pinned(archive, archive_ref)
        F.pinned(manifest_path, manifest_ref)
        for name, pin in wanted.items():
            F.pinned(destination / name, pin)
        F.write(destination, destination / 'EXTRACTION.json', marker)
    for name, pin in wanted.items():
        F.pinned(destination / name, pin)
    actual = set()
    for path in destination.rglob('*'):
        F.canonical(path, True)
        if path.is_file():
            actual.add(path.relative_to(destination).as_posix())
    need(actual == set(wanted) | {'EXTRACTION.json'}, 'Extraction has unmanifested/missing files')
    return destination


def load_bundle(F, config):
    manifest = F.read(F.pinned(config['manifest']['path'], config['manifest'])['path'])
    need(manifest['schema'] == 'p26_family_selected_original_bodies_v1'
         and manifest['role'] == config['role'] and manifest['row001_bodies_included'] is False
         and manifest['supplier_objects_included'] is False and manifest['Lean_commands'] == 0
         and manifest['new_proof_credit'] == 0, 'Evidence body package boundary differs')
    wanted_groups = {'canonical'} if config['role'] == 'canonical' else {'generic', 'prefix'}
    need(config['role'] in {'canonical', 'p1-generic-prefix'} and set(manifest['groups']) == wanted_groups,
         'Unexpected selected-evidence group keys')
    members, identities = {}, set()
    for entry in manifest['entries']:
        ref = F.E.identity(entry['original'])
        path = Path(ref['path'])
        need('row001' not in str(path).lower() and path.suffix in {'.json', '.log', '.lean'},
             'Protected/non-body file in transferable evidence package')
        need(entry['member'] == 'bodies/' + ref['sha256'] + path.suffix and key(ref) not in identities,
             'Unsafe or duplicate original-body mapping')
        identities.add(key(ref))
        if entry['member'] in members:
            need(F.same(members[entry['member']], ref), 'Conflicting body deduplication')
        members[entry['member']] = ref
    need(len(identities) == manifest['original_body_references'] and
         len(members) == manifest['unique_body_files'], 'Body inventory count differs')
    selected_groups = ([manifest['groups']['canonical']] if config['role'] == 'canonical' else
                       [manifest['groups']['generic'], *manifest['groups']['prefix'].values()])
    need(identities == {key(ref) for group in selected_groups for ref in group['body_refs']},
         'Evidence body set is not the exact declared old-chain read set')
    root = exact_extract(F, config['archive'], config['manifest'], config['destination'],
                         members, 'EVIDENCE_MANIFEST.json')
    bindings = {key(e['original']): {'original': F.E.identity(e['original']),
                                    'current_path': str(root / e['member'])} for e in manifest['entries']}
    return manifest['groups'], bindings, root


def object_provider(F, cfg, rows):
    capsule_cfg = cfg['object_capsule']
    manifest_path = F.canonical(capsule_cfg['manifest'], True)
    archive_path = F.canonical(capsule_cfg['archive'], True)
    manifest = json.loads(checked_local(manifest_path, expected('object_manifest')))
    checked_local(archive_path, expected('object_archive'))
    modules = {r['module']: r for r in manifest['modules']}
    need(len(modules) == 189 and manifest['source_body_count'] == 14 and manifest['object_count'] == 189
         and manifest['sidecar_count'] == 0 and manifest['row001_files_accessed'] is False
         and manifest['receipt_or_log_bodies_included'] is False, 'Wrong missing-object capsule')
    members = {}
    for row in manifest['members']:
        need(row['module'] in modules and 'row001' not in row['module'].lower()
             and row['kind'] in {'object', 'source'}, 'Unexpected capsule module or payload kind')
        suffix, folder = ('.olean', 'objects') if row['kind'] == 'object' else ('.lean', 'sources')
        name = folder + '/' + str(F.relative(row['module'], suffix))
        need(row['member'] == name and name not in members, 'Object-capsule member mapping differs')
        members[name] = row['original']
    need(len(members) == 203, 'Wrong exact supplier payload count')
    root = exact_extract(F, F.fp(archive_path), F.fp(manifest_path), capsule_cfg['destination'],
                         members, 'MANIFEST.json')
    present = json.loads(checked_local(cfg['inventories']['present'], expected('P3_present')))['suppliers']
    missing = json.loads(checked_local(cfg['inventories']['missing'], expected('P3_missing')))['missing']
    registry = {}
    for row in present:
        need(row['module'] not in registry and row['sidecars'] == [], 'Duplicate/sidecar existing supplier')
        registry[row['module']] = {k: row[k] for k in ('module', 'source', 'object', 'sidecars')}
    need(len(registry) == 602 and not (set(registry) & set(modules)), 'Existing/missing supplier sets overlap')
    missing_rows = {r['module']: r for r in missing}
    need(set(missing_rows) == set(modules) and len(missing_rows) == 189, 'Wrong original missing delta')
    for module, record in modules.items():
        source = missing_source(F, module, record, missing_rows[module], root)
        obj = F.fp(root / 'objects' / F.relative(module))
        need(F.same(source, record['source']) and F.same(obj, record['object']), 'Restored byte identity differs')
        registry[module] = {'module': module, 'source': source, 'object': obj, 'sidecars': []}
    need(len(registry) == 791, 'Incomplete physical supplier registry')
    for module, row in registry.items():
        need(module in rows and F.same(row['source'], rows[module]), 'Same-name source conflict')
        for name in ('source', 'object'):
            F.pinned(row[name]['path'], row[name])
        need(not any(p.exists() or p.is_symlink() for p in F.V.sidecar_paths(Path(row['object']['path']))),
             'Unexpected supplier object sidecar')
        source_text = Path(row['source']['path']).read_text()
        imports = set(re.findall(r'^import\s+(ImbalancedChen\.[A-Za-z0-9_.]+)', source_text, re.M))
        need(imports == set(rows[module]['project_imports']), 'Current source import closure differs')
    return manifest, registry, root


def missing_source(F, module, record, missing, root):
    if record['source_body_included']:
        return F.fp(root / 'sources' / F.relative(module, '.lean'))
    if 'p3_exact_source' in missing:
        return missing['p3_exact_source']
    # The original P3 inventory's provider_groups explicitly locates indices
    # for rows098--106 here; the final missing delta omitted their path field.
    allowed = {'ImbalancedChen.P2OriginalSaving19Cell01Row%03dFinite' % n for n in range(98, 107)}
    need(module in allowed and missing['source_missing'] is False,
         'Missing an explicit already-inventoried P3 source locator')
    return {**record['source'], 'path': str(OLD / 'cell01-rest-finite-v2/project' / F.relative(module, '.lean'))}


def check_transferred_groups(F, groups, delta, capsule):
    canonical = groups['canonical']
    fixed = canonical_group(F, delta)
    need(all(canonical[k] == fixed[k] for k in ('module', 'source', 'object', 'provenance')),
         'Canonical evidence authority changed')
    generic = groups['generic']
    fixed_generic = capsule['receipt_validation']['generic']
    need(generic['module'] == F.GENERIC and generic['source'] == fixed_generic['source']
         and generic['object'] == fixed_generic['object']
         and generic['provenance']['records'] == fixed_generic['records'], 'Generic authority changed')
    fixed_prefix = capsule['receipt_validation']['C_prefix']
    prefix_rows = {r['module']: r for r in fixed_prefix['rows']}
    need(set(groups['prefix']) == set(prefix_rows) and len(prefix_rows) == 9, 'C-prefix selection changed')
    for module, row in prefix_rows.items():
        group = groups['prefix'][module]
        provenance = group['provenance']
        need(group['source'] == row['source'] and group['object'] == row['object']
             and provenance['run'] == fixed_prefix['run'] and provenance['index'] == fixed_prefix['partial']
             and provenance['records'] == [{'mode': m, 'receipt': ref} for m, ref in zip(F.MODES, row['chain'])],
             'C-prefix historical chain differs from the fixed capsule/export anchor')


def local_groups(F, inventory, registry, rows):
    roots = OLD / 'cell01-rest-finite-v2'
    def reader(ref):
        path = F.canonical(ref['path'], True)
        need(path.is_relative_to(roots), 'Finite evidence body escaped the original P3 stage')
        return F.pinned(path, ref) and path.read_bytes()
    store, groups, runs = TraceBodies(F, reader), {}, []
    for attempt in inventory['finite_attempts']:
        run, index = store.json(attempt['run']), store.json(attempt['success'])
        runs.append(run)
        for ordinal in index['completed_rows']:
            module = 'ImbalancedChen.P2OriginalSaving19Cell01Row%03dFinite' % ordinal
            need(module not in groups and module in registry, 'Duplicate or unknown P3 finite owner')
            group = {'module': module, 'source': registry[module]['source'], 'object': registry[module]['object'],
                     'provenance': {'run': attempt['run'], 'input': run['input_fingerprints'],
                                    'index': attempt['success'], 'records': F.index_records(index, module)}}
            trace_chain(F, store, group, rows)
            groups[module] = group
    need(len(groups) == 133, 'Wrong original P3 A/B/C-tail coverage')
    bindings = {k: {'original': ref, 'current_path': ref['path']} for k, ref in store.entries.items()}
    return groups, bindings, runs


def row001_metadata(F, registry):
    origin = Path(F.E.ROW001_ORIGIN)
    attempt = origin / 'verification/20261126-row001-v1'
    index_ref, run_ref = F.fp(attempt / 'SUCCESS.json'), F.fp(attempt / 'RUN.json')
    index, run = F.read(index_ref['path']), F.read(run_ref['path'])
    records = F.index_records(index, F.E.ROW001)
    need(all(r['receipt']['sha256'] == F.ROW001_RECEIPTS[r['mode']] for r in records),
         'Original row001 fixed receipt identity differs')
    for r in records:
        path = F.canonical(r['receipt']['path'], True)
        need(path.is_relative_to(origin), 'Row001 receipt escaped its original host stage')
        F.pinned(path, r['receipt'])
    normal = F.read(records[0]['receipt']['path'])
    input_ref = normal['input_fingerprints']
    need(input_ref == run['input_fingerprints'] and Path(input_ref['path']).is_relative_to(origin),
         'Row001 original input binding differs')
    inputs = F.read(F.pinned(input_ref['path'], input_ref)['path'])
    row = registry[F.E.ROW001]
    need(row['source']['path'] == str(origin / 'project' / F.relative(F.E.ROW001, '.lean'))
         and row['object']['path'] == str(origin / 'objects' / F.relative(F.E.ROW001)),
         'Row001 must use only its original P3 source/object locations')
    row = {**row, 'kind': 'same_host_row001', 'provenance': {'in_place': True, 'run': run_ref,
            'input': input_ref, 'index': index_ref, 'records': records}}
    # Only paths/pins leave this function. Full original bodies remain in place.
    extra_roots = {str(origin)}
    for ref in inputs['files']:
        extra_roots.add(str(F.canonical(ref['path'], True).parent))
    return row, extra_roots


def binding_read(F, bindings, ref):
    need(key(ref) in bindings, 'Missing original body binding: ' + ref['path'])
    path = bindings[key(ref)]['current_path']
    F.pinned(path, ref)
    return F.read(path)


def owned_names(F, group, bindings, rows):
    seal = binding_read(F, bindings, group['provenance']['records'][2]['receipt'])
    ref = seal['log']
    need(key(ref) in bindings, 'Missing historical owned log binding')
    path = bindings[key(ref)]['current_path']
    F.pinned(path, ref)
    return set(F.V.parsed_imports(Path(path).read_text(), F.closure(group['module'], rows)))


def finite_runtime_roots(run):
    """Match the actual Cell01Batch verifier/exporter stage and cache contract."""
    roots = run['LEAN_PATH'].split(os.pathsep)
    project_objects = str(Path(run['stage']) / 'objects')
    need(roots and roots[0] == project_objects,
         'Original finite LEAN_PATH must begin with its exact stage/objects')
    need(run['cache_root'] != project_objects and len(roots) >= 2
         and roots[1:-1] == run['mathlib_package_object_roots'],
         'Original finite cache/package-root contract differs')
    return roots[1:]


def prepare_runtime(F, cfg, generic, groups, bindings, runs, rows, registry, source_root, catalog):
    accepted_ref = generic['accepted_module_context']
    accepted = binding_read(F, bindings, accepted_ref)
    old_external = {r['module']: r for r in accepted if not r['module'].startswith('ImbalancedChen.')}
    need(len(old_external) == 11517, 'Original generic external inventory differs')
    names = set(old_external)
    need(owned_names(F, groups['canonical'], bindings, rows) - set(rows) == names
         and owned_names(F, generic, bindings, rows) - set(rows) == names,
         'Original canonical/generic external import sets differ')
    for group in [*groups['prefix'].values(), *groups['finite'].values()]:
        need(owned_names(F, group, bindings, rows) - set(rows) <= names,
             'Finite supplier imports external modules outside accepted generic context')
    sources = [Path(row['source']['path']) for row in registry.values()]
    sources += [source_root / 'sources' / row['path'] for row in catalog['targets']]
    sources += [source_root / 'metadata/audits' / Path(row['path']).name for row in catalog['full_owned_audits']]
    for source in sources:
        direct = set(re.findall(r'^import\s+([A-Za-z0-9_.]+)', source.read_text(), re.M))
        need({n for n in direct if not n.startswith('ImbalancedChen.')} <= names,
             'Source/audit introduces an unbound external import')
    runtime_cfg = cfg['runtime']
    raw_roots = runtime_cfg.get('roots')
    if raw_roots is None:
        raw_roots = finite_runtime_roots(runs[0])
    raw_roots = [*raw_roots, *runtime_cfg.get('additional_roots', [])]
    roots = list(dict.fromkeys(str(F.canonical(Path(p).resolve(strict=True), True)) for p in raw_roots))
    lean = F.fp(F.canonical(Path(runtime_cfg.get('lean', '/toolchains/bin/lean')).resolve(strict=True), True))
    checker = F.fp(F.canonical(Path(runtime_cfg.get('leanchecker', '/toolchains/bin/leanchecker')).resolve(strict=True), True))
    generic_context = binding_read(F, bindings, binding_read(F, bindings, generic['provenance']['records'][2]['receipt'])['context'])
    need(F.same(lean, generic_context['lean_binary']) and F.same(checker, generic_context['leanchecker_binary']),
         'P3 compiler/checker bytes differ from original accepted generic')
    lib = F.canonical(Path(lean['path']).parent.parent / 'lib', True)
    for root in [*roots, str(lib)]:
        need(not (Path(root) / 'ImbalancedChen').exists(), 'Runtime project namespace fallback is forbidden')
        F.disjoint(cfg['stage'], root)
    actual = F.V.module_byte_context(names, [*roots, lib / 'lean'])
    for row in actual:
        old = old_external[row['module']]
        need(F.same(row['object'], old['object']) and F.sidecar_signature(row['sidecars']) == F.sidecar_signature(old['sidecars']),
             'P3 nonproject object/sidecar differs from accepted generic: ' + row['module'])
    tree_roots = list(dict.fromkeys([*roots, str(lib)]))
    current_context = F.fp(bindings[key(accepted_ref)]['current_path'])
    return {'schema': 'p26_family_runtime_v1', 'mode': 'complete_tree', 'lean_binary': lean,
            'leanchecker_binary': checker, 'runtime_roots': roots,
            'runtime_trees': [F.V.tree_signature(root) for root in tree_roots],
            'native_library_files': [], 'external_modules': actual, 'external_imports': sorted(names),
            'accepted_module_context': current_context}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config', type=Path, required=True)
    args = parser.parse_args()
    cfg = json.loads(args.config.read_text())
    need(cfg['schema'] == 'p26_family_p3_prepare_config_v1', 'Wrong preparation contract')
    F = load_executor(Path(cfg['executor']))
    output, stage = F.canonical(cfg['output']), F.canonical(cfg['stage'])
    source_root, source_archive = F.canonical(cfg['source_root'], True), F.canonical(cfg['source_archive'], True)
    external_cfg = cfg['runtime']['external_provider']
    external_root = F.canonical(external_cfg['destination'])
    need(cfg['runtime']['additional_roots'] == [str(external_root)],
         'Runtime must use the single complete 515-module external provider')
    destinations = [output, F.canonical(cfg['object_capsule']['destination']),
                    external_root, *[F.canonical(x['destination']) for x in cfg['evidence']]]
    # These inputs are fixed locator lists, read before creating any new path.
    # A mistaken destination must never create even a new child in an old stage.
    present_prior = json.loads(checked_local(cfg['inventories']['present'], expected('P3_present')))['suppliers']
    missing_prior = json.loads(checked_local(cfg['inventories']['missing'], expected('P3_missing')))['missing']
    protected = [stage, OLD, Path(F.E.ROW001_ORIGIN), source_root, source_archive,
                 Path(__file__).absolute().parent, Path(cfg['executor']).parent,
                 F.canonical(args.config, True).parent,
                 Path(cfg['object_capsule']['archive']).parent,
                 Path(cfg['object_capsule']['manifest']).parent,
                 *set(X.P3_ROOTS.values()), Path('/mathlib'), Path('/toolchains')]
    protected += [Path(row[k]['path']).parent for row in present_prior for k in ('source', 'object')]
    protected += [Path(row['p3_exact_source']['path']).parent for row in missing_prior
                  if 'p3_exact_source' in row]
    protected += [Path(bundle[k]['path']).parent for bundle in cfg['evidence'] for k in ('archive', 'manifest')]
    protected += [Path(external_cfg[k]['path']).parent for k in ('archive', 'manifest')]
    for i, dest in enumerate(destinations):
        for other in [*destinations[i + 1:], *protected]:
            F.disjoint(dest, other)
    frozen = F.E.Frozen()
    frozen.add(args.config)
    adapter_code = [frozen.add(Path(__file__).absolute()),
                    frozen.add(Path(__file__).absolute().with_name('join_common.py')),
                    frozen.add(Path(__file__).absolute().with_name('external_runtime.py'))]
    executor_manifest = frozen.add(Path(cfg['executor']).parent / 'CODE_MANIFEST.json', expected('executor_manifest'))
    for row in F.read(executor_manifest['path'])['files']:
        frozen.add(Path(cfg['executor']).parent / row['member'], row)
    for role, pin_key in [('present', 'P3_present'), ('missing', 'P3_missing'), ('summary', 'P3_inventory')]:
        frozen.add(cfg['inventories'][role], expected(pin_key))
    for role, pin_key in [('archive', 'object_archive'), ('manifest', 'object_manifest')]:
        frozen.add(cfg['object_capsule'][role], expected(pin_key))
    for bundle in cfg['evidence']:
        for role in ('archive', 'manifest'):
            frozen.add(bundle[role]['path'], bundle[role])
    for role in ('archive', 'manifest'):
        frozen.add(external_cfg[role]['path'], external_cfg[role])
    catalog, targets, rows = F.source_catalog(source_root, source_archive, frozen)
    delta = json.loads(checked_local(source_root / 'metadata/SUPPLIER_DELTA.json', expected('supplier_delta')))
    inventory = json.loads(checked_local(cfg['inventories']['summary'], expected('P3_inventory')))
    input_identity = {'config': F.fp(args.config), 'adapter_code': adapter_code,
                      'executor_manifest': executor_manifest}
    if output.exists():
        need((output / 'PREPARATION_INPUT.json').is_file(), 'PARTIAL_PREPARATION_REQUIRES_RECOVERY')
        need(F.read(output / 'PREPARATION_INPUT.json') == input_identity,
             'Existing preparation belongs to a different immutable configuration')
    else:
        output.mkdir(parents=True)
        F.write(output, output / 'PREPARATION_INPUT.json', input_identity)
    capsule, registry, provider_root = object_provider(F, cfg, rows)
    required_union = set().union(*(F.closure(m, rows) - set(targets) for m in targets))
    need(set(registry) == required_union and len(required_union) == 791, 'Registry is not the exact 791-old-owner union')
    groups, bindings, evidence_roots = {}, {}, []
    need({x['role'] for x in cfg['evidence']} == {'canonical', 'p1-generic-prefix'} and len(cfg['evidence']) == 2,
         'Both exact canonical and P1 generic/C-prefix body sets are required')
    for bundle_cfg in cfg['evidence']:
        bundle_groups, bundle_bindings, root = load_bundle(F, bundle_cfg)
        need(not (set(groups) & set(bundle_groups)), 'Duplicate evidence group')
        groups.update(bundle_groups)
        for k, binding in bundle_bindings.items():
            need(k not in bindings, 'Ambiguous original body mapping')
            bindings[k] = binding
        evidence_roots.append(root)
    check_transferred_groups(F, groups, delta, capsule)
    finite, local_bindings, runs = local_groups(F, inventory, registry, rows)
    groups['finite'] = finite
    need(not (set(bindings) & set(local_bindings)), 'Local/relocated evidence conflict')
    bindings.update(local_bindings)
    row001, row001_roots = row001_metadata(F, registry)
    accepted_context = groups['generic']['accepted_module_context']
    current_context = F.fp(bindings[key(accepted_context)]['current_path'])
    need(X.install(F, external_cfg, current_context, frozen) == external_root,
         'Unexpected complete external provider path')
    runtime = prepare_runtime(F, cfg, groups['generic'], groups, bindings, runs, rows,
                              registry, source_root, catalog)
    runtime_roots, lib = F.validate_runtime(runtime, frozen, stage)
    canonical = groups['canonical']
    canonical_context = {k: canonical['provenance'][v] for k, v in
                         [('run', 'run'), ('input', 'input'), ('result', 'index'), ('records', 'records')]}
    canonical_context['closure_refs'] = canonical['closure_refs']
    canonical_names = {r['module'] for r in delta['matched_canonical_suppliers']}
    need(len(canonical_names) == 646, 'Wrong canonical registry')
    all_groups = {F.ROW000: canonical, F.GENERIC: groups['generic'], **groups['prefix'], **finite}
    joins, validation_rows = {}, []
    for module in targets:
        required = F.closure(module, rows) - set(targets)
        suppliers, selected_refs = [], {key(r) for r in canonical['body_refs']}
        read_roots = {str(provider_root), *map(str, evidence_roots)}
        for name in sorted(required):
            row = dict(registry[name])
            if name in canonical_names:
                row.update(kind='canonical', canonical_context='row000_23rd')
            elif name == F.E.ROW001:
                row = row001
                read_roots.update(row001_roots)
            else:
                group = all_groups[name]
                row.update(kind='three_mode', provenance=group['provenance'])
                selected_refs.update(key(ref) for ref in group['body_refs'])
            suppliers.append(row)
            read_roots.update(str(Path(row[k]['path']).parent) for k in ('source', 'object'))
        selected_bindings = [bindings[k] for k in sorted(selected_refs)]
        read_roots.update(str(Path(b['current_path']).parent) for b in selected_bindings)
        join = {'schema': 'p26_family_owner_join_v1', 'module': module,
                'read_roots': sorted(read_roots), 'bindings': selected_bindings,
                'canonical_contexts': {'row000_23rd': canonical_context}, 'suppliers': suppliers,
                'external_imports': runtime['external_imports']}
        supplied, validations = F.validate_join(stage, join, module, rows, targets, runtime, frozen, delta)
        need(set(supplied) == required, 'Frozen validator returned another supplier closure')
        joins[module] = join
        validation_rows.append({'module': module, 'old_suppliers': len(required),
                                'full_project_closure': len(F.closure(module, rows)),
                                'validated_chains': len(validations), 'supplier_proof_commands': 0,
                                'row001': [v for v in validations if v['module'] == F.E.ROW001]})
        print(json.dumps({'phase': 'existing_supplier_join_validated', **validation_rows[-1]}), flush=True)
    frozen.check()
    F.keep(output, output / 'PREPARATION_INPUT.json', input_identity)
    F.keep(output, output / 'SUPPLIER_REGISTRY.json', {'schema': 'p26_family_p3_exact791_registry_v1',
                                                    'suppliers': [registry[k] for k in sorted(registry)]})
    runtime_pin = F.keep(output, output / 'RUNTIME.json', runtime)
    join_pins = [F.keep(output, output / 'joins' / (F.stem(m) + '.json'), joins[m]) for m in targets]
    result = {'schema': 'p26_family_p3_existing_suppliers_preflight_v1',
              'status': 'PASS_ALL_ELEVEN_EXISTING_SUPPLIER_JOINS_NO_PROOFS',
              'source_archive': F.fp(source_archive), 'runtime': runtime_pin, 'joins': join_pins,
              'supplier_union': 791, 'new_owner_count': 11, 'expected_later_new_steps': 33,
              'owner_checks': validation_rows, 'runtime_roots': [str(p) for p in runtime_roots],
              'complete_external_provider': str(external_root), 'external_provider_modules': 515,
              'existing_external_modules_reused': 505, 'old_external_modules_transferred': 10,
              'future_stage': str(stage), 'later_rss_gib': 12,
              'frozen_input_files_checked': len(frozen.files), 'Lean_commands': 0,
              'supplier_proof_commands': 0, 'new_proof_credit': 0,
              'row001_bodies_exported': False, 'P2_6_complete_claimed': False}
    F.keep(output, output / 'PREFLIGHT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
