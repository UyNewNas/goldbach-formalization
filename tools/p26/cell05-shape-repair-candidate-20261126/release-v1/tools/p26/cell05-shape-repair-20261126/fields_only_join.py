#!/usr/bin/env python3
"""Join only the original P2 fields73 plus fifteen baseline suppliers.

All historical proof, baseline and runtime checks are the existing reviewed
connections-run functions. No row capsule, P1 connection or proof replay occurs.
"""
from pathlib import Path
import argparse
import json
import os
import sys

sys.dont_write_bytecode = True
if sys.flags.optimize != 0:
    raise RuntimeError('Original evidence validators require Python assertions enabled')

from evidence_io import canonical, checked_export, dump_new, fp, read, require, same
from runtime_compat import capture_runtime_guard, check_runtime_guard, logical_roots, runtime_evidence
from supplier_capsule import full_export_view, load_plan, metadata, physical_namespace, validate_original
from supplier_join import baseline_from_fields, check_provider, context_shared_reader, disjoint, resolved_paths, supplier_path

TOOL_REL = Path('tools/p26/cell05-connections14-run-20261126')
JOIN_SCHEMA = 'cell05_connections14_fields88_join_v1'


def fields_inputs(here, project, objects):
    require(sys.flags.optimize == 0, 'Original evidence validators require Python assertions enabled')
    plan = load_plan(here)
    registry = read(here / 'SUPPLIER_REGISTRY.json')
    require(registry['schema'] == 'cell05_connections_supplier_registry_v1' and
            registry['supplier_count'] == len(registry['suppliers']) == 88 and
            plan['joined_supplier_count'] == 88 and plan['new_row_supplier_count'] == 0 and
            plan['new_connection_targets'] == 14 and plan['new_connection_steps'] == 42 and
            plan['row_capsule_required'] is False, 'Wrong exact fields-only scope')
    spec, run, _, _ = metadata(here, plan, 'fields73')
    context = run['context']
    files, _ = checked_export(spec['archive']['path'], spec['archive'], spec['export_manifest'])
    resolver = context_shared_reader(context, files, project, objects)
    view = full_export_view(spec, context, files, resolver)
    result = validate_original(here, plan, 'fields73', view)
    require(result['accepted_steps'] == 219 and result['owned_declaration_count'] == 2875,
            'Full original fields73 normal/kernel/owned coverage is required')
    baseline, baseline_files = baseline_from_fields(spec, files)
    summaries, snapshot = runtime_evidence(here, plan)
    old = {row['module']: row for row in context['suppliers']}
    fields = {row['module']: row for row in context['targets']}
    require(len(old) == 15 and len(fields) == len(result['objects']) == 73 and
            not set(old) & set(fields), 'Original baseline/field owner boundary differs')
    require({row['module'] for row in registry['suppliers']} == set(old) | set(fields),
            'Fields-only provider has missing or additional supplier names')
    for row in registry['suppliers']:
        name = row['module']
        expected = old[name] if name in old else fields[name]
        require(row['source'] == expected['source'] and row['project_imports'] == expected['project_imports'] and
                same(row['object'], old[name]['object'] if name in old else result['objects'][name]),
                'Same-name source/object/import identity differs from accepted P2 evidence')
    selection = read(here / 'CONNECTION_TARGETS.json')
    targets = selection['targets']
    require(selection['target_count'] == len(targets) == 14 and selection['expected_steps'] == 42,
            'Wrong fourteen-target selection')
    known = set(old) | set(fields)
    used = set()
    graph = {row['module']: row['project_imports'] for row in registry['suppliers'] + targets}
    for row in targets:
        require(set(row['project_imports']) <= known, 'Target dependency is absent or later in source order')
        found, active = set(), set()

        def visit(name):
            require(name in graph and name not in active, 'Missing or cyclic selected dependency')
            if name in found:
                return
            active.add(name)
            for dependency in graph[name]:
                visit(dependency)
            active.remove(name)
            found.add(name)

        for dependency in row['project_imports']:
            visit(dependency)
        require(sorted(found) == row['transitive_dependencies'], 'Frozen target closure differs')
        used |= found & (set(old) | set(fields))
        known.add(row['module'])
    require(len(used) == 83 and sorted(used) == selection['minimal_actual_supplier_union'],
            'Selected fourteen-target actual supplier union is not exactly83')
    return {'plan': plan, 'registry': registry, 'fields_spec': spec, 'fields_context': context,
            'fields_files': files, 'field_view': view, 'field_result': result,
            'baseline': baseline, 'baseline_files': baseline_files,
            'runtime_summaries': summaries, 'runtime_snapshot': snapshot}


def field_path_map(data, project, objects):
    archive = data['fields_spec']['archive']['path']
    return {'schema': 'cell05_original_path_to_current_evidence_v1',
            'mappings': resolved_paths(data['field_view'], archive, archive, project, objects,
                                       data['fields_context']), 'historical_bytes_rewritten': False}


def validate_join(here):
    here = canonical(here, True)
    join_path = here / 'SUPPLIER_JOIN.json'
    join = read(join_path)
    require(join['schema'] == JOIN_SCHEMA, 'Unknown fields-only join schema')
    stage = canonical(join['new_stage'], True)
    require(here == stage / TOOL_REL, 'Fields-only join belongs to another stage')
    project, objects = canonical(join['supplier_project'], True), canonical(join['supplier_objects'], True)
    disjoint(stage, project)
    disjoint(stage, objects)
    require(project.parent == objects.parent and project.name == 'project' and objects.name == 'objects',
            'Wrong fields-only provider layout')
    provider = project.parent
    for key, name in [('supplier_plan', 'SUPPLIER_PLAN.json'), ('supplier_registry', 'SUPPLIER_REGISTRY.json'),
                      ('target_selection', 'CONNECTION_TARGETS.json')]:
        require(fp(here / name) == join[key], 'Immutable join/input linkage differs')
    data = fields_inputs(here, project, objects)
    check_provider(project, objects, data['registry'])
    require(join['fields_archive'] == data['fields_spec']['archive'] and
            join['baseline_files'] == data['baseline_files'] and join['old_baseline'] == data['baseline'],
            'Original fields/archive/baseline linkage differs')
    require(join['historical_fields73'] == {
        'run': data['plan']['batches']['fields73']['run'], 'success': data['plan']['batches']['fields73']['success'],
        'accepted_steps': 219, 'owned_declarations': 2875}, 'Historical fields scope differs')
    guard_path = provider / 'evidence/RUNTIME_GUARD.json'
    require(join['runtime_guard']['path'] == str(guard_path), 'Runtime guard is outside exact provider')
    check_runtime_guard(join['runtime_guard'])
    guard = read(guard_path)
    require(guard['snapshot'] == data['runtime_summaries']['P2']['output'] and
            guard['logical_roots'] == logical_roots(data['runtime_summaries']['P2']),
            'Guard is not bound to the actual P2 snapshot and matching local P1/P2 probes')
    map_path = provider / 'evidence/FIELDS73_PATH_MAP.json'
    require(join['fields_path_map']['path'] == str(map_path) and fp(map_path) == join['fields_path_map'] and
            read(map_path) == field_path_map(data, project, objects), 'Original fields path map differs')
    require(join['full_supplier_kernel_closed_in_combined_evidence'] is True and
            join['old_proof_commands'] == join['compatibility_kernel_replays'] == 0 and
            join['historical_loaded_runtime_inventory_claimed'] is False and
            join['row_capsule_required'] is False, 'Unexpected fields-only acceptance scope')
    evidence = [fp(join_path), fp(here / 'SUPPLIER_PLAN.json'), fp(here / 'SUPPLIER_REGISTRY.json'),
                fp(here / 'CONNECTION_TARGETS.json'), join['fields_archive'], join['runtime_guard'],
                join['fields_path_map'], data['runtime_summaries']['P2']['output'], *data['baseline_files']]
    evidence += [fp(here / row['relative_path']) for row in data['plan']['metadata_files']]
    evidence += [fp(here / 'RUNTIME_COMPATIBILITY_PINS.json')]
    evidence += [fp(here / row['relative_path']) for row in read(here / 'RUNTIME_COMPATIBILITY_PINS.json')['files']]
    return {'status': 'PASS_EXACT_FIELDS88_SUPPLIER_JOIN', 'supplier_count': 88,
            'old_supplier_count': 15, 'row_supplier_count': 0, 'field_supplier_count': 73,
            'historical_field_steps_rechecked': 219, 'actual_selected_supplier_union': 83,
            'old_baseline': data['baseline'], 'runtime_guard': join['runtime_guard'],
            'fields_context': data['fields_context'], 'current_stock_roots_byte_identical': 10,
            'historical_loaded_runtime_inventory_claimed': False,
            'full_supplier_kernel_closed_in_combined_evidence': True,
            'old_Lean_commands_executed': 0, 'compatibility_kernel_replays': 0,
            'supplier_project': str(project), 'supplier_objects': str(objects), 'frozen_evidence': evidence}


def install_join(here, provider):
    here = canonical(here, True)
    stage, provider = here.parents[2], canonical(provider)
    require(here == stage / TOOL_REL, 'Join must run within the exact new package')
    disjoint(stage, provider)
    if (here / 'SUPPLIER_JOIN.json').exists():
        existing = read(here / 'SUPPLIER_JOIN.json')
        require(existing['supplier_project'] == str(provider / 'project') and
                existing['supplier_objects'] == str(provider / 'objects'), 'Existing join uses another provider')
        return validate_join(here)
    plan = load_plan(here)
    context = metadata(here, plan, 'fields73')[1]['context']
    disjoint(stage, context['stage'])
    disjoint(provider, context['stage'])
    original_project, original_objects = Path(context['cwd']), Path(context['objects'])
    registry = read(here / 'SUPPLIER_REGISTRY.json')
    actions, protected, expected_files = [], {}, set()
    for row in registry['suppliers']:
        for kind, folder, original in [('source', 'project', original_project), ('object', 'objects', original_objects)]:
            src = supplier_path(original, row['module'], kind)
            dst = canonical(supplier_path(provider / folder, row['module'], kind))
            require(same(fp(src), row[kind]), 'Original P2 provider byte mismatch')
            protected[str(src)] = fp(src)
            expected_files.add(dst.relative_to(provider).as_posix())
            if dst.exists():
                require(same(fp(dst), row[kind]), 'Existing partial provider differs')
            actions.append((src, dst, row[kind]))
    for name in ('RUNTIME_GUARD.json', 'FIELDS73_PATH_MAP.json'):
        path = canonical(provider / 'evidence' / name)
        require(not path.exists(), 'Partial join metadata requires exact recovery; refusing overwrite')
        expected_files.add(path.relative_to(provider).as_posix())
    if provider.exists():
        for path in provider.rglob('*'):
            canonical(path, True)
            require(path.is_dir() or path.is_file() and path.relative_to(provider).as_posix() in expected_files,
                    'Unexpected provider file/sidecar')
    modules = [row['module'] for row in registry['suppliers']]
    physical_namespace(original_project, modules, '.lean')
    physical_namespace(original_objects, modules, '.olean')
    data = fields_inputs(here, original_project, original_objects)
    protected.update({row['path']: row for row in data['baseline_files']})
    protected[data['fields_spec']['archive']['path']] = data['fields_spec']['archive']
    guard = capture_runtime_guard(here, plan)
    for path, identity in protected.items():
        require(fp(path) == identity, 'Original input changed before provider installation')
    # Every dependency/provenance/runtime check above precedes the first write.
    for src, dst, identity in actions:
        dst.parent.mkdir(parents=True, exist_ok=True)
        canonical(dst.parent, True)
        if not dst.exists():
            os.link(src, dst)
        require(same(fp(dst), identity), 'Hardlinked provider bytes differ')
    project, objects = provider / 'project', provider / 'objects'
    check_provider(project, objects, registry)
    guard_path = provider / 'evidence/RUNTIME_GUARD.json'
    dump_new(guard_path, guard)
    map_path = provider / 'evidence/FIELDS73_PATH_MAP.json'
    dump_new(map_path, field_path_map(data, project, objects))
    for path, identity in protected.items():
        require(fp(path) == identity, 'Original input changed during fields join')
    join = {'schema': JOIN_SCHEMA, 'new_stage': str(stage),
            'supplier_plan': fp(here / 'SUPPLIER_PLAN.json'), 'supplier_registry': fp(here / 'SUPPLIER_REGISTRY.json'),
            'target_selection': fp(here / 'CONNECTION_TARGETS.json'),
            'supplier_project': str(project), 'supplier_objects': str(objects),
            'fields_archive': data['fields_spec']['archive'], 'baseline_files': data['baseline_files'],
            'old_baseline': data['baseline'], 'historical_fields73': {
                'run': plan['batches']['fields73']['run'], 'success': plan['batches']['fields73']['success'],
                'accepted_steps': 219, 'owned_declarations': 2875},
            'runtime_guard': fp(guard_path), 'fields_path_map': fp(map_path),
            'old_proof_commands': 0, 'compatibility_kernel_replays': 0,
            'existing_supplier_object_bodies_copied': 0, 'row_capsule_required': False,
            'historical_loaded_runtime_inventory_claimed': False,
            'full_supplier_kernel_closed_in_combined_evidence': True}
    dump_new(here / 'SUPPLIER_JOIN.json', join)
    return validate_join(here)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--provider', type=Path)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    here = Path(__file__).absolute().parent
    require(args.check_only or args.provider is not None, '--provider is required for installation')
    result = validate_join(here) if args.check_only else install_join(here, args.provider)
    # Compact report only; raw historical context stays in exact local evidence.
    print(json.dumps({key: value for key, value in result.items() if key not in ('fields_context', 'frozen_evidence')}, sort_keys=True))


if __name__ == '__main__':
    main()
