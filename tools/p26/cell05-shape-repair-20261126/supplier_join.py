#!/usr/bin/env python3
"""Revalidate separate P1/P2 historical chains before joining exact suppliers."""
from pathlib import Path, PurePosixPath as P
import json
import os

from baseline_checks import verify_baseline
from evidence_io import (canonical, checked_export, dump_new, fp, pin, read, require, same)
from runtime_compat import (capture_runtime_guard, check_runtime_guard, logical_roots, runtime_evidence)
from supplier_capsule import (full_export_view, load_plan, metadata, physical_namespace,
                             read_row_capsule, validate_original)

TOOL_REL = Path('tools/p26/scalable-cell05-connections-run')


def disjoint(first, second):
    first, second = canonical(first), canonical(second)
    require(not first.is_relative_to(second) and not second.is_relative_to(first),
            f'Paths overlap in one direction: {first} / {second}')


def supplier_path(root, module, kind):
    return Path(root) / (module.replace('.', '/') + ('.lean' if kind == 'source' else '.olean'))


def context_shared_reader(context, fields_files, project, objects):
    def resolve(resolved, identity):
        kind = resolved['kind']
        if kind == 'fields_archive_member':
            data = fields_files[resolved['member']]
        elif kind == 'old_supplier':
            root = project if resolved['file_kind'] == 'source' else objects
            path = supplier_path(root, resolved['module'], resolved['file_kind'])
            require(same(fp(path), identity), f'Current shared supplier differs from original path identity: {path}')
            data = path.read_bytes()
        elif kind == 'runtime_binary':
            path = Path(context['runtime'][resolved['key']]['path'])
            require(same(fp(path), identity), 'Current runtime binary differs from original bytes')
            data = path.read_bytes()
        else:
            raise RuntimeError(f'Unapproved shared mapping kind: {kind}')
        require(same(pin(data), identity), 'Explicit shared mapping resolved to different bytes')
        return data
    return resolve


def baseline_from_fields(spec, fields_files):
    here = canonical(Path(spec['stage']) / spec['tool_rel'], True)
    baseline_manifest = json.loads(fields_files[spec['tool_rel'] + '/BASELINE_EVIDENCE.json'])
    relatives = ['BASELINE_EVIDENCE.json', 'SUPPLIER_REGISTRY.json'] + [row['relative_path'] for row in baseline_manifest['members']]
    require(len(relatives) == len(set(relatives)) == 156, 'Unexpected old closure document coverage')
    identities = []
    for relative in relatives:
        expected = pin(fields_files[spec['tool_rel'] + '/' + relative])
        path = here / relative
        require(same(fp(path), expected), 'Live published old closure differs from anchored fields archive')
        identities.append(fp(path))
    value = verify_baseline(here)
    require(value['full_supplier_kernel_closed_in_combined_evidence'] is True,
            'Old fifteen require their actual historical receipts and current raw05 addendum')
    return value, identities


def joined_inputs(here, row_capsule, project, objects, expected_capsule=None):
    """One shared validator for installation, proof startup, resume and export."""
    plan = load_plan(here)
    registry = read(here / 'SUPPLIER_REGISTRY.json')
    require(registry['schema'] == 'cell05_connections_supplier_registry_v1'
            and registry['supplier_count'] == len(registry['suppliers']) == 103, 'Wrong exact joined registry')
    fields, field_run, _, _ = metadata(here, plan, 'fields73')
    field_context = field_run['context']
    fields_files, fields_manifest = checked_export(fields['archive']['path'], fields['archive'], fields['export_manifest'])
    resolver = context_shared_reader(field_context, fields_files, project, objects)
    field_view = full_export_view(fields, field_context, fields_files, resolver)
    field_result = validate_original(here, plan, 'fields73', field_view)
    row_files, row_manifest, row_view, row_result = read_row_capsule(here, plan, row_capsule, resolver, expected_capsule)
    require(field_result['accepted_steps'] == 219 and row_result['accepted_steps'] == 45,
            'Full independent historical step coverage is required')
    baseline, baseline_files = baseline_from_fields(fields, fields_files)
    summaries, snapshot = runtime_evidence(here, plan)
    known_objects = {**row_result['objects'], **field_result['objects']}
    require(len(known_objects) == 88, 'New historical supplier module sets overlap')
    old = {row['module']: row for row in field_context['suppliers']}
    rows_context = metadata(here, plan, 'rows15')[1]['context']
    target_lookup = {row['module']: row for context in [rows_context, field_context] for row in context['targets']}
    for row in registry['suppliers']:
        module = row['module']
        expected = old[module] if module in old else target_lookup[module]
        require(row['source'] == expected['source'] and row['project_imports'] == expected['project_imports'],
                'Registry source/import graph differs from accepted historical context')
        require(same(row['object'], old[module]['object'] if module in old else known_objects[module]),
                'Registry object differs from all three original acceptance steps')
    require(set(old) | set(known_objects) == {row['module'] for row in registry['suppliers']}, 'Supplier coverage differs')
    return {'plan': plan, 'registry': registry, 'fields_spec': fields, 'fields_context': field_context,
            'fields_files': fields_files, 'row_files': row_files, 'row_view': row_view, 'field_view': field_view,
            'row_result': row_result, 'field_result': field_result, 'baseline': baseline, 'baseline_files': baseline_files,
            'runtime_summaries': summaries, 'runtime_snapshot': snapshot}


def resolved_paths(view, capsule, fields_archive, project, objects, context):
    rows = []
    for item in view.mappings():
        original, resolved = item['original'], item['resolved']
        kind = resolved['kind']
        if kind == 'blob':
            current = {'kind': 'archive_member', 'archive': fp(capsule), 'member': resolved['member']}
        elif kind in ('fields_archive_member', 'original_export_member'):
            current = {'kind': 'archive_member', 'archive': fp(fields_archive), 'member': resolved['member']}
        elif kind == 'old_supplier':
            root = project if resolved['file_kind'] == 'source' else objects
            current = {'kind': 'current_file', 'file': fp(supplier_path(root, resolved['module'], resolved['file_kind']))}
        elif kind == 'runtime_binary':
            current = {'kind': 'current_file', 'file': fp(context['runtime'][resolved['key']]['path'])}
        else:
            raise RuntimeError('Unexpected historical mapping type')
        rows.append({'original': original, 'resolved': current})
    return rows


def check_provider(project, objects, registry):
    project, objects = canonical(project, True), canonical(objects, True)
    disjoint(project, objects)
    modules = [row['module'] for row in registry['suppliers']]
    physical_namespace(project, modules, '.lean')
    physical_namespace(objects, modules, '.olean')
    identities = []
    for row in registry['suppliers']:
        for kind, root in [('source', project), ('object', objects)]:
            path = supplier_path(root, row['module'], kind)
            require(same(fp(path), row[kind]), 'Joined provider source/object differs from exact registry')
            identities.append(fp(path))
    return identities


def validate_join(here):
    here = canonical(here, True)
    join_path = here / 'SUPPLIER_JOIN.json'
    join = read(join_path)
    require(join['schema'] == 'cell05_connections_supplier_join_v1', 'Unknown supplier join schema')
    stage = canonical(join['new_stage'], True)
    require(here == stage / TOOL_REL, 'Joined evidence belongs to another new stage')
    project, objects = canonical(join['supplier_project'], True), canonical(join['supplier_objects'], True)
    disjoint(stage, project)
    disjoint(stage, objects)
    require(project.parent == objects.parent and project.name == 'project' and objects.name == 'objects', 'Wrong joined provider layout')
    provider = project.parent
    require(fp(here / 'SUPPLIER_PLAN.json') == join['supplier_plan']
            and fp(here / 'SUPPLIER_REGISTRY.json') == join['supplier_registry'], 'Join/package linkage differs')
    require(fp(join['row_capsule']['path']) == join['row_capsule'], 'Relocatable row capsule changed')
    data = joined_inputs(here, Path(join['row_capsule']['path']), project, objects, join['row_capsule'])
    check_provider(project, objects, data['registry'])
    require(join['fields_archive'] == data['fields_spec']['archive'], 'P2 archive provenance differs')
    require(join['baseline_files'] == data['baseline_files'] and join['old_baseline'] == data['baseline'], 'Old closure evidence join changed')
    require(join['historical_rows15'] == {'run': data['plan']['batches']['rows15']['run'],
                'success': data['plan']['batches']['rows15']['success'], 'accepted_steps': 45, 'owned_declarations': 5147},
            'P1 row historical acceptance scope differs')
    require(join['historical_fields73'] == {'run': data['plan']['batches']['fields73']['run'],
                'success': data['plan']['batches']['fields73']['success'], 'accepted_steps': 219, 'owned_declarations': 2875},
            'P2 field historical acceptance scope differs')
    guard_path = provider / 'evidence/RUNTIME_GUARD.json'
    require(join['runtime_guard']['path'] == str(guard_path), 'Runtime guard is outside this exact supplier provider')
    check_runtime_guard(join['runtime_guard'])
    require(read(guard_path)['snapshot'] == data['runtime_summaries']['P2']['output']
            and read(guard_path)['logical_roots'] == logical_roots(data['runtime_summaries']['P2']), 'Guard/runtime comparison linkage differs')
    for name, key, view in [('ROWS15_PATH_MAP.json', 'rows_path_map', data['row_view']),
                             ('FIELDS73_PATH_MAP.json', 'fields_path_map', data['field_view'])]:
        path = provider / 'evidence' / name
        require(join[key]['path'] == str(path) and fp(path) == join[key], 'Exact historical path-map document changed')
        expected = resolved_paths(view, join['row_capsule']['path'], join['fields_archive']['path'], project, objects, data['fields_context'])
        require(read(path) == {'schema': 'cell05_original_path_to_current_evidence_v1', 'mappings': expected,
                               'historical_bytes_rewritten': False}, 'Historical original-to-current mapping differs')
    require(join['full_supplier_kernel_closed_in_combined_evidence'] is True
            and join['old_proof_commands'] == join['compatibility_kernel_replays'] == 0
            and join['historical_loaded_runtime_inventory_claimed'] is False, 'Joined acceptance scope differs')
    evidence = [fp(join_path), fp(here / 'SUPPLIER_PLAN.json'), fp(here / 'SUPPLIER_REGISTRY.json'),
                join['row_capsule'], join['fields_archive'], join['runtime_guard'], join['rows_path_map'], join['fields_path_map'],
                data['runtime_summaries']['P2']['output'], *data['baseline_files']]
    return {'status': 'PASS_EXACT_103_SUPPLIER_JOIN', 'supplier_count': 103,
            'old_supplier_count': 15, 'row_supplier_count': 15, 'field_supplier_count': 73,
            'historical_row_steps_rechecked': 45, 'historical_field_steps_rechecked': 219,
            'old_baseline': data['baseline'], 'runtime_guard': join['runtime_guard'],
            'current_stock_roots_byte_identical': 10, 'historical_loaded_runtime_inventory_claimed': False,
            'full_supplier_kernel_closed_in_combined_evidence': True,
            'old_Lean_commands_executed': 0, 'compatibility_kernel_replays': 0,
            'supplier_project': str(project), 'supplier_objects': str(objects), 'frozen_evidence': evidence}


def preflight_join(here, provider, row_capsule, registry, fields_context):
    stage = here.parents[2]
    require(here == stage / TOOL_REL, 'Join must run inside the exact new stage package')
    provider, row_capsule = canonical(provider), canonical(row_capsule, True)
    disjoint(stage, provider)
    disjoint(stage, Path(fields_context['stage']))
    disjoint(provider, Path(fields_context['stage']))
    disjoint(stage, row_capsule)
    disjoint(provider, row_capsule)
    join_path = canonical(here / 'SUPPLIER_JOIN.json')
    require(not join_path.exists(), 'Supplier join already exists; validate it instead of replacing it')
    expected = set()
    for row in registry['suppliers']:
        for directory, kind in [('project', 'source'), ('objects', 'object')]:
            path = supplier_path(provider / directory, row['module'], kind)
            canonical(path)
            expected.add(path.relative_to(provider).as_posix())
            if path.exists():
                require(same(fp(path), row[kind]), 'Existing partial provider has different bytes')
    for name in ('RUNTIME_GUARD.json', 'ROWS15_PATH_MAP.json', 'FIELDS73_PATH_MAP.json'):
        path = canonical(provider / 'evidence' / name)
        require(not path.exists(), 'Existing join metadata requires exact evidence recovery; refusing overwrite')
        expected.add(path.relative_to(provider).as_posix())
    if provider.exists():
        for path in provider.rglob('*'):
            canonical(path, True)
            require(path.is_dir() or (path.is_file() and path.relative_to(provider).as_posix() in expected),
                    'Unknown existing provider file/sidecar')
    return stage, provider


def install_join(here, provider, row_capsule):
    here = canonical(here, True)
    plan = load_plan(here)
    registry = read(here / 'SUPPLIER_REGISTRY.json')
    fields_context = metadata(here, plan, 'fields73')[1]['context']
    stage, provider = preflight_join(here, provider, row_capsule, registry, fields_context)
    original_project, original_objects = Path(fields_context['cwd']), Path(fields_context['objects'])
    modules = [row['module'] for row in fields_context['suppliers'] + fields_context['targets']]
    physical_namespace(original_project, modules, '.lean')
    physical_namespace(original_objects, modules, '.olean')
    data = joined_inputs(here, row_capsule, original_project, original_objects)
    rows_context = metadata(here, plan, 'rows15')[1]['context']
    row_modules = {row['module'] for row in rows_context['targets']}
    actions, protected = [], {}
    for row in registry['suppliers']:
        module = row['module']
        for kind, directory in [('source', 'project'), ('object', 'objects')]:
            destination = supplier_path(provider / directory, module, kind)
            canonical(destination)
            if module in row_modules:
                old = supplier_path(P(rows_context['stage']) / directory, module, kind)
                body = data['row_view'].raw(old)
                require(same(pin(body), row[kind]), 'New row supplier body differs from accepted registry')
                actions.append((destination, row[kind], None, body))
            else:
                source = supplier_path(original_project if kind == 'source' else original_objects, module, kind)
                require(same(fp(source), row[kind]), 'P2 cached supplier body differs from accepted registry')
                protected[str(source)] = fp(source)
                actions.append((destination, row[kind], source, None))
    protected.update({identity['path']: identity for identity in data['baseline_files']})
    protected[str(row_capsule)] = fp(row_capsule)
    protected[data['fields_spec']['archive']['path']] = data['fields_spec']['archive']
    # All output ancestors, file identities and proof evidence have passed before
    # the first directory creation or supplier installation below.
    guard = capture_runtime_guard(here, plan)
    for name, identity in protected.items():
        require(fp(name) == identity, 'Input changed before supplier installation')
    for destination, identity, source, body in actions:
        destination.parent.mkdir(parents=True, exist_ok=True)
        canonical(destination.parent, True)
        if destination.exists():
            require(same(fp(destination), identity), 'Existing partial supplier differs')
        elif source is not None:
            # Existing 88 supplier objects remain one inode on the same volume.
            # A cross-device layout must be revised explicitly; no hidden copy.
            os.link(source, destination)
        else:
            with destination.open('xb') as output:
                output.write(body)
        require(same(fp(destination), identity), 'Installed supplier bytes differ')
    project, objects = provider / 'project', provider / 'objects'
    check_provider(project, objects, registry)
    guard_path = provider / 'evidence/RUNTIME_GUARD.json'
    dump_new(guard_path, guard)
    maps = {}
    for name, key, view in [('ROWS15_PATH_MAP.json', 'rows_path_map', data['row_view']),
                             ('FIELDS73_PATH_MAP.json', 'fields_path_map', data['field_view'])]:
        path = provider / 'evidence' / name
        dump_new(path, {'schema': 'cell05_original_path_to_current_evidence_v1',
                       'mappings': resolved_paths(view, row_capsule, data['fields_spec']['archive']['path'], project, objects, fields_context),
                       'historical_bytes_rewritten': False})
        maps[key] = fp(path)
    for name, identity in protected.items():
        require(fp(name) == identity, 'Original provider/evidence changed during join')
    join = {'schema': 'cell05_connections_supplier_join_v1', 'new_stage': str(stage),
            'supplier_plan': fp(here / 'SUPPLIER_PLAN.json'), 'supplier_registry': fp(here / 'SUPPLIER_REGISTRY.json'),
            'supplier_project': str(project), 'supplier_objects': str(objects),
            'row_capsule': fp(row_capsule), 'fields_archive': data['fields_spec']['archive'],
            'baseline_files': data['baseline_files'], 'old_baseline': data['baseline'],
            'historical_rows15': {'run': plan['batches']['rows15']['run'], 'success': plan['batches']['rows15']['success'],
                                   'accepted_steps': 45, 'owned_declarations': 5147},
            'historical_fields73': {'run': plan['batches']['fields73']['run'], 'success': plan['batches']['fields73']['success'],
                                     'accepted_steps': 219, 'owned_declarations': 2875},
            'runtime_guard': fp(guard_path), **maps,
            'old_proof_commands': 0, 'compatibility_kernel_replays': 0,
            'existing_supplier_object_bodies_copied': 0, 'new_row_supplier_objects_installed': 15,
            'historical_loaded_runtime_inventory_claimed': False,
            'full_supplier_kernel_closed_in_combined_evidence': True}
    dump_new(here / 'SUPPLIER_JOIN.json', join)
    return validate_join(here)
