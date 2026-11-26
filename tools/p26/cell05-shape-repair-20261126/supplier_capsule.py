#!/usr/bin/env python3
"""Anchored, relocatable row evidence. No historical receipt is rewritten."""
from pathlib import Path, PurePosixPath as P
import json

from evidence_io import (EvidenceView, absolute, archive_bytes, canonical, checked_export,
                         fp, pin, read, require, same, write_archive)
from portable_receipts import validate_success


def load_plan(here):
    here = canonical(here, True)
    plan = read(here / 'SUPPLIER_PLAN.json')
    require(plan['schema'] == 'cell05_connections_supplier_plan_v1', 'Unknown supplier plan')
    for row in plan['metadata_files']:
        require(same(fp(here / row['relative_path']), row), 'Pinned original supplier metadata changed')
    return plan


def metadata(here, plan, label):
    spec = plan['batches'][label]
    root = here / 'accepted-metadata' / label
    run, success, export = [read(root / name) for name in ('RUN.json', 'SUCCESS.json', 'EXPORT_MANIFEST.json')]
    require(same(fp(root / 'RUN.json'), spec['run']) and same(fp(root / 'SUCCESS.json'), spec['success'])
            and same(fp(root / 'EXPORT_MANIFEST.json'), spec['export_manifest']), 'Supplier metadata anchor mismatch')
    require(success['run'] == spec['run'] and export['success'] == spec['success'], 'Original success anchor links differ')
    require(export['accepted_targets'] == spec['target_count'] and export['accepted_steps'] == 3 * spec['target_count'],
            'Original export target/step count differs')
    require(run['context']['stage'] == spec['stage'] and success['context'] == run['context'], 'Pinned supplier contexts differ')
    return spec, run, success, export


def original_layout(context):
    """Only these four old source/object path roles may be external to exports."""
    paths = {}
    for row in context['suppliers']:
        module = row['module']
        for kind, suffix, roots in [
                ('source', '.lean', [context['supplier_project'], str(P(context['stage']) / 'project')]),
                ('object', '.olean', [context['supplier_objects'], str(P(context['stage']) / 'objects')])]:
            for root in roots:
                old = str(absolute(root) / (module.replace('.', '/') + suffix))
                paths[old] = {'original': {'path': old, **{k: row[kind][k] for k in ('bytes', 'sha256')}},
                              'resolved': {'kind': 'old_supplier', 'module': module, 'file_kind': kind}}
    for key in ('lean_binary', 'leanchecker_binary'):
        identity = context['runtime'][key]
        paths[identity['path']] = {'original': identity, 'resolved': {'kind': 'runtime_binary', 'key': key}}
    return paths


def row_mapping(here, plan):
    rows, run, _, export = metadata(here, plan, 'rows15')
    fields, fields_run, _, fields_export = metadata(here, plan, 'fields73')
    require(run['context']['suppliers'] == fields_run['context']['suppliers'], 'Old fifteen logical suppliers differ')
    require(run['context']['runtime'] == fields_run['context']['runtime'], 'Pinned source runtimes actually differ')
    field_members = {row['member']: row for row in fields_export['members']}
    prefix = rows['tool_rel'] + '/baseline/'
    mappings = original_layout(run['context'])
    shared_count = 0
    for row in export['members']:
        old_path = str(P(rows['stage']) / row['member'])
        if row['member'].startswith(prefix):
            field_member = fields['tool_rel'] + '/baseline/' + row['member'][len(prefix):]
            require(field_member in field_members and same(row, field_members[field_member]),
                    'Shared original baseline member is not byte identical')
            resolved = {'kind': 'fields_archive_member', 'member': field_member}
            shared_count += 1
        else:
            resolved = {'kind': 'blob', 'member': 'blobs/' + row['sha256']}
        require(old_path not in mappings, 'Original exported member overlaps a shared old supplier')
        mappings[old_path] = {'original': {'path': old_path, 'bytes': row['bytes'], 'sha256': row['sha256']},
                              'resolved': resolved}
    require(shared_count == 154, 'Exactly 154 byte-identical baseline files must be shared')
    frozen = {row['path']: row for row in run['context']['frozen_inputs']}
    require(set(frozen) <= set(mappings), 'Original row context has an unmapped frozen input')
    for name, identity in frozen.items():
        require(mappings[name]['original'] == identity, 'Original row frozen identity differs from path mapping')
    return [mappings[name] for name in sorted(mappings)]


def make_view(mappings, resolver):
    view = EvidenceView()
    for row in mappings:
        identity, resolved = row['original'], row['resolved']
        data = resolver(resolved, identity)
        require(same(pin(data), identity), f'Relocated bytes differ from original receipt path: {identity["path"]}')
        view.add(identity['path'], data, resolved)
    return view


def full_export_view(spec, context, files, shared_resolver):
    view = EvidenceView()
    for name, data in files.items():
        if name != 'EXPORT_MANIFEST.json':
            view.add(str(P(spec['stage']) / name), data, {'kind': 'original_export_member', 'member': name})
    for row in original_layout(context).values():
        identity, resolved = row['original'], row['resolved']
        data = shared_resolver(resolved, identity)
        require(same(pin(data), identity), 'Old supplier/runtime byte mismatch')
        view.add(identity['path'], data, resolved)
    return view


def validate_original(here, plan, label, view):
    spec, run, _, export = metadata(here, plan, label)
    require(view.fp(spec['run']['path']) == spec['run'], 'Original RUN exact bytes differ')
    checked = validate_success(view, spec['success'], run['context'], spec['tool_rel'], spec['target_count'])
    require(checked['owned_declaration_count'] == export['owned_declaration_count'], 'Original complete-owned total differs')
    member_pins = {row['member']: row for row in export['members']}
    for module, obj in checked['objects'].items():
        require(same(obj, member_pins['objects/' + module.replace('.', '/') + '.olean']),
                'Accepted object and independently exported object differ')
    return checked


def physical_namespace(root, modules, suffix):
    root = canonical(root, True)
    expected = {m.replace('.', '/') + suffix for m in modules}
    actual = set()
    for path in root.rglob('*'):
        canonical(path, True)
        if path.is_file():
            actual.add(path.relative_to(root).as_posix())
        else:
            require(path.is_dir(), 'Special file in supplier namespace')
    require(actual == expected, 'Supplier namespace contains missing, unknown or sidecar files')


def live_row_snapshot(here, plan):
    spec, run, _, export = metadata(here, plan, 'rows15')
    context = run['context']
    expected = {row['path']: row for row in context['frozen_inputs']}
    for key in ('lean_binary', 'leanchecker_binary'):
        identity = context['runtime'][key]
        expected[identity['path']] = identity
    for row in export['members']:
        name = str(P(spec['stage']) / row['member'])
        expected[name] = {'path': name, 'bytes': row['bytes'], 'sha256': row['sha256']}
    expected[spec['archive']['path']] = spec['archive']
    for name, identity in expected.items():
        require(fp(name) == identity, f'Original live P1 input differs before capsule creation: {name}')
    modules = [row['module'] for row in context['suppliers'] + context['targets']]
    physical_namespace(Path(context['objects']), modules, '.olean')
    physical_namespace(Path(context['cwd']), modules, '.lean')
    return expected


def build_row_capsule(here, output):
    plan = load_plan(here)
    spec, run, _, _ = metadata(here, plan, 'rows15')
    output = canonical(output)
    require(not output.exists(), 'Refuse existing capsule output')
    before = live_row_snapshot(here, plan)
    files, _ = checked_export(spec['archive']['path'], spec['archive'], spec['export_manifest'])

    def live_shared(resolved, identity):
        return canonical(identity['path'], True).read_bytes()

    original = full_export_view(spec, run['context'], files, live_shared)
    checked = validate_original(here, plan, 'rows15', original)
    mappings = row_mapping(here, plan)
    blobs = {'ORIGINAL_EXPORT_MANIFEST.json': files['EXPORT_MANIFEST.json']}
    for row in mappings:
        resolved, identity = row['resolved'], row['original']
        if resolved['kind'] != 'blob':
            continue
        data = original.raw(identity['path'])
        name = resolved['member']
        require(blobs.setdefault(name, data) == data, 'Blob SHA collision or inconsistent mapping')
    manifest = {'schema': 'cell05_rows15_relocatable_supplier_capsule_v1',
                'source_archive': spec['archive'], 'source_export_manifest': spec['export_manifest'],
                'source_run': spec['run'], 'source_success': spec['success'],
                'mappings': mappings,
                'members': [{'member': name, **pin(data)} for name, data in sorted(blobs.items())],
                'accepted_targets_rechecked': 15, 'accepted_steps_rechecked': checked['accepted_steps'],
                'owned_declarations_rechecked': checked['owned_declaration_count'],
                'new_object_bodies': 15, 'old_supplier_object_bodies': 0, 'fields_object_bodies': 0,
                'shared_baseline_members': 154, 'original_receipt_bytes_rewritten': False,
                'Lean_commands': 0, 'Git_commands': 0, 'complete_join_acceptance': False}
    identity = write_archive(output, blobs, manifest)
    require(live_row_snapshot(here, plan) == before, 'Original P1 inputs changed during capsule construction')
    return {'schema': 'cell05_rows15_capsule_build_report_v1', 'status': 'PASS_EXACT_ROW_SUPPLIER_CAPSULE',
            'archive': identity, 'members': len(blobs) + 1, 'original_absolute_path_mappings': len(mappings),
            'new_object_bodies': 15, 'old_supplier_object_bodies': 0, 'fields_object_bodies': 0,
            'accepted_steps_rechecked': checked['accepted_steps'], 'owned_declarations_rechecked': checked['owned_declaration_count'],
            'regular_archive_readback': True, 'original_inputs_unchanged': True,
            'Lean_commands': 0, 'Git_commands': 0, 'full_evidence_archive_transferred': False}


def read_row_capsule(here, plan, capsule_path, shared_resolver, expected_pin=None):
    files = archive_bytes(capsule_path, expected_pin)
    manifest = json.loads(files['CAPSULE_MANIFEST.json'])
    require(manifest['schema'] == 'cell05_rows15_relocatable_supplier_capsule_v1', 'Unknown capsule schema')
    spec = plan['batches']['rows15']
    for key, expected in [('source_archive', spec['archive']), ('source_export_manifest', spec['export_manifest']),
                          ('source_run', spec['run']), ('source_success', spec['success'])]:
        require(manifest[key] == expected, f'Capsule source anchor differs: {key}')
    require(same(pin(files['ORIGINAL_EXPORT_MANIFEST.json']), spec['export_manifest']), 'Original export manifest was rewritten')
    mappings = row_mapping(here, plan)
    require(manifest['mappings'] == mappings, 'Capsule absolute-path mapping differs from the independently derived plan')
    required_blobs = {row['resolved']['member'] for row in mappings if row['resolved']['kind'] == 'blob'}
    require(set(files) == required_blobs | {'ORIGINAL_EXPORT_MANIFEST.json', 'CAPSULE_MANIFEST.json'},
            'Capsule contains missing or unnecessary body members')
    expected_members = [{'member': name, **pin(data)} for name, data in sorted(files.items()) if name != 'CAPSULE_MANIFEST.json']
    require(manifest['members'] == expected_members, 'Capsule member SHA/size manifest differs')

    def resolve(resolved, identity):
        return files[resolved['member']] if resolved['kind'] == 'blob' else shared_resolver(resolved, identity)

    view = make_view(mappings, resolve)
    checked = validate_original(here, plan, 'rows15', view)
    return files, manifest, view, checked
