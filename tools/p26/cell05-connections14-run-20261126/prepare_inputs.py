#!/usr/bin/env python3
"""Locally assemble the original Cell05 fourteen-source selection without Lean."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).absolute().parent
REPO = HERE.parents[2]
DONOR = REPO / 'tools/p26/scalable-cell05-connections-run'
AUDIT = REPO / 'tools/p26/cell05-resume-audit-20261126'
HELPERS = ('evidence_io.py', 'portable_receipts.py', 'supplier_capsule.py',
           'supplier_join.py', 'runtime_compat.py', 'runtime_probe.py', 'baseline_checks.py')


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def put(path, value):
    data = value if isinstance(value, bytes) else (json.dumps(value, indent=2) + '\n').encode()
    if path.exists():
        if path.read_bytes() != data:
            raise RuntimeError('Refuse different frozen input: ' + str(path))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)


def read(path):
    return json.loads(path.read_text())


def main():
    ready = read(AUDIT / 'READY14_TARGETS.json')
    locators = read(AUDIT / 'FIELDS88_SUPPLIERS.json')
    assert ready['target_count'] == len(ready['targets']) == 14
    assert ready['accepted_new_steps'] == 0 and locators['supplier_count'] == 88
    target_names = [row['module'] for row in ready['targets']]
    old_targets = read(DONOR / 'CONNECTION_TARGETS.json')
    old_rows = {row['module']: row for row in old_targets['targets']}
    targets = [old_rows[name] for name in target_names]
    for expected, row in zip(ready['targets'], targets):
        for key in ('source', 'audit', 'source_member', 'audit_relative_path',
                    'project_imports', 'transitive_dependencies'):
            assert expected[key] == row[key], ('Changed original target', row['module'], key)
        source = (REPO / (row['module'].replace('.', '/') + '.lean')).read_bytes()
        audit = (DONOR / row['audit_relative_path']).read_bytes()
        assert pin(source) == row['source'] and pin(audit) == row['audit']
        put(HERE / row['source_member'], source)
        put(HERE / row['audit_relative_path'], audit)

    old_registry = read(DONOR / 'SUPPLIER_REGISTRY.json')
    old_suppliers = {row['module']: row for row in old_registry['suppliers']}
    locator_rows = {row['module']: row for row in locators['suppliers']}
    suppliers = [old_suppliers[name] for name in sorted(locator_rows)]
    assert len(suppliers) == 88
    for row in suppliers:
        locator = locator_rows[row['module']]
        for kind in ('source', 'object'):
            assert row[kind] == {k: locator[kind][k] for k in ('bytes', 'sha256')}
        assert row['project_imports'] == locator['project_imports']
    graph = {row['module']: row['project_imports'] for row in suppliers + targets}
    available = set(locator_rows)
    used = set()
    for row in targets:
        assert set(row['project_imports']) <= available
        found, active = set(), set()

        def visit(name):
            assert name in graph and name not in active
            if name in found:
                return
            active.add(name)
            for dependency in graph[name]:
                visit(dependency)
            active.remove(name)
            found.add(name)

        for dependency in row['project_imports']:
            visit(dependency)
        assert sorted(found) == row['transitive_dependencies']
        used |= found & set(locator_rows)
        available.add(row['module'])
    assert len(used) == 83 and len(available) == 102

    plan = read(DONOR / 'SUPPLIER_PLAN.json')
    plan.update({'new_row_supplier_count': 0, 'joined_supplier_count': 88,
                 'new_connection_targets': 14, 'new_connection_steps': 42,
                 'rows15_usage': 'LOCAL_RUNTIME_METADATA_COMPARISON_ONLY',
                 'row_capsule_required': False, 'minimal_actual_supplier_union': 83})
    for row in plan['metadata_files']:
        data = (DONOR / row['relative_path']).read_bytes()
        assert pin(data) == {key: row[key] for key in ('bytes', 'sha256')}
        put(HERE / row['relative_path'], data)
    runtime_pins = read(DONOR / 'RUNTIME_COMPATIBILITY_PINS.json')
    for row in runtime_pins['files']:
        data = (DONOR / row['relative_path']).read_bytes()
        assert pin(data) == {key: row[key] for key in ('bytes', 'sha256')}
        put(HERE / row['relative_path'], data)
    put(HERE / 'RUNTIME_COMPATIBILITY_PINS.json', (DONOR / 'RUNTIME_COMPATIBILITY_PINS.json').read_bytes())
    for name in HELPERS:
        put(HERE / name, (DONOR / name).read_bytes())

    registry = {**old_registry, 'suppliers': suppliers, 'supplier_count': 88,
                'selection': 'fields73_and_original15_only', 'required_by_selected_targets': 83}
    put(HERE / 'SUPPLIER_PLAN.json', plan)
    put(HERE / 'SUPPLIER_REGISTRY.json', registry)
    put(HERE / 'CONNECTION_TARGETS.json', {
        'schema': 'cell05_connections_targets_v1', 'targets': targets, 'target_count': 14,
        'expected_steps': 42, 'normal_kernel_owned_steps_accepted': 0,
        'minimal_actual_supplier_union': sorted(used), 'row_capsule_required': False})
    source = read(DONOR / 'CONNECTIONS_SOURCE_MANIFEST.json')
    owners = {row['module']: row for row in source['owners']}
    put(HERE / 'CONNECTIONS_SOURCE_MANIFEST.json', {
        **source, 'owners': [owners[name] for name in target_names], 'owner_count': 14,
        'scope': 'Fourteen existing Cell05 field-only connection candidates',
        'excluded_original_targets': [row['module'] for row in ready['blocked_targets']],
        'required_existing_suppliers': 83, 'preserved_existing_provider': 88,
        'source_or_audit_bytes_changed': False, 'accepted': False, 'P2_6_complete': False})
    for name in ('READY14_TARGETS.json', 'FIELDS88_SUPPLIERS.json'):
        put(HERE / name, (AUDIT / name).read_bytes())
    origins = [DONOR / name for name in (*HELPERS, 'SUPPLIER_PLAN.json', 'SUPPLIER_REGISTRY.json',
                                       'CONNECTION_TARGETS.json', 'CONNECTIONS_SOURCE_MANIFEST.json',
                                       'RUNTIME_COMPATIBILITY_PINS.json')]
    origins += [AUDIT / name for name in ('READY14_TARGETS.json', 'FIELDS88_SUPPLIERS.json')]
    put(HERE / 'INPUT_ASSEMBLY.json', {
        'schema': 'cell05_connections14_local_input_assembly_v1', 'status': 'SOURCE_ONLY_NOT_RUN',
        'origins': [{'path': str(path.relative_to(REPO)), **pin(path.read_bytes())} for path in origins],
        'unchanged_helper_files': [{'member': name, **pin((HERE / name).read_bytes())} for name in HELPERS],
        'targets': 14, 'expected_new_steps': 42, 'accepted_new_steps': 0,
        'provider_suppliers': 88, 'actual_supplier_union': 83,
        'source_bytes': sum(row['source']['bytes'] for row in targets),
        'audit_bytes': sum(row['audit']['bytes'] for row in targets),
        'Lean_commands': 0, 'P1_network_required': False, 'row_capsule_required': False})
    print(json.dumps({'status': 'FIELDS_ONLY14_INPUTS_PREPARED_NOT_RUN', 'targets': 14,
                      'provider_suppliers': 88, 'actual_supplier_union': 83,
                      'new_Lean_acceptances': 0, 'Lean_commands': 0}))


if __name__ == '__main__':
    main()
