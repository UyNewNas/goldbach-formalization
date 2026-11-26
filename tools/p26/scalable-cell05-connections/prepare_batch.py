#!/usr/bin/env python3
"""Freeze a connection source batch, audits and pending supplier evidence.

Only local authoring/integrity checks run here. No Lean process is invoked.
"""
from pathlib import Path, PurePosixPath
import argparse
import ast
import hashlib
import io
import json
import re
import shutil
import sys
import tarfile

sys.dont_write_bytecode = True
from generate_connections import HERE, REPO, fp, frozen_prior, pin, write_new

DOCS = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-connections'
BACKUP = Path('/workspace/scratch/59264dd64286/p26-transfer')
PHASE1_JOB = 'job_03820698aca949449a3c8543e9bb8652'


def source_imports(path):
    return re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', path.read_text())


def add_source_registry(registry, path, label):
    data = json.loads(path.read_text())
    for row in data['owners']:
        assert row['module'] not in registry
        registry[row['module']] = {'row': row, 'label': label, 'manifest': fp(path)}


def archive_readback(output, entries, contents):
    listed = {row['member']: row for row in contents['members']}
    seen = set()
    with tarfile.open(output, 'r:xz') as archive:
        for item in archive:
            relative = PurePosixPath(item.name)
            assert item.isfile() and not relative.is_absolute() and '..' not in relative.parts
            assert item.name not in seen, ('Duplicate archive member', item.name)
            seen.add(item.name)
            data = archive.extractfile(item).read()
            if item.name == 'PACKAGE_CONTENTS.json':
                assert json.loads(data) == contents
            else:
                assert {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()} == {
                    key: listed[item.name][key] for key in ('bytes', 'sha256')}
                assert data == entries[item.name].read_bytes()
    assert seen == set(entries) | {'PACKAGE_CONTENTS.json'}
    return len(seen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch', required=True)
    args = parser.parse_args()
    assert re.fullmatch(r'[a-z0-9_]+', args.batch)
    batch = HERE / 'batches' / args.batch
    source = json.loads((batch / 'SOURCE_MANIFEST.json').read_text())
    assert source['batch'] == args.batch and source['status'] == 'SOURCE_ONLY_NOT_COMPILED'
    protected = frozen_prior()
    assert protected == source['protected_previous_files']
    old_registry_path = HERE.parent / 'scalable-cell05-complete/SUPPLIER_REGISTRY.json'
    old_registry = json.loads(old_registry_path.read_text())
    accepted = {row['module']: row for row in old_registry['suppliers']}
    source_registry = {}
    add_source_registry(source_registry, HERE.parent / 'scalable-cell05-complete/ROW_NETWORK_SOURCE_MANIFEST.json',
                        'PHASE1_RUN_REPORTED_PASS_EXACT_OBJECT_RECEIPT_JOIN_PENDING')
    add_source_registry(source_registry, HERE.parent / 'scalable-cell05-fields/FIELDS_SOURCE_MANIFEST.json',
                        'FIELDS73_SOURCE_ONLY_MATHEMATICAL_ACCEPTANCE_PENDING')
    for prior in sorted((HERE / 'batches').glob('*/SOURCE_MANIFEST.json')):
        if prior.parent.name != args.batch:
            add_source_registry(source_registry, prior, 'CONNECTION_SOURCE_ONLY_MATHEMATICAL_ACCEPTANCE_PENDING')
    owners = {row['module']: row for row in source['owners']}
    assert len(owners) == source['owner_count']
    externals = {}

    def visit(module, active=None):
        active = set() if active is None else active
        assert module not in active, ('Import cycle', module)
        if module in owners or module in externals:
            return
        path = REPO / (module.replace('.', '/') + '.lean')
        imports = source_imports(path)
        if module in accepted:
            row = accepted[module]
            assert pin(path) == row['source'] and imports == row['project_imports']
            external = {**row, 'acceptance': 'ACCEPTED_PUBLISHED_SUPPLIER',
                        'source_path': str(path.relative_to(REPO)), 'exact_new_evidence_join_pending': False}
        else:
            assert module in source_registry, ('Unknown non-accepted source supplier', module)
            frozen = source_registry[module]
            row = frozen['row']
            assert pin(path) == {key: row['source'][key] for key in ('bytes', 'sha256')}
            assert imports == row['project_imports']
            external = {'module': module, 'source': pin(path), 'source_path': str(path.relative_to(REPO)),
                        'object': None, 'receipts': None, 'project_imports': imports,
                        'acceptance': frozen['label'], 'source_manifest': frozen['manifest'],
                        'exact_new_evidence_join_pending': True, 'must_not_assume_accepted': True,
                        'recompile_to_fill_missing_pin_forbidden': True}
            if frozen['label'].startswith('PHASE1_'):
                external['reported_success'] = {'task_id': PHASE1_JOB, 'new_owners': 15, 'new_steps': 45,
                                                'reported_by': 'parent_agent', 'local_receipt_join': False}
        external['textual_declarations'] = re.findall(
            r'(?m)^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|structure|inductive)\s+([A-Za-z0-9_\u0080-\uffff\'.]+)',
            path.read_text())
        externals[module] = external
        active.add(module)
        for dependency in imports:
            visit(dependency, active)
        active.remove(module)

    for row in source['owners']:
        for dependency in row['project_imports']:
            visit(dependency)
    available = set(externals)
    template_module = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput'
    template_path = HERE.parent / 'scalable/owned-audits' / (template_module.split('.')[-1] + '.lean')
    template = template_path.read_text()
    targets = []
    for row in source['owners']:
        module = row['module']
        path = REPO / (module.replace('.', '/') + '.lean')
        assert pin(path) == {key: row['source'][key] for key in ('bytes', 'sha256')}
        assert source_imports(path) == row['project_imports']
        assert set(row['project_imports']) <= available, ('Batch order is not topological', module)
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)', path.read_text())
        available.add(module)
        audit = batch / 'owned-audits' / (module.split('.')[-1] + '.lean')
        write_new(audit, template.replace(template_module, module))
        targets.append({'module': module, 'source': pin(path),
                        'source_member': 'sources/' + module.replace('.', '/') + '.lean',
                        'audit': pin(audit), 'audit_member': str(audit.relative_to(REPO)),
                        'project_imports': row['project_imports'], 'scope': row['scope'],
                        'normal_kernel_full_owned_required': True, 'accepted': False})
    supplier_manifest = {
        'schema': 'cell05_connection_supplier_sources_and_pending_objects_v1', 'batch': args.batch,
        'suppliers': [externals[module] for module in sorted(externals)],
        'accepted_supplier_count': sum(row['acceptance'] == 'ACCEPTED_PUBLISHED_SUPPLIER' for row in externals.values()),
        'pending_supplier_count': sum(row['acceptance'] != 'ACCEPTED_PUBLISHED_SUPPLIER' for row in externals.values()),
        'required_array_root_interfaces': source.get('array_roots', {}),
        'textual_declaration_inventory_is_Lean_elaboration': False,
        'old_supplier_objects_must_not_be_recompiled': True, 'execution_requires_exact_pending_object_receipt_join': True,
        'published_supplier_registry': fp(old_registry_path),
        'published_evidence_archives': json.loads((HERE.parent / 'scalable-cell05-complete/BASELINE_EVIDENCE.json').read_text())['archives'],
        'runtime_binaries': old_registry['runtime_binaries']}
    write_new(batch / 'SUPPLIER_PINS.json', supplier_manifest)
    manifest = {
        'schema': 'cell05_connections_authored_batch_v1', 'batch': args.batch,
        'status': 'SOURCE_ONLY_NOT_COMPILED', 'targets': targets, 'target_count': len(targets),
        'expected_new_steps': 3 * len(targets), 'normal_steps_accepted': 0,
        'kernel_steps_accepted': 0, 'full_owned_steps_accepted': 0,
        'source_manifest': fp(batch / 'SOURCE_MANIFEST.json'), 'supplier_manifest': fp(batch / 'SUPPLIER_PINS.json'),
        'full_owned_audit_template': fp(template_path), 'original_input': source['original_input'],
        'source_generator': source['generator'], 'package_generator': fp(Path(__file__)),
        'old_checkpoints_unchanged': len(protected), 'raw_parser_changed': False, 'typed_decoder_changed': False,
        'whole_geometry_decoded_accepted': False, 'geometry_or_integral_semantics_claimed': False,
        'P2_6_complete': False, 'root_schedules_cloud_jobs': True,
        'future_evidence_export_policy': 'cloud_retained_archive_and_metadata_only'}
    write_new(batch / 'BATCH_MANIFEST.json', manifest)
    entries = {}
    for row in targets:
        entries[row['source_member']] = REPO / (row['module'].replace('.', '/') + '.lean')
        entries[row['audit_member']] = REPO / row['audit_member']
    for path in sorted(batch.glob('*')):
        if path.is_file():
            entries[str(path.relative_to(REPO))] = path
    for path in sorted(HERE.glob('*')):
        if path.is_file() and path.suffix in ('.md', '.py'):
            entries[str(path.relative_to(REPO))] = path
            if path.suffix == '.py':
                ast.parse(path.read_text(), filename=str(path))
    members = [{'member': member, **pin(path)} for member, path in sorted(entries.items())]
    contents = {'schema': 'cell05_connections_source_package_v1', 'batch': args.batch,
                'status': 'SOURCE_ONLY_NOT_COMPILED', 'members': members,
                'new_owners': len(targets), 'expected_new_steps': 3 * len(targets),
                'new_Lean_steps_run': 0, 'normal_kernel_owned_accepted': False}
    docs = DOCS / args.batch
    docs.mkdir(parents=True, exist_ok=True)
    output = docs / (args.batch + '-source-candidates-v1.tar.xz')
    assert not output.exists()
    with tarfile.open(output, 'w:xz', preset=6) as archive:
        for member, path in sorted(entries.items()):
            data = path.read_bytes()
            info = tarfile.TarInfo(member)
            info.type, info.size, info.mode, info.mtime = tarfile.REGTYPE, len(data), 0o644, 0
            archive.addfile(info, io.BytesIO(data))
        data = (json.dumps(contents, indent=2) + '\n').encode()
        info = tarfile.TarInfo('PACKAGE_CONTENTS.json')
        info.type, info.size, info.mode, info.mtime = tarfile.REGTYPE, len(data), 0o644, 0
        archive.addfile(info, io.BytesIO(data))
    member_count = archive_readback(output, entries, contents)
    assert frozen_prior() == protected
    for row in members:
        assert pin(entries[row['member']]) == {key: row[key] for key in ('bytes', 'sha256')}
    report = {
        'schema': 'cell05_connections_local_candidate_check_v1',
        'status': 'PASS_SOURCE_AUDIT_PIN_AND_ARCHIVE_CHECKS_ONLY', 'batch': args.batch,
        'owners': len(targets), 'source_bytes': sum(row['source']['bytes'] for row in targets),
        'complete_owned_audits': len(targets),
        'accepted_supplier_pins': supplier_manifest['accepted_supplier_count'],
        'pending_supplier_pins': supplier_manifest['pending_supplier_count'],
        'archive_members_checked': member_count, 'previous_checkpoint_files_unchanged': len(protected),
        'original_fields': 14, 'original_input_bytes': 201042, 'vertices_host_plan': 28, 'rows_host_plan': 56,
        'new_Lean_steps_run': 0, 'normal_kernel_owned_accepted': False,
        'whole_geometry_decoded_accepted': False, 'P2_6_complete': False}
    write_new(docs / 'LOCAL_CHECK.json', report)
    write_new(docs / 'PACKAGE.json', {**contents, 'archive': fp(output), 'local_check': fp(docs / 'LOCAL_CHECK.json')})
    stage = {str(path.relative_to(REPO)) for path in entries.values()}
    stage |= {str(path.relative_to(REPO)) for path in docs.iterdir() if path.is_file()}
    handoff = docs / 'HANDOFF_STAGING_FILES.txt'
    stage.add(str(handoff.relative_to(REPO)))
    write_new(handoff, '\n'.join(sorted(stage)) + '\n')
    backup = BACKUP / ('cell05-connections-' + args.batch + '-v1')
    backup.mkdir(parents=True, exist_ok=True)
    for path in sorted(docs.iterdir()):
        if path.is_file():
            target = backup / path.name
            write_new(target, path.read_bytes())
            assert pin(target) == pin(path)
    print(json.dumps({'batch': args.batch, 'status': 'SOURCE_ONLY_READY_FOR_CHECKPOINT',
                      'archive': fp(output), 'backup_archive': str(backup / output.name),
                      'new_owners': len(targets), 'full_owned_audits': len(targets),
                      'accepted_supplier_pins': supplier_manifest['accepted_supplier_count'],
                      'pending_supplier_pins': supplier_manifest['pending_supplier_count'],
                      'archive_members': member_count, 'handoff_files': len(stage), 'new_Lean_steps_run': 0}))


if __name__ == '__main__':
    main()
