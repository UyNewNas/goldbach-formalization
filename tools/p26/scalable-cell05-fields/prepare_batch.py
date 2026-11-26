#!/usr/bin/env python3
"""Package one authored field batch, complete owned audits and exact source pins.

This tool produces source-only review inputs. It never submits or executes a
Lean proof command and never creates a replacement accepted supplier object.
"""
from pathlib import Path, PurePosixPath
import argparse
import ast
import io
import json
import re
import sys
import tarfile

sys.dont_write_bytecode = True
from generate_arrays import HERE, REPO, fp, frozen_prior, pin, write_new

DOCS = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-fields'


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
    old_registry = json.loads((HERE.parent / 'scalable-cell05-complete/SUPPLIER_REGISTRY.json').read_text())
    accepted = {row['module']: row for row in old_registry['suppliers']}
    owners = {row['module']: row for row in source['owners']}
    assert len(owners) == source['owner_count']
    externals = {}

    def visit(module, active=None):
        active = set() if active is None else active
        assert module not in active, ('Import cycle', module)
        if module in owners or module in externals:
            return
        path = REPO / (module.replace('.', '/') + '.lean')
        data = path.read_bytes()
        imports = re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', data.decode())
        if module in accepted:
            row = accepted[module]
            assert pin(path) == row['source'] and imports == row['project_imports']
            external = {**row, 'acceptance': 'ACCEPTED_PUBLISHED_SUPPLIER', 'source_path': str(path.relative_to(REPO))}
        else:
            external = {'module': module, 'source': pin(path), 'source_path': str(path.relative_to(REPO)),
                        'object': None, 'project_imports': imports,
                        'acceptance': 'SOURCE_ONLY_DEPENDENCY_REQUIRES_NORMAL_KERNEL_OWNED', 'must_not_assume_accepted': True}
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
        assert set(row['project_imports']) <= available, ('Batch order is not topological', module)
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)', path.read_text())
        available.add(module)
        audit = batch / 'owned-audits' / (module.split('.')[-1] + '.lean')
        write_new(audit, template.replace(template_module, module))
        targets.append({'module': module, 'source': pin(path),
                        'source_member': 'sources/' + module.replace('.', '/') + '.lean',
                        'audit': pin(audit), 'audit_member': 'tools/p26/scalable-cell05-fields/' + str(audit.relative_to(HERE)),
                        'project_imports': row['project_imports'], 'scope': row['scope'],
                        'normal_kernel_full_owned_required': True, 'accepted': False})
    supplier_manifest = {'schema': 'cell05_fields_batch_supplier_pins_v1', 'batch': args.batch,
                         'suppliers': [externals[module] for module in sorted(externals)],
                         'accepted_supplier_count': sum(row['acceptance'] == 'ACCEPTED_PUBLISHED_SUPPLIER' for row in externals.values()),
                         'pending_supplier_count': sum(row['acceptance'] != 'ACCEPTED_PUBLISHED_SUPPLIER' for row in externals.values()),
                         'old_supplier_objects_must_not_be_recompiled': True,
                         'published_evidence_archives': json.loads((HERE.parent / 'scalable-cell05-complete/BASELINE_EVIDENCE.json').read_text())['archives'],
                         'runtime_binaries': old_registry['runtime_binaries']}
    write_new(batch / 'SUPPLIER_PINS.json', supplier_manifest)
    manifest = {'schema': 'cell05_fields_authored_batch_v1', 'batch': args.batch,
                'status': 'SOURCE_ONLY_NOT_COMPILED', 'targets': targets, 'target_count': len(targets),
                'expected_new_steps': 3 * len(targets), 'normal_steps_accepted': 0,
                'kernel_steps_accepted': 0, 'full_owned_steps_accepted': 0,
                'source_manifest': fp(batch / 'SOURCE_MANIFEST.json'), 'supplier_manifest': fp(batch / 'SUPPLIER_PINS.json'),
                'full_owned_audit_template': fp(template_path), 'original_input': source['original_input'],
                'source_generator': fp(HERE / 'generate_arrays.py'), 'package_generator': fp(Path(__file__)),
                'old_checkpoints_unchanged': len(protected), 'raw_parser_changed': False, 'typed_decoder_changed': False,
                'whole_geometry_decoded': False, 'geometry_or_integral_semantics_claimed': False,
                'P2_6_complete': False, 'root_schedules_cloud_jobs': True,
                'future_evidence_export_policy': 'cloud_retained_archive_and_metadata_only'}
    write_new(batch / 'BATCH_MANIFEST.json', manifest)
    for path in [HERE / 'generate_arrays.py', Path(__file__)]:
        ast.parse(path.read_text(), filename=str(path))
    entries = {}
    for row in targets:
        entries[row['source_member']] = REPO / (row['module'].replace('.', '/') + '.lean')
        entries[row['audit_member']] = REPO / row['audit_member']
    for path in sorted(batch.glob('*')):
        if path.is_file():
            entries['tools/p26/scalable-cell05-fields/' + str(path.relative_to(HERE))] = path
    for name in ['README.md', 'PLAN.md', 'generate_arrays.py', 'prepare_batch.py']:
        entries['tools/p26/scalable-cell05-fields/' + name] = HERE / name
    members = [{'member': member, **pin(path)} for member, path in sorted(entries.items())]
    contents = {'schema': 'cell05_fields_source_package_v1', 'batch': args.batch, 'status': 'SOURCE_ONLY_NOT_COMPILED',
                'members': members, 'new_owners': len(targets), 'expected_new_steps': 3 * len(targets),
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
        info.size, info.mode, info.mtime = len(data), 0o644, 0
        archive.addfile(info, io.BytesIO(data))
    listed = {row['member']: row for row in members}
    seen = set()
    with tarfile.open(output, 'r:xz') as archive:
        for item in archive:
            relative = PurePosixPath(item.name)
            assert item.isfile() and not relative.is_absolute() and '..' not in relative.parts and item.name not in seen
            seen.add(item.name)
            data = archive.extractfile(item).read()
            if item.name == 'PACKAGE_CONTENTS.json':
                assert json.loads(data) == contents
            else:
                assert {'bytes': len(data), 'sha256': __import__('hashlib').sha256(data).hexdigest()} == {
                    key: listed[item.name][key] for key in ('bytes', 'sha256')}
    assert seen == set(entries) | {'PACKAGE_CONTENTS.json'}
    assert frozen_prior() == protected
    for member, path in entries.items():
        assert pin(path) == {key: listed[member][key] for key in ('bytes', 'sha256')}
    report = {'schema': 'cell05_fields_local_candidate_check_v1', 'status': 'PASS_SOURCE_AUDIT_PIN_AND_ARCHIVE_CHECKS_ONLY',
              'batch': args.batch, 'owners': len(targets), 'source_bytes': sum(row['source']['bytes'] for row in targets),
              'complete_owned_audits': len(targets), 'accepted_supplier_pins': supplier_manifest['accepted_supplier_count'],
              'pending_supplier_pins': supplier_manifest['pending_supplier_count'], 'archive_members_checked': len(seen),
              'previous_checkpoint_files_unchanged': len(protected), 'new_Lean_steps_run': 0,
              'normal_kernel_owned_accepted': False, 'whole_geometry_decoded': False, 'P2_6_complete': False}
    write_new(docs / 'LOCAL_CHECK.json', report)
    write_new(docs / 'PACKAGE.json', {**contents, 'archive': fp(output), 'local_check': fp(docs / 'LOCAL_CHECK.json')})
    stage = {str(path.relative_to(REPO)) for path in entries.values()}
    stage |= {str(path.relative_to(REPO)) for path in docs.iterdir() if path.is_file()}
    handoff = docs / 'HANDOFF_STAGING_FILES.txt'
    stage.add(str(handoff.relative_to(REPO)))
    write_new(handoff, '\n'.join(sorted(stage)) + '\n')
    print(json.dumps({'batch': args.batch, 'status': 'SOURCE_ONLY_READY_FOR_CHECKPOINT', 'archive': fp(output),
                      'new_owners': len(targets), 'full_owned_audits': len(targets), 'accepted_supplier_pins': supplier_manifest['accepted_supplier_count'],
                      'pending_supplier_pins': supplier_manifest['pending_supplier_count'],
                      'archive_members': len(seen), 'handoff_files': len(stage), 'new_Lean_steps_run': 0}))


if __name__ == '__main__':
    main()
