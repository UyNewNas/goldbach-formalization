#!/usr/bin/env python3
"""Locally adapt the reviewed row workflow v3 to exactly 73 field owners."""
from pathlib import Path, PurePosixPath
import ast
import difflib
import hashlib
import io
import json
import re
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
from generate_arrays import HERE, REPO, fp, frozen_prior, pin, write_new

OLD = HERE.parent / 'scalable-cell05-complete'
DOCS = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-fields/workflow-v1'
BATCHES = ['a_vertices_facets', 'b_active8', 'c_values_faces', 'd_minima']


def main():
    protected = frozen_prior()
    old_verifier = json.loads((OLD / 'ROW_NETWORK_VERIFIER.json').read_text())
    assert old_verifier['workflow_revision'] == 3
    old_pins = {row['relative_path']: row for row in old_verifier['workflow_files']}
    for name in ['receipt_checks.py', 'verify_phase1.py', 'export_phase1.py', 'test_workflow.py',
                 'baseline_checks.py', 'receipt_support.py', 'BASELINE_EVIDENCE.json', 'SUPPLIER_REGISTRY.json']:
        assert pin(OLD / name) == {key: old_pins[name][key] for key in ('bytes', 'sha256')}
    mappings = {'receipt_checks.py': 'receipt_checks.py', 'verify_phase1.py': 'verify_fields.py',
                'export_phase1.py': 'export_fields.py', 'test_workflow.py': 'test_workflow.py',
                'baseline_checks.py': 'baseline_checks.py', 'receipt_support.py': 'receipt_support.py'}
    adaptations, diff = [], []
    for old_name, new_name in mappings.items():
        original = (OLD / old_name).read_text()
        text = original
        changes = []

        def replace(before, after):
            nonlocal text
            assert before in text, (old_name, before)
            changes.append({'before': before, 'after': after, 'occurrences': text.count(before)})
            text = text.replace(before, after)

        if old_name == 'receipt_checks.py':
            replace('tools/p26/scalable-cell05-complete', 'tools/p26/scalable-cell05-fields')
            replace('== 15', '== 73')
            replace('Exactly 15 new owners required', 'Exactly 73 new owners required')
            replace('== 45', '== 219')
            replace('45-step order/coverage mismatch', '219-step order/coverage mismatch')
        elif old_name == 'verify_phase1.py':
            replace('Run only 15 supplied new owners', 'Run only 73 supplied new owners')
            replace('ROW_NETWORK_VERIFIER.json', 'FIELDS_VERIFIER.json')
            replace('ROW_NETWORK_SOURCE_MANIFEST.json', 'FIELDS_SOURCE_MANIFEST.json')
            replace('cell05_complete_frozen_verifier_v2', 'cell05_fields_frozen_verifier_v1')
            replace("len(source_manifest['owners']) == 15, 'Expected 15 new owners'", "len(source_manifest['owners']) == 73, 'Expected 73 new owners'")
            replace("len(source_rows) == 15, 'Duplicate new source module'", "len(source_rows) == 73, 'Duplicate new source module'")
            replace("'accepted_targets': 15, 'accepted_steps': 45", "'accepted_targets': 73, 'accepted_steps': 219")
        elif old_name == 'export_phase1.py':
            replace('recheck 45 receipt chains', 'recheck 219 receipt chains')
            replace('Only the 15 new object bodies', 'Only the 73 new object bodies')
            replace('from verify_phase1 import', 'from verify_fields import')
            replace("default='v2'", "default='v1'")
            replace('ROW_NETWORK_VERIFIER.json', 'FIELDS_VERIFIER.json')
            replace('len(archived_objects) == 15', 'len(archived_objects) == 73')
            replace('FIFTEEN_NEW_OWNERS', 'SEVENTY_THREE_NEW_OWNERS')
            replace("'accepted_targets': 15, 'accepted_steps': 45", "'accepted_targets': 73, 'accepted_steps': 219")
            replace("'step_counts': {'normal': 15, 'kernel': 15, 'owned': 15}", "'step_counts': {'normal': 73, 'kernel': 73, 'owned': 73}")
            replace("'baseline': baseline, 'row_interval_newly_supplied': [16, 56], 'assembled_row_interval': [0, 56],",
                    "'baseline': baseline, 'original_nonrow_arrays': ['active8_enumeration', 'vertices', 'vertex_values',\n" +
                    "                    'all_original_constraint_minima', 'facet_vertices', 'face_ledger'],\n" +
                    "                'metadata_prefix_fields': 5, 'row_count_host_plan': 56,")
            replace("f'phase1-{args.attempt}-{args.label}-evidence.tar.xz'", "f'fields-{args.attempt}-{args.label}-evidence.tar.xz'")
            replace('cell05_complete_cloud_export_v2', 'cell05_fields_cloud_export_v1')
            replace('cell05_complete_cloud_export_report_v2', 'cell05_fields_cloud_export_report_v1')
        elif old_name == 'test_workflow.py':
            replace('from export_phase1 import', 'from export_fields import')
            replace('test_success_45_chains_resume_counts_and_export_gate', 'test_success_219_chains_resume_counts_and_export_gate')
            replace('Fixture(15)', 'Fixture(73)')
            replace("'accepted_targets': 15, 'accepted_steps': 45", "'accepted_targets': 73, 'accepted_steps': 219")
            replace("'reused_steps': 45", "'reused_steps': 219")
            replace('len(steps), 45', 'len(steps), 219')
            replace("value['newly_executed_steps'] = 45", "value['newly_executed_steps'] = 219")
        ast.parse(text, filename=new_name)
        write_new(HERE / new_name, text)
        adaptations.append({'source': fp(OLD / old_name), 'destination': fp(HERE / new_name), 'literal_replacements': changes})
        diff.extend(difflib.unified_diff(original.splitlines(keepends=True), text.splitlines(keepends=True),
                                       fromfile='reviewed-v3/' + old_name, tofile='fields-v1/' + new_name))
    write_new(HERE / 'workflow/v3-to-fields.diff', ''.join(diff))
    for name in ['SUPPLIER_REGISTRY.json', 'BASELINE_EVIDENCE.json']:
        write_new(HERE / name, (OLD / name).read_bytes())
    baseline_manifest = json.loads((OLD / 'BASELINE_EVIDENCE.json').read_text())
    for row in baseline_manifest['members']:
        write_new(HERE / row['relative_path'], (OLD / row['relative_path']).read_bytes())
    assert len(baseline_manifest['members']) == 154
    owners, batch_pins, target_rows = [], [], []
    for name in BATCHES:
        batch = HERE / 'batches' / name
        source = json.loads((batch / 'SOURCE_MANIFEST.json').read_text())
        authored = json.loads((batch / 'BATCH_MANIFEST.json').read_text())
        assert source['status'] == authored['status'] == 'SOURCE_ONLY_NOT_COMPILED'
        assert source['protected_previous_files'] == protected
        owners.extend(source['owners'])
        batch_pins.append({'batch': name, 'source_manifest': fp(batch / 'SOURCE_MANIFEST.json'),
                           'authored_manifest': fp(batch / 'BATCH_MANIFEST.json')})
        for row in authored['targets']:
            module = row['module']
            source_path = REPO / (module.replace('.', '/') + '.lean')
            audit_path = REPO / row['audit_member']
            assert pin(source_path) == row['source'] and pin(audit_path) == row['audit']
            audit_relative = 'owned-audits/' + module.split('.')[-1] + '.lean'
            write_new(HERE / audit_relative, audit_path.read_bytes())
            target_rows.append({'module': module, 'source': row['source'], 'source_member': row['source_member'],
                                'audit': row['audit'], 'audit_relative_path': audit_relative,
                                'project_imports': row['project_imports']})
    assert len(owners) == len({row['module'] for row in owners}) == len(target_rows) == 73
    write_new(HERE / 'FIELDS_SOURCE_MANIFEST.json', {'schema': 'cell05_fields_all_array_sources_v1',
              'status': 'SOURCE_ONLY_NOT_COMPILED', 'owners': owners, 'owner_count': 73,
              'original_batches': batch_pins, 'original_input': source['original_input'],
              'original_input_bytes': 201042, 'vertices_host_plan': 28, 'rows_host_plan': 56,
              'business_sources_and_audits_unchanged_from_four_authored_batches': True,
              'normal_kernel_owned_accepted': False, 'whole_geometry_decoded': False, 'P2_6_complete': False})
    registry = json.loads((HERE / 'SUPPLIER_REGISTRY.json').read_text())
    graph = {row['module']: row['project_imports'] for row in registry['suppliers'] + target_rows}
    available = {row['module'] for row in registry['suppliers']}
    for row in target_rows:
        assert set(row['project_imports']) <= available, row['module']
        available.add(row['module'])
        closure, active = set(), set()

        def visit(module):
            assert module in graph and module not in active
            if module in closure:
                return
            active.add(module)
            for dependency in graph[module]:
                visit(dependency)
            active.remove(module)
            closure.add(module)

        for dependency in row['project_imports']:
            visit(dependency)
        row['transitive_dependencies'] = sorted(closure)
    write_new(HERE / 'FIELD_WORKFLOW_ADAPTATION.json', {'schema': 'cell05_fields_workflow_adaptation_v1',
              'source_workflow': fp(OLD / 'ROW_NETWORK_VERIFIER.json'), 'source_workflow_revision': 3,
              'adaptations': adaptations, 'diff': fp(HERE / 'workflow/v3-to-fields.diff'),
              'target_change': [15, 73], 'required_step_change': [45, 219], 'supplier_count_unchanged': 15,
              'baseline_capsule_unchanged': 154, 'strict_guards_removed_or_relaxed': False,
              'business_Lean_changed': False, 'old_supplier_Lean_reexecuted': False})
    workflow = ['receipt_checks.py', 'verify_fields.py', 'export_fields.py', 'test_workflow.py',
                'baseline_checks.py', 'receipt_support.py', 'BASELINE_EVIDENCE.json', 'SUPPLIER_REGISTRY.json',
                'FIELDS_SOURCE_MANIFEST.json', 'FIELD_WORKFLOW_ADAPTATION.json', 'workflow/v3-to-fields.diff',
                'WORKFLOW_README.md', 'prepare_workflow.py', 'generate_arrays.py', 'prepare_batch.py', 'README.md', 'PLAN.md']
    workflow += ['batches/' + batch + '/' + name for batch in BATCHES
                 for name in ['SOURCE_MANIFEST.json', 'BATCH_MANIFEST.json', 'SUPPLIER_PINS.json', 'owner_order.txt']]
    verifier = {'schema': 'cell05_fields_frozen_verifier_v1', 'workflow_revision': 1,
                'status': 'SOURCE_ONLY_NOT_COMPILED', 'targets': target_rows, 'target_count': 73,
                'workflow_files': [{'relative_path': name, **pin(HERE / name)} for name in workflow],
                'expected_new_proof_steps': 219, 'normal_kernel_owned_accepted': False,
                'old_supplier_proof_commands': 0, 'whole_geometry_decoded': False, 'P2_6_complete': False,
                'new_evidence_full_archive_automatic_transfer': False}
    write_new(HERE / 'FIELDS_VERIFIER.json', verifier)
    from verify_fields import load_configuration
    loaded, _, baseline = load_configuration(HERE)
    assert loaded == verifier
    proc = subprocess.run([sys.executable, str(HERE / 'test_workflow.py')], text=True, capture_output=True)
    log = proc.stdout + proc.stderr
    assert proc.returncode == 0, log
    tests = re.findall(r'(?m)^(test_\S+) .* \.\.\. ok$', log)
    assert len(tests) == 34
    DOCS.mkdir(parents=True, exist_ok=True)
    log_path = DOCS / 'WORKFLOW_REGRESSIONS.log'
    write_new(log_path, log)
    entries = {}
    for row in target_rows:
        entries[row['source_member']] = REPO / (row['module'].replace('.', '/') + '.lean')
        entries['tools/p26/scalable-cell05-fields/' + row['audit_relative_path']] = HERE / row['audit_relative_path']
    for name in workflow + ['FIELDS_VERIFIER.json']:
        entries['tools/p26/scalable-cell05-fields/' + name] = HERE / name
    for row in baseline_manifest['members']:
        entries['tools/p26/scalable-cell05-fields/' + row['relative_path']] = HERE / row['relative_path']
    members = [{'member': member, **pin(path)} for member, path in sorted(entries.items())]
    contents = {'schema': 'cell05_fields_workflow_source_package_v1', 'status': 'SOURCE_ONLY_NOT_COMPILED',
                'members': members, 'new_owners': 73, 'old_suppliers': 15, 'baseline_members': 154,
                'expected_new_steps': 219, 'new_Lean_steps_run': 0, 'normal_kernel_owned_accepted': False}
    output = DOCS / 'fields-73-owner-workflow-v1.tar.xz'
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
                assert {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()} == {key: listed[item.name][key] for key in ('bytes', 'sha256')}
    assert seen == set(entries) | {'PACKAGE_CONTENTS.json'}
    assert frozen_prior() == protected
    for member, path in entries.items():
        assert pin(path) == {key: listed[member][key] for key in ('bytes', 'sha256')}
    report = {'schema': 'cell05_fields_workflow_local_check_v1', 'status': 'PASS_LOCAL_WORKFLOW_AND_SOURCE_PACKAGE_ONLY',
              'targets': 73, 'expected_new_steps': 219, 'business_source_bytes': sum(row['source']['bytes'] for row in target_rows),
              'business_sources_and_audits_unchanged_from_four_batches': True,
              'supplier_count_unchanged': 15, 'baseline_capsule_unchanged': 154, 'baseline': baseline,
              'old_and_row_workflow_files_unchanged': len(protected), 'synthetic_workflow_regressions_passed': 34,
              'synthetic_test_names': tests, 'regression_log': fp(log_path), 'archive_members_checked': len(seen),
              'new_Lean_steps_run': 0, 'normal_kernel_owned_accepted': False, 'whole_geometry_decoded': False, 'P2_6_complete': False}
    write_new(DOCS / 'LOCAL_CHECK.json', report)
    write_new(DOCS / 'PACKAGE.json', {**contents, 'archive': fp(output), 'local_check': fp(DOCS / 'LOCAL_CHECK.json')})
    all_paths = {str(path.relative_to(REPO)) for path in HERE.rglob('*') if path.is_file() and '__pycache__' not in path.parts}
    all_paths |= {row['module'].replace('.', '/') + '.lean' for row in target_rows}
    all_paths |= {str(path.relative_to(REPO)) for path in DOCS.parent.rglob('*') if path.is_file()}
    handoff = DOCS / 'HANDOFF_STAGING_FILES.txt'
    all_paths.add(str(handoff.relative_to(REPO)))
    write_new(handoff, '\n'.join(sorted(all_paths)) + '\n')
    print(json.dumps({'status': 'SOURCE_ONLY_73_OWNER_WORKFLOW_READY_FOR_REVIEW', 'archive': fp(output),
                      'archive_members': len(seen), 'targets': 73, 'expected_new_steps': 219,
                      'synthetic_workflow_regressions_passed': 34, 'new_Lean_steps_run': 0,
                      'handoff_paths': len(all_paths)}))


if __name__ == '__main__':
    main()
