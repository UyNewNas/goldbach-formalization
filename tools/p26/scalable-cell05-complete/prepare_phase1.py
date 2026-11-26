#!/usr/bin/env python3
"""Freeze the recovered phase1 candidate and run local workflow-only checks."""
from pathlib import Path, PurePosixPath
import ast
import hashlib
import io
import json
import re
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
from prepare_baseline import fp, pin, protected_files, write_new
from baseline_checks import verify_baseline

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DOCS = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-complete'
WORKFLOW = ['BASELINE_EVIDENCE.json', 'SUPPLIER_REGISTRY.json', 'ROW_NETWORK_SOURCE_MANIFEST.json',
            'row_network_order.txt', 'PLAN.md', 'README.md', 'baseline_checks.py', 'export_phase1.py',
            'generate_rows.py', 'prepare_baseline.py', 'prepare_phase1.py', 'receipt_checks.py',
            'receipt_support.py', 'test_workflow.py', 'verify_phase1.py']


def main():
    baseline_manifest = json.loads((HERE / 'BASELINE_EVIDENCE.json').read_text())
    before = protected_files()
    assert before == baseline_manifest['published_files']
    baseline = verify_baseline(HERE)
    source_manifest = json.loads((HERE / 'ROW_NETWORK_SOURCE_MANIFEST.json').read_text())
    registry = json.loads((HERE / 'SUPPLIER_REGISTRY.json').read_text())
    owners = source_manifest['owners']
    assert len(owners) == len({row['module'] for row in owners}) == 15
    assert source_manifest['status'] == 'SOURCE_ONLY_NOT_COMPILED'
    assert source_manifest['input']['bytes'] == 201042
    assert source_manifest['input']['sha256'] == 'e601ac9ceda569646f06a64f4baddcf9cd405cde1e377a323a238ad4e4681b82'
    assert source_manifest['published_files'] == before
    template_name = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput'
    template = (REPO / 'tools/p26/scalable/owned-audits' / (template_name.split('.')[-1] + '.lean')).read_text()
    graph = {row['module']: row['project_imports'] for row in owners + registry['suppliers']}
    targets = []
    available = {row['module'] for row in registry['suppliers']}
    for row in owners:
        module = row['module']
        source = REPO / (module.replace('.', '/') + '.lean')
        assert {key: fp(source)[key] for key in ('bytes', 'sha256')} == {key: row['source'][key] for key in ('bytes', 'sha256')}
        text = source.read_text()
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)', text)
        assert re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', text) == row['project_imports']
        assert set(row['project_imports']) <= available
        available.add(module)
        audit_relative = 'owned-audits/' + module.split('.')[-1] + '.lean'
        audit = HERE / audit_relative
        write_new(audit, template.replace(template_name, module))
        closure, active = set(), set()

        def visit(dependency):
            assert dependency in graph and dependency not in active
            if dependency in closure:
                return
            active.add(dependency)
            for parent in graph[dependency]:
                visit(parent)
            active.remove(dependency)
            closure.add(dependency)

        for dependency in row['project_imports']:
            visit(dependency)
        targets.append({'module': module, 'source': pin(source.read_bytes()),
                        'source_member': 'sources/' + module.replace('.', '/') + '.lean',
                        'audit': pin(audit.read_bytes()), 'audit_relative_path': audit_relative,
                        'project_imports': row['project_imports'], 'transitive_dependencies': sorted(closure)})
    for name in WORKFLOW:
        if name.endswith('.py'):
            ast.parse((HERE / name).read_text(), filename=name)
    verifier = {'schema': 'cell05_complete_frozen_verifier_v2', 'status': 'SOURCE_ONLY_NOT_COMPILED',
                'workflow_files': [{'relative_path': name, **pin((HERE / name).read_bytes())} for name in WORKFLOW],
                'targets': targets, 'target_count': 15, 'expected_new_proof_steps': 45,
                'normal_kernel_owned_accepted': False, 'old_supplier_proof_commands': 0,
                'whole_geometry_decoded': False, 'P2_6_complete': False,
                'new_evidence_full_archive_automatic_transfer': False}
    write_new(HERE / 'ROW_NETWORK_VERIFIER.json', verifier)
    from verify_phase1 import load_configuration
    checked, _, _ = load_configuration(HERE)
    assert checked == verifier
    proc = subprocess.run([sys.executable, str(HERE / 'test_workflow.py')], text=True, capture_output=True)
    log = proc.stdout + proc.stderr
    assert proc.returncode == 0, log
    tests = re.findall(r'(?m)^(test_\S+) .* \.\.\. ok$', log)
    assert len(tests) >= 32, (len(tests), log)
    DOCS.mkdir(parents=True, exist_ok=True)
    regression_log = DOCS / 'PHASE1_WORKFLOW_REGRESSIONS_V2.log'
    # Test timing is an observation, not part of immutable source package bytes.
    with regression_log.open('x') as stream:
        stream.write(log)
    entries = {}
    for target in targets:
        entries[target['source_member']] = REPO / (target['module'].replace('.', '/') + '.lean')
        entries['tools/p26/scalable-cell05-complete/' + target['audit_relative_path']] = HERE / target['audit_relative_path']
    for name in WORKFLOW + ['ROW_NETWORK_VERIFIER.json']:
        entries['tools/p26/scalable-cell05-complete/' + name] = HERE / name
    for row in baseline_manifest['members']:
        entries['tools/p26/scalable-cell05-complete/' + row['relative_path']] = HERE / row['relative_path']
    members = [{'member': name, **pin(path.read_bytes())} for name, path in sorted(entries.items())]
    package_contents = {'schema': 'cell05_complete_source_package_contents_v2', 'status': 'SOURCE_ONLY_NOT_COMPILED',
                        'members': members, 'new_owners': 15, 'old_suppliers': 15, 'baseline_members': 154,
                        'new_Lean_steps_run': 0, 'new_owner_acceptance_claimed': False}
    output = DOCS / 'row-network-source-package-v2.tar.xz'
    assert not output.exists(), 'Refuse to overwrite a frozen source package'
    with tarfile.open(output, 'w:xz', preset=6) as archive:
        for member, path in sorted(entries.items()):
            data = path.read_bytes()
            info = tarfile.TarInfo(member)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            archive.addfile(info, io.BytesIO(data))
        data = (json.dumps(package_contents, indent=2) + '\n').encode()
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
                assert json.loads(data) == package_contents
            else:
                assert pin(data) == {key: listed[item.name][key] for key in ('bytes', 'sha256')}
    assert seen == set(entries) | {'PACKAGE_CONTENTS.json'}
    for member, path in entries.items():
        assert pin(path.read_bytes()) == {key: listed[member][key] for key in ('bytes', 'sha256')}
    assert protected_files() == before
    local_check = {'schema': 'cell05_complete_local_candidate_check_v2', 'status': 'PASS_LOCAL_SOURCE_AND_WORKFLOW_CHECKS_ONLY',
                   'baseline': baseline, 'new_sources': 15, 'new_source_bytes': sum(row['source']['bytes'] for row in targets),
                   'source_and_import_pins_checked': True, 'old_70_files_unchanged': True,
                   'synthetic_workflow_regressions_passed': len(tests), 'synthetic_test_names': tests,
                   'synthetic_regression_log': fp(regression_log), 'archive_members_checked': len(seen),
                   'new_Lean_steps_run': 0, 'normal_kernel_owned_accepted': False,
                   'whole_geometry_decoded': False, 'P2_6_complete': False}
    write_new(DOCS / 'PHASE1_LOCAL_CHECK_V2.json', local_check)
    write_new(DOCS / 'ROW_NETWORK_PACKAGE_V2.json', {**package_contents, 'archive': fp(output),
              'archive_members_including_manifest': len(seen), 'local_check': fp(DOCS / 'PHASE1_LOCAL_CHECK_V2.json')})
    files = sorted({str(path.relative_to(REPO)) for path in HERE.rglob('*') if path.is_file() and '__pycache__' not in path.parts}
                   | {row['module'].replace('.', '/') + '.lean' for row in targets}
                   | {str(path.relative_to(REPO)) for path in DOCS.rglob('*') if path.is_file()})
    handoff = DOCS / 'HANDOFF_STAGING_FILES_V2.txt'
    files.append(str(handoff.relative_to(REPO)))
    write_new(handoff, '\n'.join(sorted(files)) + '\n')
    print(json.dumps({'status': 'SOURCE_ONLY_CANDIDATE_READY_FOR_INDEPENDENT_REVIEW', 'archive': fp(output),
                      'archive_members': len(seen), 'new_owners': 15, 'baseline_members': 154,
                      'synthetic_workflow_regressions_passed': len(tests), 'new_Lean_steps_run': 0,
                      'handoff_files': len(files)}))


if __name__ == '__main__':
    main()
