#!/usr/bin/env python3
"""Freeze workflow v3 after two reproduced review failures; preserve all Lean."""
from pathlib import Path, PurePosixPath
import ast
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
V2_PIN = {'bytes': 308156, 'sha256': 'f4ac5aafa2a6f39585e01123340c13cb03fe85b11d6f048e2a542d93f676f065'}
SNAPSHOTS = ['README.md', 'receipt_checks.py', 'export_phase1.py', 'test_workflow.py', 'ROW_NETWORK_VERIFIER.json']


def main():
    previous = DOCS / 'row-network-source-package-v2.tar.xz'
    assert pin(previous.read_bytes()) == V2_PIN
    with tarfile.open(previous, 'r:xz') as archive:
        old = {item.name: archive.extractfile(item).read() for item in archive if item.isfile()}
    prefix = 'tools/p26/scalable-cell05-complete/'
    previous_verifier = json.loads(old[prefix + 'ROW_NETWORK_VERIFIER.json'])
    assert (HERE / 'ROW_NETWORK_VERIFIER.json').read_bytes() == old[prefix + 'ROW_NETWORK_VERIFIER.json'], 'Unexpected live verifier drift'
    for name in SNAPSHOTS:
        assert (HERE / 'history/v2' / name).read_bytes() == old[prefix + name]
    protected = protected_files()
    baseline_manifest = json.loads((HERE / 'BASELINE_EVIDENCE.json').read_text())
    assert protected == baseline_manifest['published_files']
    for row in baseline_manifest['members']:
        assert (HERE / row['relative_path']).read_bytes() == old[prefix + row['relative_path']]
    targets = previous_verifier['targets']
    for row in targets:
        assert (REPO / (row['module'].replace('.', '/') + '.lean')).read_bytes() == old[row['source_member']]
        assert (HERE / row['audit_relative_path']).read_bytes() == old[prefix + row['audit_relative_path']]
    workflow = [row['relative_path'] for row in previous_verifier['workflow_files']]
    workflow += ['prepare_revision.py'] + ['history/v2/' + name for name in SNAPSHOTS]
    assert len(workflow) == len(set(workflow))
    for name in workflow:
        if name.endswith('.py'):
            ast.parse((HERE / name).read_text(), filename=name)
    verifier = {**previous_verifier, 'workflow_revision': 3,
                'previous_source_package': V2_PIN, 'business_Lean_and_audit_sources_unchanged_from_v2': True,
                'workflow_files': [{'relative_path': name, **pin((HERE / name).read_bytes())} for name in workflow]}
    # Root authorized a new workflow revision; the old exact verifier is retained
    # in history/v2 and in the immutable v2 archive before replacing this pointer.
    (HERE / 'ROW_NETWORK_VERIFIER.json').write_text(json.dumps(verifier, indent=2) + '\n')
    from verify_phase1 import load_configuration
    loaded, _, baseline = load_configuration(HERE)
    assert loaded == verifier
    proc = subprocess.run([sys.executable, str(HERE / 'test_workflow.py')], text=True, capture_output=True)
    log = proc.stdout + proc.stderr
    assert proc.returncode == 0, log
    tests = re.findall(r'(?m)^(test_\S+) .* \.\.\. ok$', log)
    assert len(tests) == 34, (len(tests), log)
    log_path = DOCS / 'PHASE1_WORKFLOW_REGRESSIONS_V3.log'
    write_new(log_path, log)
    fixes = {'schema': 'cell05_phase1_workflow_review_fixes_v3', 'status': 'TWO_REPRODUCED_FAILURES_FIXED_LOCALLY',
             'previous_source_package': fp(previous),
             'reproductions': [fp(DOCS / name) for name in ['PHASE1_V2_REVIEW_REPRODUCTION.log', 'PHASE1_V2_INDEX_REPRODUCTION.log']],
             'fixes': [
                 {'issue': 'Hardlinked source/project files became nonregular tar members',
                  'change': 'Emit every selected member as REGTYPE TarInfo plus addfile bytes; retain readback and before/after checks',
                  'regression': 'test_hardlinked_source_project_archive_roundtrip'},
                 {'issue': 'Accepted markers survived missing results/objects but result-only lookup returned unexecuted',
                  'change': 'Check results, accepted seals and SUCCESS/STOPPED accepted references; missing or broken links stop preflight and prior',
                  'regression': 'test_seal_without_result_and_object_stops_resume'}],
             'regression_log': fp(log_path), 'synthetic_workflow_tests_passed': 34,
             'business_Lean_sources_unchanged': 15, 'audit_sources_unchanged': 15,
             'baseline_members_unchanged': 154, 'published_files_unchanged': 70,
             'historical_lost_v1_source_total_bytes': 2026333,
             'reconstructed_source_total_bytes': 2026335,
             'byte_identity_with_lost_v1_claimed': False, 'new_Lean_steps_run': 0}
    write_new(DOCS / 'WORKFLOW_REVIEW_FIXES_V3.json', fixes)
    entries = {}
    for row in targets:
        entries[row['source_member']] = REPO / (row['module'].replace('.', '/') + '.lean')
        entries[prefix + row['audit_relative_path']] = HERE / row['audit_relative_path']
    for name in workflow + ['ROW_NETWORK_VERIFIER.json']:
        entries[prefix + name] = HERE / name
    for row in baseline_manifest['members']:
        entries[prefix + row['relative_path']] = HERE / row['relative_path']
    members = [{'member': name, **pin(path.read_bytes())} for name, path in sorted(entries.items())]
    contents = {'schema': 'cell05_complete_source_package_contents_v2', 'workflow_revision': 3,
                'status': 'SOURCE_ONLY_NOT_COMPILED', 'members': members, 'new_owners': 15,
                'old_suppliers': 15, 'baseline_members': 154, 'new_Lean_steps_run': 0,
                'new_owner_acceptance_claimed': False, 'previous_source_package': V2_PIN,
                'business_Lean_and_audit_sources_unchanged_from_v2': True}
    output = DOCS / 'row-network-source-package-v3.tar.xz'
    assert not output.exists(), 'Refuse to overwrite a frozen package'
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
                assert pin(data) == {key: listed[item.name][key] for key in ('bytes', 'sha256')}
    assert seen == set(entries) | {'PACKAGE_CONTENTS.json'}
    for member, path in entries.items():
        assert pin(path.read_bytes()) == {key: listed[member][key] for key in ('bytes', 'sha256')}
    assert protected_files() == protected and pin(previous.read_bytes()) == V2_PIN
    report = {'schema': 'cell05_complete_local_candidate_check_v3', 'status': 'PASS_LOCAL_SOURCE_AND_WORKFLOW_CHECKS_ONLY',
              'baseline': baseline, 'business_sources_unchanged_from_v2': 15, 'audits_unchanged_from_v2': 15,
              'business_source_bytes': sum(row['source']['bytes'] for row in targets),
              'old_70_files_unchanged': True, 'baseline_154_files_unchanged': True,
              'v2_archive_unchanged': True, 'synthetic_workflow_regressions_passed': 34,
              'synthetic_test_names': tests, 'regression_log': fp(log_path),
              'review_fixes': fp(DOCS / 'WORKFLOW_REVIEW_FIXES_V3.json'), 'archive_members_checked': len(seen),
              'new_Lean_steps_run': 0, 'normal_kernel_owned_accepted': False,
              'whole_geometry_decoded': False, 'P2_6_complete': False}
    write_new(DOCS / 'PHASE1_LOCAL_CHECK_V3.json', report)
    write_new(DOCS / 'ROW_NETWORK_PACKAGE_V3.json', {**contents, 'archive': fp(output),
              'archive_members_including_manifest': len(seen), 'local_check': fp(DOCS / 'PHASE1_LOCAL_CHECK_V3.json')})
    files = {str(path.relative_to(REPO)) for path in HERE.rglob('*') if path.is_file() and '__pycache__' not in path.parts}
    files |= {row['module'].replace('.', '/') + '.lean' for row in targets}
    files |= {str(path.relative_to(REPO)) for path in DOCS.rglob('*') if path.is_file()}
    handoff = DOCS / 'HANDOFF_STAGING_FILES_V3.txt'
    files.add(str(handoff.relative_to(REPO)))
    write_new(handoff, '\n'.join(sorted(files)) + '\n')
    print(json.dumps({'status': 'SOURCE_ONLY_WORKFLOW_V3_READY_FOR_REVIEW', 'archive': fp(output),
                      'archive_members': len(seen), 'new_owners': 15, 'business_sources_unchanged_from_v2': True,
                      'synthetic_workflow_regressions_passed': 34, 'new_Lean_steps_run': 0,
                      'handoff_files': len(files)}))


if __name__ == '__main__':
    main()
