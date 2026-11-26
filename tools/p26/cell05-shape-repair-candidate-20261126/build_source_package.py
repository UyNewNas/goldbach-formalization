#!/usr/bin/env python3
"""Freeze the locally authored two-lemma repair with the reviewed isolated runner."""
from pathlib import Path
import ast
import copy
import hashlib
import io
import json
import tarfile

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
TOOL_REL = Path('tools/p26/cell05-shape-repair-20261126')
FRAMEWORK = REPO / TOOL_REL
TARGET = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableShapeArrays'
SOURCE_MEMBER = 'sources/' + TARGET.replace('.', '/') + '.lean'
SOURCE_SHA = 'ec463c113938483a47782ea152bce78308a3983a62865571205c8ead92434796'
DIAGNOSTIC_SHA = '8b1fd277b6501c20de54e1f21275d5430ce7283b04cfc44e5feac8a82b2b3ad5'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def encode(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()


def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)
    need(path.read_bytes() == data, 'Local write changed bytes: ' + str(path))


def main():
    need(not str(ROOT).startswith('/workspace/'), 'The package builder runs locally only')
    boundary = json.loads((FRAMEWORK / 'BOUNDARY.json').read_bytes())
    review = json.loads((FRAMEWORK / 'REVIEW_CANDIDATE.json').read_bytes())
    controls = {row['relative_path']: row for row in review['files']}
    source = (ROOT / SOURCE_MEMBER).read_bytes()
    need(pin(source) == {'bytes': 15299, 'sha256': SOURCE_SHA}, 'Unreviewed replacement source')
    original = (REPO / (TARGET.replace('.', '/') + '.lean')).read_bytes()
    need(pin(original) == boundary['original_target']['source'], 'Original candidate changed')
    expected = original.decode()
    for old, new in [
        ('  simpa only [h.1] using h.2.2\n', '  intro i\n  exact h.2.2 ⟨i.val, h.1 ▸ i.isLt⟩\n'),
        ('  simpa only [h.1] using h.2.2.1\n', '  intro i\n  exact h.2.2.1 ⟨i.val, h.1 ▸ i.isLt⟩\n')]:
        need(expected.count(old) == 1, 'The diagnosed proof site is not unique')
        expected = expected.replace(old, new)
    need(expected.encode() == source, 'Repair changes more than the two diagnosed proof terms')
    diagnostic = (REPO / 'tools/p26/cell05-deployment-20261126/failure-inspection/normal.log').read_bytes()
    need(pin(diagnostic) == {'bytes': 3700, 'sha256': DIAGNOSTIC_SHA}, 'Original failure diagnostic changed')
    names = [row['relative_path'] for row in boundary['shared_helper_pins']] + [
        'verify_shape.py', 'receipt_checks.py', 'export_shape.py', 'stage_entry.py',
        'origin_join.py', 'boundary.py', 'BOUNDARY.json']
    need(len(names) == len(set(names)) == 16, 'Wrong reviewed workflow inventory')
    blobs = {SOURCE_MEMBER: source}
    for name in names:
        data = (FRAMEWORK / name).read_bytes()
        need(pin(data) == {key: controls[name][key] for key in ('bytes', 'sha256')},
             'Reviewed framework changed: ' + name)
        if name.endswith('.py'):
            ast.parse(data, filename=name)
        blobs[str(TOOL_REL / name)] = data
    audit_rel = boundary['original_target']['audit_relative_path']
    original_tool = REPO / 'tools/p26/cell05-connections14-run-20261126/releases/v1/tools/p26/cell05-connections14-run-20261126'
    audit = (original_tool / audit_rel).read_bytes()
    need(pin(audit) == boundary['original_target']['audit'], 'The original complete owned audit changed')
    blobs[str(TOOL_REL / audit_rel)] = audit
    source_manifest = {
        'schema': 'cell05_shape_repair_source_v1', 'module': TARGET,
        'original_source': boundary['original_target']['source'], 'source': pin(source),
        'original_failed_normal_log': pin(diagnostic),
        'changed_theorems': ['facet_shape_of_fixed_size', 'face_shape_of_fixed_size'],
        'statement_changes': 0, 'import_changes': 0, 'accepted_steps': 0,
        'repair_source_ready': True, 'P2_6_complete': False}
    blobs[str(TOOL_REL / 'SHAPE_SOURCE_MANIFEST.json')] = encode(source_manifest)
    target = copy.deepcopy(boundary['original_target'])
    target['source'] = pin(source)
    workflow = [{'relative_path': str(Path(name).relative_to(TOOL_REL)), **pin(data)}
                for name, data in sorted(blobs.items()) if name.startswith(str(TOOL_REL) + '/')]
    need(len(workflow) == 18, 'Wrong frozen workflow count')
    verifier = {
        'schema': 'cell05_shape_repair_frozen_verifier_v1',
        'target_count': 1, 'expected_steps': 3, 'repair_source_ready': True,
        'targets': [target], 'workflow_files': workflow, 'accepted_steps': 0,
        'old_supplier_proof_commands': 0, 'P2_6_complete': False}
    verifier_blob = encode(verifier)
    blobs[str(TOOL_REL / 'SHAPE_REPAIR_VERIFIER.json')] = verifier_blob
    package_manifest = {
        'schema': 'cell05_shape_repair_source_package_v1',
        'target_count': 1, 'planned_new_steps': 3, 'accepted_steps': 0,
        'repair_source_ready': True, 'P2_6_complete': False,
        'members': [{'member': name, **pin(data)} for name, data in sorted(blobs.items())]}
    package_manifest_blob = encode(package_manifest)
    blobs['PACKAGE_CONTENTS.json'] = package_manifest_blob
    need(len(blobs) == 21 and not any(name.endswith('.olean') for name in blobs),
         'Source package member boundary differs')
    release = ROOT / 'release-v1'
    release.mkdir(exist_ok=False)
    for name, data in blobs.items():
        put(release / name, data)
    archive = ROOT / 'cell05-shape-repair-source-v1.tar.xz'
    with archive.open('xb') as raw:
        with tarfile.open(fileobj=raw, mode='w:xz', preset=6) as tar:
            for name, data in sorted(blobs.items()):
                info = tarfile.TarInfo(name)
                info.size, info.mtime, info.mode = len(data), 0, 0o644
                tar.addfile(info, io.BytesIO(data))
    with tarfile.open(archive, 'r:xz') as tar:
        members = tar.getmembers()
        need(len(members) == len(blobs) and {m.name for m in members} == set(blobs),
             'Archive member set differs after write')
        for member in members:
            need(member.isfile() and tar.extractfile(member).read() == blobs[member.name],
                 'Archive is not the exact regular-file source package')
    report = {
        'schema': 'cell05_shape_repair_source_release_v1',
        'status': 'FROZEN_SOURCE_ONLY_NOT_RUN', 'archive': pin(archive.read_bytes()),
        'regular_members': len(blobs), 'total_uncompressed_bytes': sum(map(len, blobs.values())),
        'source': pin(source), 'audit': pin(audit), 'verifier': pin(verifier_blob),
        'package_manifest': pin(package_manifest_blob), 'framework_files_unchanged': 16,
        'normal_failure_used_as_reproduction': True, 'old_tests_reexecuted': 0,
        'Lean_commands_executed': 0, 'accepted_steps': 0, 'P2_6_complete': False}
    put(ROOT / 'SOURCE_RELEASE.json', encode(report))
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
