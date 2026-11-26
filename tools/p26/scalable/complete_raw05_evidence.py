#!/usr/bin/env python3
"""Close raw05's historical evidence boundary without any new Lean execution."""
from pathlib import Path
import hashlib
import io
import json
import shutil
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
ARCHIVE = Path('/dev/shm/p26-59264dd64286/raw05-complete-recovered-evidence.tar.xz')
DESTINATION = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05/raw05-supplier-evidence.tar.xz'
MODULE = 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05'
OBJECT_MEMBER = 'objects/' + MODULE.replace('.', '/') + '.olean'
SOURCE_MEMBER = 'project/' + MODULE.replace('.', '/') + '.lean'


def fp(path):
    data = Path(path).read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    payload = ARCHIVE.read_bytes()
    assert len(payload) == 184036
    assert hashlib.sha256(payload).hexdigest() == 'f4feab458fec447cb09e4d375102e2ecd3218d88d8336302eafc860d112a60c6'
    with tarfile.open(fileobj=io.BytesIO(payload), mode='r:xz') as tar:
        def blob(member): return tar.extractfile(member).read()
        def read(member): return json.loads(blob(member))
        manifest = read('RECOVERED_EXPORT_MANIFEST.json')
        assert len(manifest['members']) == 74
        for row in manifest['members']:
            data = blob(row['member'])
            assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
        prefix = 'previous-p1-evidence/'
        strict_member = prefix + 'runs/attempt-00000/RESULT.json'
        normal_member = prefix + 'normal/' + MODULE + '/NORMAL_PASS.json'
        validation_member = prefix + 'audits/4a6c7c6a709e4eabfdf5/lane-0/VALIDATION_RESULTS.json'
        lane = validation_member.rsplit('/', 1)[0] + '/'
        strict, normal, validation = read(strict_member), read(normal_member), read(validation_member)
        expected = 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
        assert strict['status'] == validation['status'] == expected
        assert strict['accepted_owners'] == [MODULE]
        assert validation['source_plus_five_outputs'][MODULE] == normal['source_plus_five_outputs']
        assert read(lane + 'BEFORE_KERNEL.json')[MODULE] == normal['source_plus_five_outputs']
        for command in [validation['kernel_commands'][MODULE], validation['audit_command']]:
            assert command['exit_code'] == 0
            assert hashlib.sha256(blob(lane + command['log'])).hexdigest() == command['log_sha256']
        owned = read(lane + 'OWNED_EXPORTS.json')
        assert len(owned) == validation['total_owned_exports'] == 1
        assert owned[0]['module'] == MODULE and owned[0]['axioms'] == []
        assert owned[0]['name'] == 'ImbalancedChen.P2OriginalSaving19Archive.geometryPacked05'
        assert blob(SOURCE_MEMBER) == (REPO / (MODULE.replace('.', '/') + '.lean')).read_bytes()
        local_input = Path('/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-05-cell.witness.json')
        assert blob('original-input/' + local_input.name) == local_input.read_bytes()
        raw_objects = {SOURCE_MEMBER: blob(SOURCE_MEMBER), OBJECT_MEMBER: blob(OBJECT_MEMBER)}
        receipt_pins = {name: {'member': name, 'bytes': len(blob(name)), 'sha256': hashlib.sha256(blob(name)).hexdigest()}
                        for name in [strict_member, normal_member, validation_member,
                                     lane + 'BEFORE_KERNEL.json', lane + 'OWNED_EXPORTS.json',
                                     lane + 'P2OriginalSaving19ArchiveGeometryData05-kernel-command.json',
                                     lane + 'P2OriginalSaving19ArchiveGeometryData05-kernel.log',
                                     lane + 'all-owned-types-axioms-command.json', lane + 'all-owned-types-axioms.log']}
    DESTINATION.parent.mkdir(parents=True, exist_ok=True)
    if DESTINATION.exists():
        assert DESTINATION.read_bytes() == payload
    else:
        DESTINATION.write_bytes(payload)
    supplier_path = HERE / 'SUPPLIER_PINS.json'
    verifier_path = HERE / 'ScalableGeometry_VERIFIER.json'
    old_supplier, old_verifier = fp(supplier_path), fp(verifier_path)
    registry = json.loads(supplier_path.read_text())
    row = next(x for x in registry['suppliers'] if x['module'] == MODULE)
    assert not row['independent_kernel_receipt_pinned'], 'Completion already applied; preserve its files.'
    for role, member in [('source', SOURCE_MEMBER), ('object', OBJECT_MEMBER)]:
        assert len(raw_objects[member]) == row[role]['bytes']
        assert hashlib.sha256(raw_objects[member]).hexdigest() == row[role]['sha256']
    history = HERE / 'history/v1'
    history.mkdir(parents=True, exist_ok=True)
    for path in [supplier_path, verifier_path]:
        destination = history / path.name
        if destination.exists(): assert destination.read_bytes() == path.read_bytes()
        else: shutil.copyfile(path, destination)
    row['previous_context_basis'] = row['evidence_basis']
    row['evidence_basis'] = {'kind': 'recovered_P1_normal_kernel_full_owned_same_object',
                             'archive': fp(DESTINATION), 'receipt_members': receipt_pins,
                             'source_commit': strict['source_commit'],
                             'owned_declaration_count': 1, 'axioms': [],
                             'raw_input_matches_exact_original': True,
                             'new_Lean_executions': 0}
    row['independent_kernel_receipt_pinned'] = True
    registry['schema'] = 'scalable_geometry_supplier_pins_v2_raw05_receipts_recovered'
    registry['raw_owner_kernel_receipts_pending'] = [x['module'] for x in registry['suppliers'] if not x['independent_kernel_receipt_pinned']]
    supplier_path.write_text(json.dumps(registry, indent=2) + '\n')
    verifier = json.loads(verifier_path.read_text())
    verifier['schema'] = 'scalable_geometry_frozen_verifier_v2_raw05_receipts_recovered'
    verifier['supplier_manifest'] = fp(supplier_path)
    verifier_path.write_text(json.dumps(verifier, indent=2) + '\n')
    result = {'status': 'RECOVERED_EXISTING_NORMAL_KERNEL_FULL_OWNED_SAME_BYTES',
              'module': MODULE, 'source': row['source'], 'object': row['object'],
              'evidence_archive': fp(DESTINATION), 'listed_members_verified': 74,
              'old_supplier_manifest': old_supplier, 'new_supplier_manifest': fp(supplier_path),
              'old_verifier_manifest': old_verifier, 'new_verifier_manifest': fp(verifier_path),
              'new_Lean_executions': 0, 'new_proof_source_bytes_changed': False,
              'cell05_supplier_kernel_closed': True, 'cell12_supplier_kernel_closed': False}
    (HERE / 'RAW05_EVIDENCE_COMPLETION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
