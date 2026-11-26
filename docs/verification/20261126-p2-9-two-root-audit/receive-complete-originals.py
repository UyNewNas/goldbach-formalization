#!/usr/bin/env python3
"""Reassemble original archive, verify every raw member and join already-held lineage."""
import base64
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile

BASE = Path('/dev/shm/p29-two-root-7981839-reception')
CONTROL = Path('/workspace/scratch/005887317b49/p29-atlas-1126/two-root-complete-evidence-pack-controls.json')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pretty(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def check(value, message):
    if not value:
        raise ValueError(message)


def main():
    metadata = json.loads((BASE / 'TRANSPORT_META.json').read_bytes())
    slices = []
    offset = 0
    for part in metadata['parts']:
        check(part['offset'] == offset, 'part gap or overlap')
        raw = (BASE / ('part-%03d.raw' % part['index'])).read_bytes()
        check(len(raw) == part['bytes'] and sha(raw) == part['sha256'], 'part identity mismatch')
        slices.append(raw)
        offset += len(raw)
    original = b''.join(slices)
    check(offset == metadata['archive_bytes'] and sha(original) == metadata['archive_sha256'],
          'whole original archive identity mismatch')
    (BASE / 'original-complete.tar.xz').write_bytes(original)
    members = {}
    with tarfile.open(fileobj=io.BytesIO(original), mode='r:xz') as tf:
        for item in tf.getmembers():
            p = PurePosixPath(item.name)
            check(item.isfile() and not p.is_absolute() and '..' not in p.parts and item.name not in members,
                  'unsafe or duplicate original archive member')
            raw = tf.extractfile(item).read()
            check(len(raw) == item.size, 'tar member size mismatch')
            members[item.name] = raw
    check(len(members) == metadata['member_count'], 'member count mismatch')
    original_manifest_raw = members['manifest.json']
    check(sha(original_manifest_raw) == metadata['manifest_sha256'], 'manifest identity mismatch')
    manifest = json.loads(original_manifest_raw)
    check(set(members) == set(manifest['files']) | {'manifest.json'}, 'manifest coverage mismatch')
    for name, pin in manifest['files'].items():
        check(len(members[name]) == pin['bytes'] and sha(members[name]) == pin['sha256'],
              'original member identity mismatch: ' + name)
    snapshot = members['external/EXTERNAL_SNAPSHOT.json']
    check(len(snapshot) == 20904189 and sha(snapshot) ==
          'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27',
          'full original external snapshot mismatch')
    control_specs = json.loads(CONTROL.read_bytes())
    for name, spec in control_specs.items():
        check(name not in members, 'control member collision')
        raw = base64.b64decode(spec['base64'], validate=True)
        check(len(raw) == spec['bytes'] and sha(raw) == spec['sha256'], 'original local control changed')
        members[name] = raw
    check(sha(members['lineage/SELECTED_ORIGINAL_NORMAL_RECORDS.json']) ==
          manifest['original_normal_records_sha256'], 'previous normal lineage mismatch')
    complete_manifest = {
        'schema': 'p29_two_root_complete_originals_and_preexisting_control_join_v1',
        'original_audit_job': metadata.get('original_audit_job', '7981839ec960464d913d5ee2b3a18175'),
        'original_archive': {'bytes': len(original), 'sha256': sha(original),
                             'manifest_sha256': sha(original_manifest_raw), 'member_count': metadata['member_count']},
        'roots': manifest['roots'],
        'original_manifest_member': 'manifest.json',
        'previous_normal_records_member': 'lineage/SELECTED_ORIGINAL_NORMAL_RECORDS.json',
        'external_snapshot_member': 'external/EXTERNAL_SNAPSHOT.json',
        'remote_export_lean_invocations': 0,
        'local_lean_invocations': 0,
        'root_acceptance_pending': True,
        'scope': 'Lossless reception and local join only; full original 6+12 owned evidence retained, no full-facet qualification claim.',
        'files': {name: {'bytes': len(raw), 'sha256': sha(raw)} for name, raw in members.items()},
    }
    members['COMPLETE_MANIFEST.json'] = pretty(complete_manifest)
    output = BASE / 'complete'
    check(not output.exists(), 'complete reception output already exists; do not repeat')
    output.mkdir()
    for name, raw in members.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(raw)
    archive = BASE / 'complete-with-original-lineage.tar.xz'
    with tarfile.open(archive, mode='w:xz', preset=6, format=tarfile.PAX_FORMAT) as tf:
        for name, raw in members.items():
            info = tarfile.TarInfo(name)
            info.size = len(raw)
            info.mode = 0o644
            info.mtime = 0
            tf.addfile(info, io.BytesIO(raw))
    archive_bytes = archive.read_bytes()
    result = {'schema': 'p29_two_root_complete_raw_reception_v1',
              'status': 'ALL_TRANSPORT_AND_MEMBER_HASHES_PASSED_ROOT_PARSER_REVIEW_PENDING',
              'original_archive': complete_manifest['original_archive'],
              'complete_archive_path': str(archive), 'complete_archive_bytes': len(archive_bytes),
              'complete_archive_sha256': sha(archive_bytes), 'complete_member_count': len(members),
              'complete_manifest_sha256': sha(members['COMPLETE_MANIFEST.json']),
              'complete_directory': str(output),
              'snapshot_path': str(output / 'external/EXTERNAL_SNAPSHOT.json'),
              'snapshot_sha256': sha(snapshot), 'snapshot_bytes': len(snapshot),
              'root_credit_added_by_reception': 0}
    (BASE / 'COMPLETE_RECEPTION.json').write_bytes(pretty(result))
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
