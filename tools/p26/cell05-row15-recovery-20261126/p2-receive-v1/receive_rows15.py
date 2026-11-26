#!/usr/bin/env python3
"""Receive exact existing Cell05 capsule bytes in one new P2 directory; no extraction."""
from pathlib import Path, PurePosixPath
import base64
import hashlib
import json
import os
import stat
import sys

sys.dont_write_bytecode = True
ROOT = Path('/workspace/p26-continuation-557a12f3bcd7/cell05-rows15-private-receive-v1')
CONTROL = ROOT / 'control'
PARTS = ROOT / 'parts'
ARCHIVE = ROOT / 'rows15-provider-v1.tar.xz'
SOURCE_NAMES = {'receive_rows15.py', 'evidence_io.py', 'RECEIVE_MANIFEST.json', 'ORIGINAL_REPORT.json'}
CAPSULE_PIN = {'bytes': 2397884, 'sha256': 'b41f83e3ec17764d06cfbd6b095c7cc499594de0c5060f78327fa0ffd351dfdd'}

from evidence_io import archive_bytes, canonical, fp, member_name, pin, require


def encoded_json(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def load_controls():
    require(sys.flags.optimize == 0, 'Run without Python optimization')
    require(canonical(Path(__file__), True) == CONTROL / 'receive_rows15.py', 'Unexpected receiver location')
    source_path = CONTROL / 'SOURCE_MANIFEST.json'
    source = json.loads(canonical(source_path, True).read_bytes())
    require(source['schema'] == 'cell05_rows15_receive_source_v1' and source['remote_root'] == str(ROOT),
            'Wrong source control scope')
    rows = {row['relative_path']: row for row in source['files']}
    require(len(rows) == len(source['files']) == 4 and set(rows) == SOURCE_NAMES, 'Wrong control member set')
    frozen = {str(source_path): fp(source_path)}
    for name, expected in rows.items():
        actual = fp(CONTROL / name)
        require({key: actual[key] for key in ('bytes', 'sha256')} ==
                {key: expected[key] for key in ('bytes', 'sha256')}, 'Control bytes changed: ' + name)
        frozen[actual['path']] = actual
    request = json.loads((CONTROL / 'RECEIVE_MANIFEST.json').read_bytes())
    require(request['schema'] == 'cell05_rows15_receive_request_v1' and request['remote_root'] == str(ROOT)
            and request['archive'] == CAPSULE_PIN, 'Wrong fixed capsule request')
    require(request['chunk_bytes_max'] == 75000 and len(request['chunks']) == 32, 'Wrong transfer partition')
    offset = 0
    for index, row in enumerate(request['chunks']):
        require(row['index'] == index and row['offset'] == offset and
                row['bytes'] == min(75000, CAPSULE_PIN['bytes'] - offset), 'Chunk layout differs')
        offset += row['bytes']
    require(offset == CAPSULE_PIN['bytes'], 'Chunk layout does not cover the capsule')
    require(pin((CONTROL / 'ORIGINAL_REPORT.json').read_bytes()) == request['original_report'],
            'Original report pin differs')
    return request, frozen


def unchanged(frozen):
    require({name: fp(Path(name)) for name in frozen} == frozen, 'Receiver control bytes changed')


def namespace(request):
    allowed = {'control/' + name for name in SOURCE_NAMES | {'SOURCE_MANIFEST.json'}}
    allowed |= {'parts/part-%03d' % row['index'] for row in request['chunks']}
    allowed |= {'rows15-provider-v1.tar.xz', 'RECEIVED.json', 'MEMBER_PINS.json'}
    allowed |= {name + '.pending' for name in allowed if not name.startswith('control/')}
    directories = {ROOT, CONTROL, PARTS}
    for path in ROOT.rglob('*'):
        canonical(path, True)
        mode = path.lstat().st_mode
        if stat.S_ISDIR(mode):
            require(path in directories, 'Unknown receiver directory')
        else:
            require(stat.S_ISREG(mode) and path.relative_to(ROOT).as_posix() in allowed,
                    'Unknown receiver file or inode type')


def install_exact(path, body):
    canonical(path)
    require(path.is_relative_to(ROOT) and not path.is_relative_to(CONTROL), 'Write outside new data root')
    expected = pin(body)
    if path.exists():
        require({key: fp(path)[key] for key in ('bytes', 'sha256')} == expected,
                'Refuse conflicting existing receiver file')
        return 'identical_existing'
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    canonical(path.parent, True)
    pending = canonical(path.with_name(path.name + '.pending'))
    if pending.exists():
        require({key: fp(pending)[key] for key in ('bytes', 'sha256')} == expected,
                'Mismatched partial requires inspection; no overwrite or deletion')
    else:
        available = os.statvfs(ROOT).f_bavail * os.statvfs(ROOT).f_frsize
        require(available >= len(body) + 262144, 'Insufficient free space before receiver write')
        descriptor = os.open(pending, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600)
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(body)
            stream.flush()
            os.fsync(stream.fileno())
        require({key: fp(pending)[key] for key in ('bytes', 'sha256')} == expected, 'Pending file readback differs')
    os.link(pending, path, follow_symlinks=False)
    require({key: fp(path)[key] for key in ('bytes', 'sha256')} == expected, 'Installed bytes differ')
    pending.unlink()  # Only this task's fully verified temporary hardlink is removed.
    return 'created'


def verify_capsule(path, request):
    bodies = archive_bytes(path, CAPSULE_PIN)  # Reads regular members into memory; never extracts.
    require(len(bodies) == 267 and 'CAPSULE_MANIFEST.json' in bodies, 'Wrong regular archive member count')
    require(pin(bodies['CAPSULE_MANIFEST.json']) == request['capsule_manifest'], 'Capsule manifest bytes differ')
    manifest = json.loads(bodies['CAPSULE_MANIFEST.json'])
    require(manifest['schema'] == 'cell05_rows15_relocatable_supplier_capsule_v1', 'Wrong capsule schema')
    members = [{'member': name, **pin(body)} for name, body in sorted(bodies.items())]
    require(manifest['members'] == [row for row in members if row['member'] != 'CAPSULE_MANIFEST.json'],
            'A payload member differs from its original pin')
    require(sum(len(body) for body in bodies.values()) == request['archive_expanded_bytes'], 'Expanded byte total differs')
    for key, expected in request['source_anchors'].items():
        require(manifest[key] == expected, 'Original source anchor differs: ' + key)
    require(set(request['source_anchors']) == {'source_archive', 'source_export_manifest', 'source_run', 'source_success'},
            'Wrong original source anchor set')
    require(pin(bodies['ORIGINAL_EXPORT_MANIFEST.json']) ==
            {key: request['source_anchors']['source_export_manifest'][key] for key in ('bytes', 'sha256')},
            'Original export manifest body differs')
    mappings = manifest['mappings']
    require(len(mappings) == 496 and pin(encoded_json(mappings)) == request['canonical_mappings'],
            'Original 496 path mappings differ from the independently checked local mapping')
    seen, blob_names = set(), set()
    for row in mappings:
        original, resolved = row['original'], row['resolved']
        old_path = PurePosixPath(original['path'])
        require(old_path.is_absolute() and '..' not in old_path.parts and str(old_path) == original['path']
                and original['path'] not in seen, 'Unsafe or duplicate historical path label')
        seen.add(original['path'])
        if resolved['kind'] == 'blob':
            name = resolved['member']
            member_name(name)
            require(name in bodies and pin(bodies[name]) ==
                    {key: original[key] for key in ('bytes', 'sha256')}, 'Mapped blob identity differs')
            blob_names.add(name)
    require(set(bodies) == blob_names | {'CAPSULE_MANIFEST.json', 'ORIGINAL_EXPORT_MANIFEST.json'},
            'Unexpected or missing blob member')
    expected_scope = {'accepted_targets_rechecked': 15, 'accepted_steps_rechecked': 45,
                      'owned_declarations_rechecked': 5147, 'new_object_bodies': 15,
                      'old_supplier_object_bodies': 0, 'fields_object_bodies': 0,
                      'shared_baseline_members': 154, 'original_receipt_bytes_rewritten': False,
                      'Lean_commands': 0, 'Git_commands': 0, 'complete_join_acceptance': False}
    require(all(manifest.get(key) == value for key, value in expected_scope.items()), 'Original capsule scope differs')
    require(pin(path.read_bytes()) == CAPSULE_PIN, 'Capsule changed during member verification')
    return members


def main():
    request, frozen = load_controls()
    namespace(request)
    require(len(sys.argv) >= 2 and sys.argv[1] in ('chunk', 'finalize', 'inspect'), 'Unknown receiver operation')
    if sys.argv[1] == 'chunk':
        require(len(sys.argv) == 4, 'Expected chunk index and base64 body')
        index = int(sys.argv[2])
        require(0 <= index < 32, 'Chunk index is out of scope')
        body = base64.b64decode(sys.argv[3], validate=True)
        expected = request['chunks'][index]
        require(pin(body) == {key: expected[key] for key in ('bytes', 'sha256')}, 'Chunk bytes differ')
        require(not (ROOT / 'RECEIVED.json').exists() or (PARTS / ('part-%03d' % index)).exists(),
                'Missing chunk after successful receipt; inspect instead of recreating')
        action = install_exact(PARTS / ('part-%03d' % index), body)
        unchanged(frozen)
        print(json.dumps({'status': 'EXACT_CHUNK_PRESENT', 'index': index, **pin(body), 'action': action}))
        return
    require(len(sys.argv) == 2, 'Unexpected receiver arguments')
    parts = []
    for row in request['chunks']:
        path = PARTS / ('part-%03d' % row['index'])
        if not path.exists() and sys.argv[1] == 'inspect':
            continue
        actual = fp(path)
        require({key: actual[key] for key in ('bytes', 'sha256')} ==
                {key: row[key] for key in ('bytes', 'sha256')}, 'Stored chunk pin differs')
        parts.append(actual)
    if sys.argv[1] == 'inspect':
        result = {'status': 'READ_ONLY_RECEIVER_INVENTORY', 'chunks_present': len(parts),
                  'archive': fp(ARCHIVE) if ARCHIVE.exists() else None,
                  'receipt': fp(ROOT / 'RECEIVED.json') if (ROOT / 'RECEIVED.json').exists() else None}
        unchanged(frozen)
        print(json.dumps(result, sort_keys=True))
        return
    if (ROOT / 'RECEIVED.json').exists():
        require(ARCHIVE.exists() and (ROOT / 'MEMBER_PINS.json').exists(),
                'Missing successful output; inspect instead of recreating')
    capsule = b''.join(Path(row['path']).read_bytes() for row in parts)
    require(pin(capsule) == CAPSULE_PIN, 'Reassembled whole capsule differs')
    install_exact(ARCHIVE, capsule)
    members = verify_capsule(ARCHIVE, request)
    inventory = {'schema': 'cell05_rows15_received_member_inventory_v1', 'archive': fp(ARCHIVE), 'members': members}
    install_exact(ROOT / 'MEMBER_PINS.json', encoded_json(inventory))
    result = {'schema': 'cell05_rows15_received_capsule_v1', 'status': 'PASS_RECEIVED_CAPSULE_ONLY',
              'archive': fp(ARCHIVE), 'source_controls': frozen, 'chunk_pins': parts,
              'member_inventory': fp(ROOT / 'MEMBER_PINS.json'), 'regular_members': 267,
              'payload_members_checked': 266, 'source_anchors_checked': 4, 'original_mappings_checked': 496,
              'archive_extracted': False, 'provider_installed': False, 'Lean_commands': 0,
              'old_proof_steps_replayed': 0, 'new_Lean_acceptance': 0,
              'original_P1_capsule_removal_performed': False, 'complete_join_acceptance': False}
    unchanged(frozen)
    install_exact(ROOT / 'RECEIVED.json', encoded_json(result))
    unchanged(frozen)
    print(json.dumps({'status': result['status'], 'archive': result['archive'],
                      'receipt': fp(ROOT / 'RECEIVED.json'), 'member_inventory': result['member_inventory'],
                      'Lean_commands': 0, 'new_Lean_acceptance': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
