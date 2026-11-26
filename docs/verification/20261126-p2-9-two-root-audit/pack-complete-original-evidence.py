#!/usr/bin/env python3
"""Archive only the original successful 798 audit evidence; zero Lean invocations."""
import base64
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import tarfile
import time

ROOT = Path('/workspace/p2-saving16-20261125')
OUT = Path('/workspace/p29-polyhedral-affine-7981839-archive')
TOOLS = Path('/workspace/p2-9-20261125/verification/part2')
SNAPSHOT = Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
SNAPSHOT_SHA = 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
TOOL_PINS = {
    'run_winner9_private_audit.py': '571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5',
    'run_winner9_private_checks.py': '164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac',
    'inspect_winner9_owner_native.py': '9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d',
    'winner9_private_audit_template.lean': '2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b',
    'winner9_external_snapshot.py': 'a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf',
}
TARGETS = {
    'ImbalancedChen.ActualPrimePolyhedralTestFunctions': {
        'source_git_blob': '660ce6ca1a0da5065d32bb028509faf629d685fa',
        'source_sha256': '7281ad47406ad7eb48c5f50c24fa037880778aeb59d79a32f25855ab0dd17ad6',
        'object_sha256': 'a1ea6cd7acd3317a1e72b9af50c054906b8205d0db2bd78234922745800281da',
        'record_sha256': '8a420f88c97482a5949f51821e748a8fc219f4c135dc0dff91c530fd86fd9e95',
        'closure_signature': '144bbc68377dd301ff84bdd6d404b43686fe2653d7a8599703a2b2b89621def4',
        'owned': 6,
    },
    'ImbalancedChen.AffinePrimeWallReserve': {
        'source_git_blob': '68a60733bdb819724149054b9debf4da390c840a',
        'source_sha256': '185e640b506ee01c6df125cb83c06ff39d8f600e37cc4bf355eeecefe2be559b',
        'object_sha256': 'e05ed8e1c69ceadb300c35466c3042675228c420d0508e449b9541ba87f280f4',
        'record_sha256': 'f6978a7a65cc13f45d39ee81e5b9ce70ffc06873d346573ed87c3129a43d0899',
        'closure_signature': '9c662c0a50da62b2649208afdf57dbab944d48348912fca2eeb7f11c1b11c91e',
        'owned': 12,
    },
}
LEAN = '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean'
CHECKER = '/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leanchecker'
MEMBERS = {}
IDENTITIES = {}
READS = {}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def pretty(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def identity(path):
    s = path.stat()
    require(stat.S_ISREG(s.st_mode), 'not a regular file: ' + str(path))
    return {'requested_path': str(path), 'resolved_path': str(path.resolve()),
            'st_dev': s.st_dev, 'st_ino': s.st_ino, 'st_size': s.st_size,
            'st_mtime_ns': s.st_mtime_ns, 'st_ctime_ns': s.st_ctime_ns,
            'st_mode': s.st_mode}


def read_once(path, expected=None, limit=64 * 1024 * 1024):
    path = Path(path)
    key = str(path)
    if key in READS:
        raw = READS[key]
    else:
        before = identity(path)
        require(before['st_size'] <= limit, 'bounded original exceeds limit: ' + key)
        raw = path.read_bytes()
        require(len(raw) == before['st_size'] and identity(path) == before,
                'original changed while reading: ' + key)
        IDENTITIES[key] = {**before, 'sha256': sha(raw)}
        READS[key] = raw
    require(expected is None or sha(raw) == expected, 'original SHA mismatch: ' + key)
    return raw


def add(name, raw, origin=None, kind='original_file'):
    p = PurePosixPath(name)
    require(not p.is_absolute() and '..' not in p.parts and name not in MEMBERS,
            'unsafe or duplicate archive member: ' + name)
    MEMBERS[name] = {'data': raw, 'bytes': len(raw), 'sha256': sha(raw),
                     'origin': origin, 'kind': kind}
    return name


def project_original(relative, expected=None):
    p = Path(relative)
    full = p if p.is_absolute() else ROOT / p
    rel = full.relative_to(ROOT).as_posix()
    name = 'project/' + rel
    if name in MEMBERS:
        require(expected is None or MEMBERS[name]['sha256'] == expected,
                'inconsistent duplicate reference: ' + name)
        return name
    return add(name, read_once(full, expected), str(full))


def main():
    require(not OUT.exists(), 'exclusive archive output already exists; do not rerun')
    require(shutil.disk_usage('/workspace').free >= 96 * 1024 * 1024,
            'insufficient free disk before the archive write')
    registry = ROOT / '.lake/p2-private/records.json'
    registry_bytes = read_once(registry)
    records = json.loads(registry_bytes)
    roots = {}
    for module, pin in TARGETS.items():
        row = records[module]
        require(sha(canonical(row)) == pin['record_sha256'], 'canonical normal row changed: ' + module)
        require(row['module'] == module and row['exit_code'] == 0 and row['new_strict_compile'] is True,
                'normal record identity/status mismatch')
        require(row['source_sha256'] == pin['source_sha256'] and row['object_sha256'] == pin['object_sha256']
                and row['closure_signature'] == pin['closure_signature'], 'normal source/object/closure mismatch')
        source_member = project_original(row['source'], pin['source_sha256'])
        object_member = project_original(row['object'], pin['object_sha256'])
        normal_log = project_original(row['log'], sha(b''))
        record_member = add('provenance/' + module + '/canonical-normal-record.json', canonical(row),
                            str(registry) + '#' + module, 'canonical_selected_original_row')
        latest_path = ROOT / '.lake/p2-private/audit' / module / 'latest.json'
        latest_raw = read_once(latest_path)
        receipt = json.loads(latest_raw)
        require(receipt['schema'] == 1 and receipt['module'] == module and receipt['accepted'] is True,
                'original audit receipt not accepted')
        require(receipt['source_sha256'] == pin['source_sha256'] and receipt['object_sha256'] == pin['object_sha256']
                and receipt['compile_closure_signature'] == pin['closure_signature'], 'audit/normal binding mismatch')
        require(sha(canonical(receipt['input_snapshot'])) == receipt['input_sha256'], 'input snapshot digest mismatch')
        snap = receipt['input_snapshot']
        require(snap['driver_sha256'] == TOOL_PINS['run_winner9_private_audit.py']
                and snap['template_sha256'] == TOOL_PINS['winner9_private_audit_template.lean'], 'audit tool pin mismatch')
        external = snap['external_snapshot']
        require(external.get('snapshot_sha256') == SNAPSHOT_SHA, 'external snapshot receipt SHA mismatch')
        replay, audit = receipt['replay'], receipt['audit']
        require(replay['command'] == [CHECKER, '--verbose', module] and replay['exit_code'] == 0
                and replay['inputs_unchanged'] is True, 'named replay process mismatch')
        require(audit['command'] == [LEAN, '-t0', '-j1', '-M11264', '-DwarningAsError=true',
                '-DmaxRecDepth=50000', '-DmaxHeartbeats=40000000', audit['source']]
                and audit['exit_code'] == 0 and audit['inputs_unchanged'] is True
                and audit['declaration_count'] == pin['owned'], 'full-owned process mismatch')
        latest_member = project_original(latest_path, sha(latest_raw))
        attempt_dir = (ROOT / audit['source']).parent
        require(attempt_dir.parent == latest_path.parent, 'unexpected original attempt directory')
        attempt_receipt = project_original(attempt_dir / 'receipt.json', sha(latest_raw))
        artifact_members = {}
        require(set(receipt['artifacts']) == {replay['log'], audit['log'], audit['source'],
                str((attempt_dir / 'declarations.json').relative_to(ROOT)),
                str((attempt_dir / 'types.txt').relative_to(ROOT))}, 'unexpected artifact set')
        for path, digest in receipt['artifacts'].items():
            artifact_members[path] = project_original(path, digest)
        require(receipt['artifacts'][replay['log']] == replay['log_sha256']
                and receipt['artifacts'][audit['log']] == audit['log_sha256']
                and receipt['artifacts'][audit['source']] == audit['source_sha256'], 'process artifact mismatch')
        declarations = json.loads(READS[str(attempt_dir / 'declarations.json')])
        require(declarations['declaration_count'] == pin['owned']
                and len(declarations['declarations']) == pin['owned'], 'owned inventory count mismatch')
        roots[module] = {**pin, 'source_member': source_member, 'object_member': object_member,
                         'normal_log_member': normal_log, 'canonical_normal_record_member': record_member,
                         'latest_receipt_member': latest_member, 'attempt_receipt_member': attempt_receipt,
                         'receipt_sha256': sha(latest_raw), 'input_sha256': receipt['input_sha256'],
                         'artifact_members': artifact_members,
                         'normal_replayed_by_export': False, 'kernel_or_owned_replayed_by_export': False}
    summary_path = ROOT / '.lake/p2-private/audit/p29-polyhedral-affine-missing-owned-20261126.json'
    summary_raw = read_once(summary_path)
    summary = json.loads(summary_raw)
    require(summary['all_accepted'] is True and summary['accepted'] == 2 and summary['requested'] == 2
            and set(summary['modules']) == set(TARGETS), 'original summary mismatch')
    for module, pin in TARGETS.items():
        require(summary['modules'][module] == {'accepted': True, 'declarations': pin['owned'], 'reused': False},
                'original per-root summary mismatch')
    project_original(summary_path, sha(summary_raw))
    for name, digest in TOOL_PINS.items():
        add('original-tools/' + name, read_once(TOOLS / name, digest), str(TOOLS / name))
    snapshot_raw = read_once(SNAPSHOT, SNAPSHOT_SHA)
    require(len(snapshot_raw) == 20904189, 'external snapshot byte count mismatch')
    add('external/EXTERNAL_SNAPSHOT.json', snapshot_raw, str(SNAPSHOT))
    for path, before in IDENTITIES.items():
        require(identity(Path(path)) == {k: v for k, v in before.items() if k != 'sha256'},
                'input identity changed before archiving: ' + path)
    add('provenance/TRANSFER_INPUT_IDENTITIES.json', pretty(IDENTITIES), None,
        'new_export_read_stability_receipt_not_new_proof_qualification')
    manifest = {'schema': 'p29_original_two_root_schema1_complete_archive_v1',
        'original_audit_job': '7981839ec960464d913d5ee2b3a18175', 'roots': roots,
        'previously_received_normal_records_file': 'SELECTED_ORIGINAL_NORMAL_RECORDS.json',
        'original_normal_records_sha256': '88f5f492ccae8e0fa9ddee189559bb10d1c3cd1dea589486286a5eb6d2a8f78d',
        'previous_normal_records_archive_git_blob': '76f918e111c03dccb3069b8c75829fda443055be',
        'previously_received_control_files': 'Preserved locally and on Git; joined after reception without uploading and retransferring old evidence.',
        'external_snapshot': {'member': 'external/EXTERNAL_SNAPSHOT.json', 'sha256': SNAPSHOT_SHA, 'bytes': 20904189},
        'export_lean_invocations': 0, 'export_normal_compiles': 0, 'export_audit_replays': 0,
        'root_acceptance_pending': True,
        'scope': 'Two accepted original schema1 audits and existing normal provenance. No new full native-standard facet graph qualification. No 54-object inventory rerun.',
        'files': {name: {k: v for k, v in entry.items() if k != 'data'} for name, entry in MEMBERS.items()}}
    manifest_raw = pretty(manifest)
    add('manifest.json', manifest_raw, None, 'new_complete_archive_manifest')
    OUT.mkdir()
    archive = OUT / 'complete.tar.xz'
    with tarfile.open(archive, mode='w:xz', preset=6, format=tarfile.PAX_FORMAT) as tf:
        for name, entry in MEMBERS.items():
            info = tarfile.TarInfo(name)
            info.size = len(entry['data'])
            info.mode = 0o644
            info.mtime = 0
            tf.addfile(info, io.BytesIO(entry['data']))
    archive_raw = archive.read_bytes()
    part_bytes = 1200000
    parts = [{'index': i, 'offset': off, 'bytes': len(archive_raw[off:off + part_bytes]),
              'sha256': sha(archive_raw[off:off + part_bytes])}
             for i, off in enumerate(range(0, len(archive_raw), part_bytes))]
    metadata = {'schema': 'p29_complete_two_root_archive_transport_v1', 'archive': str(archive),
        'archive_bytes': len(archive_raw), 'archive_sha256': sha(archive_raw),
        'manifest_sha256': sha(manifest_raw), 'member_count': len(MEMBERS),
        'manifest_file_count': len(manifest['files']), 'raw_member_bytes': sum(v['bytes'] for v in MEMBERS.values()),
        'snapshot_bytes': len(snapshot_raw), 'snapshot_sha256': SNAPSHOT_SHA,
        'roots': {m: {'owned': p['owned'], 'receipt_sha256': roots[m]['receipt_sha256']} for m, p in TARGETS.items()},
        'parts': parts, 'part_bytes_limit': part_bytes, 'export_lean_invocations': 0,
        'archive_identity': identity(archive)}
    (OUT / 'TRANSPORT_META.json').write_bytes(pretty(metadata))
    print('P29_TWO_ROOT_ARCHIVE_META ' + json.dumps(metadata, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
