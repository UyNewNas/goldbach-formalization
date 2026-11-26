#!/usr/bin/env python3
"""Build the locally authored, source-only Cell05 join preflight deployment."""
from pathlib import Path, PurePosixPath
import hashlib
import io
import json
import os
import stat
import tarfile


HERE = Path(__file__).absolute().parent
REPO = HERE.parents[2]
TOOL_REL = Path('tools/p26/cell05-connections14-run-20261126')
SOURCE = REPO / TOOL_REL
STAGE = '/workspace/p26-cell05-connections14-stage-557a12f3bcd7'
PROVIDER = '/workspace/p26-cell05-connections14-provider-557a12f3bcd7'
JOIN_SHA = '4f4e4dd395b293375c020d656f3d60d19fcd0b862bbecd48597b6e51457520e8'
BASE_FILES = (
    'fields_only_join.py', 'evidence_io.py', 'portable_receipts.py',
    'supplier_capsule.py', 'supplier_join.py', 'runtime_compat.py',
    'runtime_probe.py', 'baseline_checks.py', 'receipt_support.py',
    'SUPPLIER_PLAN.json', 'SUPPLIER_REGISTRY.json', 'CONNECTION_TARGETS.json',
    'RUNTIME_COMPATIBILITY_PINS.json', 'CONNECTIONS_SOURCE_MANIFEST.json',
    'INPUT_ASSEMBLY.json', 'READY14_TARGETS.json', 'FIELDS88_SUPPLIERS.json',
)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def exact_file(path):
    for part in [*reversed(path.parents), path]:
        require(not part.is_symlink(), 'Symlink input: ' + str(part))
    require(stat.S_ISREG(path.stat().st_mode), 'Nonregular input: ' + str(path))
    return path.read_bytes()


def publish(path, body):
    if path.exists():
        require(exact_file(path) == body, 'Refusing to replace: ' + str(path))
        return
    with path.open('xb') as handle:
        handle.write(body)
        handle.flush()
        os.fsync(handle.fileno())
    require(exact_file(path) == body, 'Publication readback mismatch')


def main():
    plan = json.loads(exact_file(SOURCE / 'SUPPLIER_PLAN.json'))
    runtime = json.loads(exact_file(SOURCE / 'RUNTIME_COMPATIBILITY_PINS.json'))
    linked = plan['metadata_files'] + runtime['files']
    require(len(plan['metadata_files']) == 10 and len(runtime['files']) == 5,
            'Changed metadata/runtime scope')
    names = sorted([*BASE_FILES, *(row['relative_path'] for row in linked)])
    require(len(names) == len(set(names)) == 32, 'Changed join-only inventory')
    bodies = {}
    for name in names:
        member = PurePosixPath(name)
        require(not member.is_absolute() and '..' not in member.parts
                and str(member) == name, 'Unsafe input member')
        bodies[str(TOOL_REL / name)] = exact_file(SOURCE / name)
    for row in linked:
        require(digest(bodies[str(TOOL_REL / row['relative_path'])]) ==
                {key: row[key] for key in ('bytes', 'sha256')},
                'Original metadata/runtime pin mismatch')
    require(digest(bodies[str(TOOL_REL / 'fields_only_join.py')]) ==
            {'bytes': 14674, 'sha256': JOIN_SHA}, 'Frozen join changed')
    donor = REPO / 'tools/p26/scalable-cell05-connections-run'
    for name in BASE_FILES[1:9]:
        require(exact_file(donor / name) == bodies[str(TOOL_REL / name)],
                'Original helper changed: ' + name)
    manifest = {
        'schema': 'cell05_join_only_deployment_v1',
        'status': 'SOURCE_ONLY_NOT_RUN',
        'stage': STAGE, 'provider': PROVIDER, 'tool_relative_path': str(TOOL_REL),
        'member_count': len(bodies),
        'files': [{'relative_path': name, **digest(body)}
                  for name, body in sorted(bodies.items())],
        'new_Lean_commands': 0, 'new_Lean_acceptances': 0,
        'target_sources_included': 0, 'target_audits_included': 0,
        'historical_receipt_bodies_copied': 0,
        'supplier_object_bodies_copied': 0,
        'runtime_snapshot_bodies_copied': 0,
        'later_runner_must_reuse_existing_join_and_runtime_guard': True,
    }
    manifest_body = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode='w:xz', format=tarfile.PAX_FORMAT) as archive:
        for name, body in sorted(bodies.items()):
            entry = tarfile.TarInfo(name)
            entry.size = len(body)
            entry.mode = 0o644
            entry.uid = entry.gid = entry.mtime = 0
            entry.uname = entry.gname = ''
            archive.addfile(entry, io.BytesIO(body))
    archive_body = output.getvalue()
    with tarfile.open(fileobj=io.BytesIO(archive_body), mode='r:xz') as archive:
        members = archive.getmembers()
        require(len(members) == len(bodies) and all(x.isfile() for x in members),
                'Archive member type/count mismatch')
        recovered = {x.name: archive.extractfile(x).read() for x in members}
    require(recovered == bodies, 'Archive byte readback mismatch')
    for name, original in bodies.items():
        require(exact_file(REPO / name) == original, 'Source changed during packaging')
    publish(HERE / 'MANIFEST.json', manifest_body)
    publish(HERE / 'cell05-join-only-v1.tar.xz', archive_body)
    report = {
        'schema': 'cell05_join_only_package_readback_v1',
        'status': 'PASS_SOURCE_PACKAGE_READBACK_NOT_RUN',
        'member_count': len(bodies), 'uncompressed_payload_bytes': sum(map(len, bodies.values())),
        'manifest': {'file': 'MANIFEST.json', **digest(manifest_body)},
        'archive': {'file': 'cell05-join-only-v1.tar.xz', **digest(archive_body)},
        'all_original_sources_unchanged': True,
        'all_members_regular_unique_exact': True,
        'all_member_bytes_read_back': True,
        'new_Lean_commands': 0, 'new_Lean_acceptances': 0,
    }
    publish(HERE / 'PACKAGE_READBACK.json',
            (json.dumps(report, indent=2, sort_keys=True) + '\n').encode())
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
