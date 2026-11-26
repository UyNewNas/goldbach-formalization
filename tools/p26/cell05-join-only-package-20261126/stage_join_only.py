#!/usr/bin/env python3
"""Install only the frozen Cell05 join preflight payload; never run Lean."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import io
import json
import os
import stat
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
STAGE = Path('/workspace/p26-cell05-connections14-stage-557a12f3bcd7')
PROVIDER = Path('/workspace/p26-cell05-connections14-provider-557a12f3bcd7')
TOOL_REL = PurePosixPath('tools/p26/cell05-connections14-run-20261126')
ARCHIVE_PIN = {'bytes': 123736, 'sha256': '9ceac786913f8196d4d5c5cb841790c70d111fdbfa8702c7f95333bf29c079c7'}
MANIFEST_PIN = {'bytes': 7665, 'sha256': 'ab4cf98194b86a0fc359f6e6b386b66084b652285760acde265629167bd425ea'}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def safe_path(path, directory=False):
    require(path.is_absolute() and '..' not in path.parts, 'Noncanonical path: ' + str(path))
    for ancestor in reversed(path.parents):
        try:
            mode = ancestor.lstat().st_mode
        except FileNotFoundError:
            continue
        require(stat.S_ISDIR(mode) and not stat.S_ISLNK(mode),
                'Unsafe ancestor: ' + str(ancestor))
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        return False
    require(not stat.S_ISLNK(mode), 'Symlink path: ' + str(path))
    require(stat.S_ISDIR(mode) if directory else stat.S_ISREG(mode),
            'Unexpected path type: ' + str(path))
    return True


def read_exact(path, expected):
    require(safe_path(path), 'Missing input: ' + str(path))
    body = path.read_bytes()
    require(pin(body) == expected, 'Input pin mismatch: ' + str(path))
    return body


def load_payload(archive_path, manifest_path):
    for path in (archive_path, manifest_path):
        require(not path.is_relative_to(STAGE), 'Package input is inside output stage')
        require(not path.is_relative_to(PROVIDER), 'Package input is inside provider')
    manifest_body = read_exact(manifest_path, MANIFEST_PIN)
    archive_body = read_exact(archive_path, ARCHIVE_PIN)
    manifest = json.loads(manifest_body)
    require(manifest['schema'] == 'cell05_join_only_deployment_v1'
            and manifest['stage'] == str(STAGE)
            and manifest['provider'] == str(PROVIDER)
            and manifest['tool_relative_path'] == str(TOOL_REL)
            and manifest['member_count'] == 32, 'Unexpected deployment contract')
    expected = {}
    for row in manifest['files']:
        name = row['relative_path']
        member = PurePosixPath(name)
        require(str(member) == name and not member.is_absolute()
                and '..' not in member.parts and member.is_relative_to(TOOL_REL)
                and member != TOOL_REL and name not in expected, 'Unsafe/duplicate member')
        expected[name] = {key: row[key] for key in ('bytes', 'sha256')}
    require(len(expected) == 32, 'Unexpected payload inventory')
    bodies = {}
    with tarfile.open(fileobj=io.BytesIO(archive_body), mode='r:xz') as archive:
        for member in archive.getmembers():
            require(member.isfile() and member.name in expected and member.name not in bodies,
                    'Unexpected tar member: ' + member.name)
            require(member.size == expected[member.name]['bytes'], 'Tar member size mismatch')
            body = archive.extractfile(member).read()
            require(pin(body) == expected[member.name], 'Tar member hash mismatch')
            bodies[member.name] = body
    require(set(bodies) == set(expected), 'Missing payload member')
    require(read_exact(manifest_path, MANIFEST_PIN) == manifest_body
            and read_exact(archive_path, ARCHIVE_PIN) == archive_body,
            'Package changed during preflight')
    return bodies


def create_directories(path):
    for directory in [*reversed(path.parents), path]:
        if safe_path(directory, directory=True):
            continue
        try:
            directory.mkdir()
        except FileExistsError:
            pass
        require(safe_path(directory, directory=True), 'Cannot create safe directory')


def install_payload(bodies):
    # Inspect every existing target before the first mutation. Other final-runner
    # files are allowed and are not touched by this partial, immutable payload.
    safe_path(STAGE, directory=True)
    for name, body in bodies.items():
        destination = STAGE / name
        if safe_path(destination):
            require(destination.read_bytes() == body, 'Refusing to overwrite: ' + str(destination))
    installed = reused = 0
    for name, body in sorted(bodies.items()):
        destination = STAGE / name
        if safe_path(destination):
            require(destination.read_bytes() == body, 'Existing payload changed')
            reused += 1
            continue
        create_directories(destination.parent)
        descriptor, temporary_name = tempfile.mkstemp(prefix='.join-only-', dir=destination.parent)
        temporary = Path(temporary_name)
        try:
            with os.fdopen(descriptor, 'wb') as output:
                output.write(body)
                output.flush()
                os.fsync(output.fileno())
                os.fchmod(output.fileno(), 0o644)
            require(temporary.read_bytes() == body, 'Temporary payload readback mismatch')
            safe_path(destination.parent, directory=True)
            try:
                os.link(temporary, destination)
                installed += 1
            except FileExistsError:
                require(safe_path(destination) and destination.read_bytes() == body,
                        'Concurrent destination differs; refusing overwrite')
                reused += 1
        finally:
            temporary.unlink()
    for name, body in bodies.items():
        destination = STAGE / name
        require(safe_path(destination) and destination.read_bytes() == body,
                'Final payload readback mismatch')
    return installed, reused


def main():
    require(sys.flags.optimize == 0, 'Run without Python optimization')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--install', action='store_true')
    args = parser.parse_args()
    archive_path, manifest_path = args.archive.absolute(), args.manifest.absolute()
    bodies = load_payload(archive_path, manifest_path)
    installed, reused = install_payload(bodies) if args.install else (0, 0)
    read_exact(archive_path, ARCHIVE_PIN)
    read_exact(manifest_path, MANIFEST_PIN)
    print(json.dumps({'status': 'JOIN_ONLY_STAGED_NOT_RUN' if args.install else 'JOIN_ONLY_PACKAGE_CHECKED_NOT_RUN',
                      'stage': str(STAGE), 'provider': str(PROVIDER), 'members': len(bodies),
                      'installed': installed, 'reused_identical': reused,
                      'new_Lean_commands': 0, 'new_Lean_acceptances': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
