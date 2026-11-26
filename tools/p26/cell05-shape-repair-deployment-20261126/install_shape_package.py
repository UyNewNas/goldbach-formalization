#!/usr/bin/env python3
"""Install one exact local source package, then execute the reviewed one-owner job."""
from pathlib import Path, PurePosixPath
import hashlib
import json
import shutil
import subprocess
import sys
import tarfile

DEPLOY = Path('/workspace/p26-continuation-557a12f3bcd7/cell05-shape-repair-deploy-v1')
PACKAGE = Path('/workspace/p26-continuation-557a12f3bcd7/cell05-shape-repair-package-v1')
STAGE = Path('/workspace/p26-cell05-shape-repair-stage-557a12f3bcd7')
ARCHIVE = {'bytes': 38124, 'sha256': '68ef61eb8583c57176fd2278a2b92e593a07cc9c7ad09a6c66165b83b3b222ac'}
DISPATCH = {'bytes': 6204, 'sha256': 'c42926a24108a7e8ff13478ad2664d973b564b1559939d12a1fb1adf7b624657'}
MANIFEST = {'bytes': 4139, 'sha256': 'd48785ae7184223eb3824a0b91faadabbb07a08cf86f17907007ec37b05b1517'}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    need(sys.flags.optimize == 0, 'Python optimization is not permitted')
    need(Path(__file__).absolute() == DEPLOY / 'install_shape_package.py', 'Wrong installer location')
    need(DEPLOY.resolve(strict=True) == DEPLOY and not DEPLOY.is_symlink(), 'Noncanonical deployment root')
    need(PACKAGE.resolve() == PACKAGE and STAGE.resolve() == STAGE and
         not PACKAGE.exists() and not STAGE.exists(), 'Fresh package/stage paths are required')
    archive = DEPLOY / 'cell05-shape-repair-source-v1.tar.xz'
    dispatch = DEPLOY / 'dispatch_shape.py'
    need(not archive.is_symlink() and pin(archive.read_bytes()) == ARCHIVE, 'Wrong frozen source package')
    need(not dispatch.is_symlink() and pin(dispatch.read_bytes()) == DISPATCH, 'Wrong reviewed dispatcher')
    need(shutil.disk_usage(DEPLOY).free >= 32 * 1024**2, 'Less than 32 MiB free; preserve inputs and stop before proof')
    blobs = {}
    with tarfile.open(archive, 'r:xz') as tar:
        for member in tar:
            relative = PurePosixPath(member.name)
            need(member.isfile() and member.name not in blobs and
                 not relative.is_absolute() and '..' not in relative.parts and
                 str(relative) == member.name and not member.name.endswith('.olean'),
                 'Unsafe, duplicate, or non-source archive member')
            blobs[member.name] = tar.extractfile(member).read()
            need(len(blobs[member.name]) == member.size, 'Short archive member')
    need(len(blobs) == 21 and pin(blobs['PACKAGE_CONTENTS.json']) == MANIFEST, 'Wrong package manifest')
    manifest = json.loads(blobs['PACKAGE_CONTENTS.json'])
    need(manifest['schema'] == 'cell05_shape_repair_source_package_v1' and
         manifest['target_count'] == 1 and manifest['planned_new_steps'] == 3 and
         manifest['accepted_steps'] == 0 and manifest['repair_source_ready'] is True,
         'Wrong source-only proof boundary')
    expected = {row['member']: row for row in manifest['members']}
    need(len(expected) == len(manifest['members']) == 20 and
         set(blobs) == set(expected) | {'PACKAGE_CONTENTS.json'}, 'Wrong exact package member set')
    for name, row in expected.items():
        need(pin(blobs[name]) == {key: row[key] for key in ('bytes', 'sha256')},
             'Frozen member bytes changed: ' + name)
    PACKAGE.mkdir(exist_ok=False)
    for name, data in blobs.items():
        destination = PACKAGE / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        need(destination.resolve() == destination, 'Noncanonical installation destination')
        with destination.open('xb') as stream:
            stream.write(data)
        need(destination.read_bytes() == data, 'Installation readback differs')
    report = {'schema': 'cell05_shape_repair_deployment_v1', 'status': 'PASS_EXACT_LOCAL_SOURCE_PACKAGE_INSTALL',
              'archive': {'path': str(archive), **ARCHIVE}, 'dispatcher': {'path': str(dispatch), **DISPATCH},
              'package': str(PACKAGE), 'stage': str(STAGE), 'regular_members': 21,
              'old_supplier_proof_commands': 0, 'accepted_steps_at_deployment': 0,
              'old_fourteen_target_stage_modified': False, 'P2_6_complete': False}
    with (DEPLOY / 'DEPLOYED.json').open('x') as stream:
        stream.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)
    result = subprocess.run([sys.executable, '-B', str(dispatch), '--emit-archive'])
    raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
