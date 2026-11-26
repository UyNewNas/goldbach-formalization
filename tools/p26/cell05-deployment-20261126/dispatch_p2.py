#!/usr/bin/env python3
"""Deploy exact local-authored inputs and run only the 14 new Cell05 owners."""
from pathlib import Path, PurePosixPath
import hashlib
import io
import json
import os
import subprocess
import sys
import tarfile
import time

sys.dont_write_bytecode = True
if sys.flags.optimize:
    raise RuntimeError('Run with assertions enabled')
BASE = Path('/workspace/p26-continuation-557a12f3bcd7')
UPLOAD = BASE / 'cell05-connections14-upload-v1'
PACKAGE = BASE / 'cell05-connections14-package-v1'
STAGE = Path('/workspace/p26-cell05-connections14-stage-557a12f3bcd7')
PROVIDER = Path('/workspace/p26-cell05-connections14-provider-557a12f3bcd7')
TOOL = Path('tools/p26/cell05-connections14-run-20261126')
PARTS = [{"index":0,"bytes":40000,"sha256":"6a10225eeec251b8a455ad5faa5fe0b6e8160e0e12e02db651a9b1e80dc3d86e"},{"index":1,"bytes":40000,"sha256":"160c09cf7ce61928357d3fbbdb511bba8c80bb379239d493074fce8b597ffe72"},{"index":2,"bytes":40000,"sha256":"adca937ddb8abbb3a2ff18e9f939dd650632b56f862cf3a87089f00fa4a214da"},{"index":3,"bytes":25492,"sha256":"b9e358cd2aa5612b4838698fe5c8b510b0142eab6063bddca31afb7a8db012e8"}]
ARCHIVE_BYTES = 145492
ARCHIVE_SHA = '3334435ea38770c5361d56c52b2595696d2072d55e1e22b0132d81acd03f6188'
PROGRESS = BASE / 'cell05-connections14-dispatch-v1'
PILOT = 'ready14-pilot-v1'
COMPLETE = 'ready14-complete-v1'

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def canonical(path):
    path = Path(path)
    need(path.is_absolute() and path.resolve() == path, 'Noncanonical/symlink path: ' + str(path))
    return path

def create_or_same(path, data):
    canonical(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    canonical(path.parent)
    if path.exists():
        need(path.is_file() and path.read_bytes() == data, 'Refusing different existing file: ' + str(path))
    else:
        with path.open('xb') as stream:
            stream.write(data)

def event(name, value):
    payload = {'phase': name, 'time_utc_epoch': time.time(), **value}
    data = (json.dumps(payload, indent=2) + '\n').encode()
    path = PROGRESS / (name + '.json')
    canonical(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)
    print(json.dumps(payload), flush=True)

def deploy():
    for root in (BASE, UPLOAD, PACKAGE, STAGE, PROVIDER, PROGRESS):
        canonical(root)
    bodies = []
    for part in PARTS:
        path = UPLOAD / ('part-%03d' % part['index'])
        data = canonical(path).read_bytes()
        need(pin(data) == {key: part[key] for key in ('bytes', 'sha256')}, 'Upload part identity differs')
        bodies.append(data)
    raw = b''.join(bodies)
    need(pin(raw) == {'bytes': ARCHIVE_BYTES, 'sha256': ARCHIVE_SHA}, 'Full frozen source archive differs')
    payload = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:xz') as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            need(member.isfile() and not name.is_absolute() and '..' not in name.parts and
                 str(name) == member.name and member.name not in payload, 'Unsafe or duplicate source member')
            data = archive.extractfile(member).read()
            need(len(data) == member.size, 'Short source member')
            payload[member.name] = data
    need(len(payload) == 68 and 'PACKAGE_CONTENTS.json' in payload, 'Wrong frozen package inventory')
    manifest = json.loads(payload['PACKAGE_CONTENTS.json'])
    need(manifest['schema'] == 'cell05_connections14_source_package_v1' and
         manifest['target_count'] == 14 and manifest['planned_new_steps'] == 42 and
         manifest['accepted_steps'] == 0, 'Wrong source-only package scope')
    expected = {row['member']: row for row in manifest['members']}
    need(len(expected) == len(manifest['members']) and set(payload) == set(expected) | {'PACKAGE_CONTENTS.json'},
         'Manifest and source package members differ')
    for name, row in expected.items():
        need(pin(payload[name]) == {key: row[key] for key in ('bytes', 'sha256')}, 'Frozen member bytes differ')
        need(not name.endswith('.olean'), 'Source package must not contain proof objects')
    if PACKAGE.exists():
        for file in PACKAGE.rglob('*'):
            canonical(file)
            if file.is_file():
                name = file.relative_to(PACKAGE).as_posix()
                need(name in payload and file.read_bytes() == payload[name], 'Conflicting prior package body')
    # All source identities are checked before writing the extraction.
    create_or_same(BASE / 'cell05-connections14-source-v1.tar.xz', raw)
    for name, data in payload.items():
        create_or_same(PACKAGE / name, data)
    need(all((PACKAGE / name).read_bytes() == data for name, data in payload.items()), 'Source readback differs')
    event('deployed', {'status': 'EXACT_FROZEN_SOURCE_PACKAGE_INSTALLED', 'archive_sha256': ARCHIVE_SHA,
                      'members': len(payload), 'old_supplier_proof_commands': 0})

def run_phase(name, argv):
    event(name + '-started', {'argv': argv, 'old_supplier_proof_commands': 0})
    subprocess.run(argv, check=True, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    event(name + '-process-finished', {'exit_code': 0, 'proof_credit': 'requires_original_receipt_validation'})

def main():
    deploy()
    entry = PACKAGE / TOOL / 'stage_entry.py'
    common = [sys.executable, '-B', str(entry), '--stage', str(STAGE), '--provider', str(PROVIDER),
              '--rss-gib', '6', '--wall-seconds', '900']
    run_phase('preflight', common + ['--attempt', 'ready14-preflight-v1', '--preflight-only'])
    run_phase('pilot', common + ['--attempt', PILOT, '--max-new-steps', '3'])
    paused = json.loads((STAGE / 'verification' / PILOT / 'STOPPED.json').read_text())
    need(paused['status'] == 'stopped' and paused['reason'] == 'new_step_budget' and
         paused['accepted_steps'] == 3 and paused['accepted_targets'] == 1 and
         paused['newly_executed_steps'] == 3 and paused['reused_steps'] == 0, 'Pilot did not retain exactly three accepted steps')
    event('pilot-accepted-prefix', {'accepted_steps': 3, 'accepted_targets': 1, 'P2_6_complete': False})
    run_phase('remaining', common + ['--attempt', COMPLETE])
    success = json.loads((STAGE / 'verification' / COMPLETE / 'SUCCESS.json').read_text())
    need(success['status'] == 'succeeded' and success['accepted_steps'] == 42 and success['accepted_targets'] == 14 and
         success['newly_executed_steps'] == 39 and success['reused_steps'] == 3 and
         success['frozen_inputs_unchanged'] is True and success['P2_6_complete'] is False,
         'Completion scope or pilot reuse differs')
    exporter = STAGE / TOOL / 'export_connections14.py'
    run_phase('export', [sys.executable, '-B', str(exporter), '--stage', str(STAGE), '--attempt', COMPLETE, '--label', 'v1'])
    report_path = STAGE / 'exports' / ('connections14-' + COMPLETE + '-v1-evidence.tar.xz.json')
    report = json.loads(report_path.read_text())
    need(report['status'] == 'PASS_EXPORT_RECHECK' and report['accepted_steps'] == 42 and
         report['accepted_targets'] == 14 and report['archive_member_recheck_passed'] is True,
         'Full export/readback did not pass')
    event('finished', {'status': 'PASS_CELL05_FOURTEEN_NEW_OWNERS_AND_EXPORT',
                      'accepted_targets': 14, 'accepted_steps': 42, 'old_supplier_proof_commands': 0,
                      'archive': report['archive'], 'automatic_archive_transfer': False,
                      'whole_geometry_decoded': False, 'P2_6_complete': False})

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'status': 'DISPATCH_STOPPED', 'error': type(error).__name__ + ': ' + str(error),
                          'automatic_retry': False, 'P2_6_complete': False}), file=sys.stderr, flush=True)
        raise

