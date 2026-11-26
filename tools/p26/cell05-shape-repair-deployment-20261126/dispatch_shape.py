#!/usr/bin/env python3
"""Run the isolated repaired owner once and expose any original failure details.

The source package must already be installed and pinned by a separate local-first
deployment. This wrapper never retries a failed phase or touches the old stage.
"""
from pathlib import Path
import argparse
import base64
import hashlib
import json
import os
import subprocess
import sys

PACKAGE = Path('/workspace/p26-continuation-557a12f3bcd7/cell05-shape-repair-package-v1')
STAGE = Path('/workspace/p26-cell05-shape-repair-stage-557a12f3bcd7')
TOOL = Path('tools/p26/cell05-shape-repair-20261126')
ATTEMPT = 'shape-repair-v1-first'
TARGET = 'ImbalancedChen.P2OriginalSaving19Geometry05ScalableShapeArrays'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def fingerprint(path):
    need(path.is_file() and not path.is_symlink() and path.resolve() == path,
         'Noncanonical or missing file: ' + str(path))
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def show_failure():
    index = STAGE / 'verification' / ATTEMPT / 'STOPPED.json'
    if not index.exists():
        print(json.dumps({'phase': 'failure-detail', 'stopped_index_present': False,
                          'automatic_retry': False}), flush=True)
        return
    fingerprint(index)
    stopped = json.loads(index.read_text())
    if 'failed_result' not in stopped:
        print(json.dumps({'phase': 'failure-detail', 'stopped_index': fingerprint(index),
                          'failure_record_present': False, 'automatic_retry': False}), flush=True)
        return
    result_path = Path(stopped['failed_result']['path'])
    folder = index.parent / TARGET.split('.')[-1]
    need(result_path.parent == folder, 'Failure result is outside the isolated target')
    need(fingerprint(result_path) == stopped['failed_result'], 'Failure result pin differs')
    result = json.loads(result_path.read_text())
    need(result['module'] == TARGET and result['mode'] in ('normal', 'kernel', 'owned'),
         'Unexpected failed owner or mode')
    log = folder / (result['mode'] + '.log')
    need(result_path.name == result['mode'] + '-result.json' and fingerprint(log) == result['log'],
         'Original failure log binding differs')
    body = log.read_bytes()
    # Preserve the whole log in the stage; expose enough original bytes to make
    # the ordinary compiler diagnostic immediately available in task output.
    text = body.decode('utf-8', errors='replace')
    excerpt = text if len(body) <= 60000 else text[:20000] + '\n[diagnostic middle omitted]\n' + text[-20000:]
    print(json.dumps({'phase': 'failure-detail', 'stopped_index': fingerprint(index),
                      'result': fingerprint(result_path), 'status': result['status'],
                      'exit_code': result['exit_code'],
                      'termination_reason': result.get('termination_reason'),
                      'validation_error': result.get('validation_error'),
                      'original_log': fingerprint(log), 'diagnostic': excerpt,
                      'diagnostic_is_complete': len(body) <= 60000,
                      'automatic_retry': False, 'P2_6_complete': False}), flush=True)


def phase(name, argv):
    print(json.dumps({'phase': name + '-started', 'argv': argv}), flush=True)
    result = subprocess.run(argv, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    if result.returncode:
        show_failure()
        raise SystemExit(result.returncode)
    print(json.dumps({'phase': name + '-passed', 'exit_code': 0}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit-archive', action='store_true')
    args = parser.parse_args()
    entry = PACKAGE / TOOL / 'stage_entry.py'
    phase('isolated-three-checks', [sys.executable, '-B', str(entry), '--stage', str(STAGE),
                                  '--attempt', ATTEMPT, '--rss-gib', '6', '--wall-seconds', '900'])
    success_path = STAGE / 'verification' / ATTEMPT / 'SUCCESS.json'
    success = json.loads(success_path.read_text())
    need(success['status'] == 'succeeded' and success['accepted_targets'] == 1
         and success['accepted_steps'] == 3 and success['newly_executed_steps'] == 3
         and success['reused_steps'] == 0 and success['P2_6_complete'] is False,
         'Unexpected independent one-owner success boundary')
    phase('export', [sys.executable, '-B', str(STAGE / TOOL / 'export_shape.py'),
                     '--stage', str(STAGE), '--attempt', ATTEMPT, '--label', 'v1'])
    archive = STAGE / 'exports' / ('shape-repair-' + ATTEMPT + '-v1-evidence.tar.xz')
    report_path = archive.with_name(archive.name + '.json')
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes)
    need(report['status'] == 'PASS_EXPORT_RECHECK' and report['accepted_targets'] == 1
         and report['accepted_steps'] == 3 and report['archive_member_recheck_passed'] is True
         and report['old_supplier_object_bodies_included'] is False,
         'Isolated export was not completely verified')
    need(fingerprint(archive) == report['archive'], 'Export changed before readback')
    output = {'phase': 'finished', 'status': 'PASS_ISOLATED_SHAPE_THREE_CHECKS_AND_EXPORT',
              'accepted_targets': 1, 'accepted_steps': 3, 'original_report': report,
              'original_report_pin': fingerprint(report_path),
              'original_report_text': report_bytes.decode('utf-8'),
              'old_supplier_proof_commands': 0, 'old_thirteen_owner_replays': 0,
              'full_fourteen_target_success': False, 'P2_6_complete': False}
    if args.emit_archive:
        data = archive.read_bytes()
        need(len(data) == report['archive']['bytes']
             and hashlib.sha256(data).hexdigest() == report['archive']['sha256'],
             'New isolated archive changed during transfer read')
        output.update(payload_encoding='base64', payload_base64=base64.b64encode(data).decode('ascii'))
    print(json.dumps(output), flush=True)


if __name__ == '__main__':
    main()
