#!/usr/bin/env python3
"""Check the isolated String/Char front-end bridge; never load Core or fixtures."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parent
LOCAL = ROOT / 'local'
PACKAGES = Path('/workspace/library-files/p34-proof-work/.lake/packages')
RUNTIME = Path('/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux')
PIN = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
MODULES = [
    ('ImbalancedChen.P2OriginalSaving19CharInputBridge',
     'ImbalancedChen/P2OriginalSaving19CharInputBridge.lean'),
]


def fingerprint(path):
    with path.open('rb') as stream:
        return {'bytes': os.fstat(stream.fileno()).st_size,
                'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}


def main():
    lean = RUNTIME / 'bin/lean'
    checker = RUNTIME / 'bin/leanchecker'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PACKAGES / 'mathlib').decode().strip() == PIN
    version = subprocess.check_output([str(lean), '--version']).decode().strip()
    assert '4.33.0-rc1' in version and '62eed1db4d67327ec8120be05f1a1b0847d74561' in version
    LOCAL.mkdir(parents=True, exist_ok=True)
    lib = LOCAL / 'lib/lean'
    env = os.environ.copy()
    env['PATH'] = str(RUNTIME / 'bin') + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = ':'.join(map(str, [lib] + sorted(PACKAGES.glob('*/.lake/build/lib/lean'))))
    package_marker = RUNTIME / 'lib/lean/Lean.olean'
    marker_before = fingerprint(package_marker)
    result = {'status': 'LOCAL_GENERIC_DIAGNOSTIC_STARTED_NO_P1_ACCEPTANCE',
              'lean_version': version, 'lean': {'path': str(lean), **fingerprint(lean)},
              'mathlib_commit': PIN, 'LEAN_PATH': env['LEAN_PATH'], 'working_directory': str(ROOT),
              'project_Core_imported': False, 'original_fixtures_loaded': False,
              'archive_complete': False, 'only_cell00_proved': False,
              'library_rebuilt': False, 'P34_sources_or_objects_modified': False,
              'remote_jobs_started': False, 'commands': []}
    for module, relative in MODULES:
        source = ROOT / relative
        output = lib / Path(relative).with_suffix('.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        for stage, command in (
            ('normal', [str(lean), '-j1', '-M4096', '-o', str(output), str(source)]),
            ('kernel', [str(checker), '--verbose', module])):
            log = LOCAL / (module + '-' + stage + '.log')
            started = time.monotonic()
            with log.open('w') as stream:
                completed = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                           stderr=subprocess.STDOUT, timeout=60)
            row = {'module': module, 'stage': stage, 'command': command,
                   'exit_code': completed.returncode, 'elapsed_seconds': time.monotonic() - started,
                   'source': {'path': str(source), **fingerprint(source)},
                   'object': ({'path': str(output), **fingerprint(output)} if output.exists() else None),
                   'log': {'path': str(log), **fingerprint(log)}}
            result['commands'].append(row)
            print(json.dumps(row, sort_keys=True), flush=True)
            if completed.returncode != 0:
                result['status'] = 'LOCAL_GENERIC_DIAGNOSTIC_FAILED_NO_P1_ACCEPTANCE'
                (LOCAL / 'DIAGNOSTIC.json').write_text(json.dumps(result, indent=2) + '\n')
                print(log.read_text(), flush=True)
                return completed.returncode
    assert fingerprint(package_marker) == marker_before
    result['package_marker_unchanged'] = {'path': str(package_marker), **marker_before}
    result['status'] = 'LOCAL_GENERIC_NORMAL_AND_KERNEL_PASS_NO_ARCHIVE_ACCEPTANCE'
    (LOCAL / 'DIAGNOSTIC.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'archive_complete': False}, sort_keys=True), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
