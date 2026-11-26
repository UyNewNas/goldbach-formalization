#!/usr/bin/env python3
"""Bounded diagnostic only: locate the stalled command in frozen FieldDecode.

No proof acceptance, replay, audit, dependency compilation, or publication occurs.
The sole source edits are pure #check Nat markers. A PTY makes their incremental
CLI reporting line-buffered; the original strict Lean flags are unchanged.
"""
from pathlib import Path
import errno
import hashlib
import json
import os
import pty
import re
import select
import shutil
import signal
import subprocess
import sys
import time
import traceback

ROOT = Path('/workspace/p25-q96-20261125')
PRIOR = ROOT / '.lake/diagnostic/p25-cell00-field-decode-attempt002'
OUT = ROOT / '.lake/diagnostic/p25-field-progress-attempt001'
PUBLICATION = '8fa1d8c84f8c465da8f8fd00bfce1410e1807ae3'
RESULT_SHA = '3af403db2e1e5bb09b0e9cd82d23984305e05265a7ee43d9abd4d12d517e2392'
SOURCE_SHA = '3bca40fbe7f5484ce50da650d9c505026e1634f0c0accdcda3dfe93ab5698b96'
PROGRESS_SHA = 'b1f545aec461c218d494390c7f1c300d1016c2fe09903c745aae9394db03f55b'
TARGET = 'ImbalancedChen.P2Saving16Cell00FieldDecode'
DIAGNOSTIC = 'ImbalancedChen.P2Saving16Cell00FieldProgress'
FLAGS = ['-t0', '-j1', '-M11264', '-DwarningAsError=true',
         '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
WALL_SECONDS = 90


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def record(path):
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha(path)}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def instrument(raw):
    original = raw.decode()
    output, names = [], []
    for number, line in enumerate(original.splitlines(keepends=True), 1):
        match = re.match(r'^(private )?theorem (\w+)', line)
        if match:
            marker = 900000 + len(names)
            names.append({'marker': marker, 'name': match.group(2),
                          'private': bool(match.group(1)), 'original_line': number,
                          'diagnostic_marker_line': len(output) + 1})
            output.append(f'#check ({marker} : Nat)\n')
        if line.startswith('end ImbalancedChen.P2Saving16Cell00FieldDecode'):
            output.append('#check (900442 : Nat)\n')
        output.append(line)
    source = ''.join(output)
    require(len(names) == 442 and sum(not row['private'] for row in names) == 146,
            'Original declaration inventory differs.')
    require(re.sub(r'^#check \(900\d{3} : Nat\)\n', '', source, flags=re.M) == original,
            'Instrumentation modified an original source command.')
    require(hashlib.sha256(source.encode()).hexdigest() == PROGRESS_SHA,
            'Diagnostic source differs from the reviewed exact insertion transform.')
    return source.encode(), names


def main():
    require(len(sys.argv) == 2 and re.fullmatch('[0-9a-f]{64}', sys.argv[1]),
            'Pass the independently reviewed runner SHA256.')
    require(sha(__file__) == sys.argv[1], 'Runner self hash differs.')
    require(not OUT.exists(), 'Preserve the previous diagnostic; refuse to overwrite.')
    OUT.mkdir()
    state = {'schema': 'p25-bounded-field-progress-v1', 'status': 'PREFLIGHT',
             'accepted': False, 'formal_credit': False, 'P2_5_proved': False,
             'diagnostic_only': True, 'dependency_modules_compiled': [],
             'wall_limit_seconds': WALL_SECONDS, 'strict_flags': FLAGS,
             'runner': record(Path(__file__)), 'prior_result_sha256': RESULT_SHA}
    frozen = {}

    def bind(path, expected):
        path = Path(path)
        require(path.is_file() and sha(path) == expected, 'Pinned file differs: ' + str(path))
        frozen[str(path)] = expected
        return path

    def check_frozen():
        require(all(sha(Path(path)) == expected for path, expected in frozen.items()),
                'A diagnostic input changed during the bounded run.')

    try:
        receipt_path = bind(PRIOR / 'RESULT.json', RESULT_SHA)
        receipt = json.loads(receipt_path.read_text())
        failed = receipt['modules'][TARGET]
        normal = failed['stages']['normal']
        require(receipt['publication_commit'] == PUBLICATION and receipt['accepted'] is False
                and receipt['status'] == 'MODULE_STAGE_FAILED' and receipt['failed_module'] == TARGET
                and failed['accepted'] is False and normal['timed_out'] is True
                and normal['exit_code'] == 124 and normal['log_bytes'] == 0,
                'Expected the exact bounded-time failure with no accepted Field owner.')
        require(receipt['strict_flags'] == FLAGS and normal['command'][1:7] == FLAGS,
                'Original strict compiler flags differ.')
        for path, expected in receipt['frozen_inputs'].items():
            bind(path, expected)
        source_path = bind(failed['source_copy']['path'], SOURCE_SHA)
        raw = source_path.read_bytes()
        source, names = instrument(raw)
        require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT).decode().strip() == PUBLICATION,
                'P3 publication changed before the bounded diagnostic.')
        require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT),
                'Tracked P3 worktree is not clean.')
        require(subprocess.check_output(['git', 'show', PUBLICATION + ':' + failed['source_origin']['path']],
                                        cwd=ROOT) == raw, 'Frozen source is not the exact published version.')
        lean = bind(receipt['runtime']['lean']['path'], receipt['runtime']['lean']['sha256'])
        require(subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                    cwd=receipt['runtime']['mathlib_path']).decode().strip() == receipt['runtime']['mathlib_pin'],
                'Mathlib pin changed.')
        deps = {**receipt['dependency_objects'], **receipt['reused_owner_objects']}
        require(len(receipt['dependency_objects']) == 8 and len(receipt['reused_owner_objects']) == 3
                and len(deps) == 11 and TARGET not in deps, 'Unexpected accepted dependency selection.')
        src, lib = OUT / 'src', OUT / 'lib'
        (src / 'ImbalancedChen').mkdir(parents=True)
        (lib / 'ImbalancedChen').mkdir(parents=True)
        copied = {}
        for module, row in deps.items():
            if module in receipt['reused_owner_objects']:
                require(receipt['modules'][module]['accepted'] is True
                        and receipt['modules'][module]['object']['sha256'] == row['sha256'],
                        'A reused owner is not accepted.')
            original = bind(row['isolated_path'], row['sha256'])
            destination = lib / (module.replace('.', '/') + '.olean')
            shutil.copyfile(original, destination)
            bind(destination, row['sha256'])
            copied[module] = record(destination)
        require(len(list((lib / 'ImbalancedChen').glob('*.olean'))) == 11
                and not (lib / (TARGET.replace('.', '/') + '.olean')).exists(),
                'Failed Field object must not enter the diagnostic library.')
        diagnostic_source = src / (DIAGNOSTIC.replace('.', '/') + '.lean')
        diagnostic_object = lib / (DIAGNOSTIC.replace('.', '/') + '.olean')
        diagnostic_source.write_bytes(source)
        bind(diagnostic_source, PROGRESS_SHA)
        write_json(OUT / 'PROGRESS_MAP.json', {'markers': names, 'final_marker': 900442})
        search = receipt['approved_LEAN_PATH'].split(os.pathsep)
        require(Path(search[0]) == PRIOR / 'lib' and len(search) == len(set(search)),
                'Expected original isolated dependency path first, with no duplicate providers.')
        env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(lib), *search[1:]]),
                   LEAN_SYSROOT=str(lean.parent.parent))
        command = [str(lean), *FLAGS, '--json', '--root=' + str(src), '-o', str(diagnostic_object), str(diagnostic_source)]
        state.update(status='RUNNING_BOUNDED_DIAGNOSTIC', command=command,
                     source_origin=failed['source_origin'], original_source=record(source_path),
                     diagnostic_source=record(diagnostic_source), copied_dependencies=copied,
                     frozen_inputs=dict(frozen), approved_LEAN_PATH=env['LEAN_PATH'],
                     stream_mode='PTY for line-buffered incremental JSON diagnostic messages')
        write_json(OUT / 'RESULT.json', state)
        check_frozen()
        start = time.monotonic()
        master, slave = pty.openpty()
        process = subprocess.Popen(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                   stdout=slave, stderr=slave, start_new_session=True)
        os.close(slave)
        os.set_blocking(master, False)
        timed_out, closed, killed_at = False, False, None
        with (OUT / 'NORMAL.log').open('wb') as log:
            while not closed:
                elapsed = time.monotonic() - start
                if process.poll() is None and elapsed >= WALL_SECONDS and not timed_out:
                    timed_out = True
                    killed_at = time.monotonic()
                    os.killpg(process.pid, signal.SIGTERM)
                if killed_at is not None and process.poll() is None and time.monotonic() - killed_at > 5:
                    os.killpg(process.pid, signal.SIGKILL)
                    killed_at = None
                if select.select([master], [], [], 0.1)[0]:
                    try:
                        block = os.read(master, 65536)
                    except OSError as error:
                        if error.errno != errno.EIO:
                            raise
                        block = b''
                    if not block:
                        closed = True
                    else:
                        log.write(block)
                        log.flush()
                elif process.poll() is not None:
                    # PTY eventually becomes readable with EIO after its last writer exits.
                    continue
        os.close(master)
        code = process.wait(timeout=10)
        elapsed = time.monotonic() - start
        check_frozen()
        text = (OUT / 'NORMAL.log').read_text(errors='replace')
        markers = []
        marker_lines = {row['marker']: row['diagnostic_marker_line'] for row in names}
        marker_lines[900442] = next(number for number, line in enumerate(source.decode().splitlines(), 1)
                                    if line == '#check (900442 : Nat)')
        for line in text.splitlines():
            try:
                message = json.loads(line)
            except json.JSONDecodeError:
                continue
            match = re.fullmatch(r'(900\d{3}) : (?:Nat|ℕ)\s*', message.get('data', ''))
            if match:
                marker = int(match.group(1))
                require(message.get('fileName') == str(diagnostic_source)
                        and message.get('pos', {}).get('line') == marker_lines.get(marker),
                        'A marker message does not belong to its exact inserted command position.')
                markers.append(marker)
        require(markers == sorted(set(markers)) and all(900000 <= m <= 900442 for m in markers),
                'Diagnostic marker order or bounds differ.')
        last = markers[-1] if markers else None
        by_marker = {row['marker']: row for row in names}
        before_last = [row for row in names if last is not None and row['marker'] < last]
        public_before = [row for row in before_last if not row['private']]
        state.update(status='BOUNDED_DIAGNOSTIC_FINISHED', timed_out=timed_out,
                     exit_code=124 if timed_out else code, process_exit_code=code,
                     seconds=round(elapsed, 3), normal_log=record(OUT / 'NORMAL.log'),
                     markers_seen=markers, last_marker=last,
                     next_command_at_last_marker=by_marker.get(last),
                     last_public_command_before_marker=public_before[-1] if public_before else None,
                     interpretation='Command-boundary progress only; no proof acceptance or claim that every preceding asynchronous proof is kernel-accepted.',
                     diagnostic_object=record(diagnostic_object) if diagnostic_object.is_file() else None)
        write_json(OUT / 'RESULT.json', state)
        print('P25_FIELD_PROGRESS_RESULT', json.dumps({k: state[k] for k in
              ('status', 'timed_out', 'exit_code', 'seconds', 'last_marker', 'next_command_at_last_marker',
               'last_public_command_before_marker', 'accepted')}, sort_keys=True), flush=True)
        return 0
    except BaseException as error:
        state.update(status='DIAGNOSTIC_FAILED', error=str(error), traceback=traceback.format_exc())
        write_json(OUT / 'RESULT.json', state)
        print('P25_FIELD_PROGRESS_FAILED', str(error), flush=True)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
