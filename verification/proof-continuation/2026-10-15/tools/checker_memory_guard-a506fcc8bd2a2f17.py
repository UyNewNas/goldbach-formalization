"""Linux resource guard for one explicitly owned stock leanchecker process.

This module starts nothing on import. The caller must hold runtime_v3 slot 0
for this entire call and must require result['status'] == 'PASS'. The guard is
periodic RSS observation, not an OS hard cap. It never changes the checker.
"""
from pathlib import Path
import datetime
import hashlib
import json
import os
import signal
import subprocess
import time

def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

def snapshot(pid):
    base = Path('/proc') / str(pid)
    fields = (base / 'stat').read_text().rsplit(')', 1)[1].split()
    status = {}
    for line in (base / 'status').read_text().splitlines():
        key, _, value = line.partition(':')
        if key in ('VmRSS', 'VmHWM', 'VmSwap', 'Threads'):
            status[key] = int(value.split()[0])
    return {'pid': pid, 'ppid': int(fields[1]), 'pgrp': int(fields[2]),
            'starttime_ticks': int(fields[19]), 'state': fields[0],
            'argv': (base / 'cmdline').read_bytes().rstrip(b'\0').decode().split('\0'),
            'status': status}

def run_checker_guarded(command, *, cwd, env, log_path, receipt_path,
                        max_rss_kib=4 * 1024 * 1024, poll_seconds=0.05):
    """Return terminal evidence; RESOURCE_LIMIT is never an accepted proof gate.

    Use only for one exact-module stock checker invocation after checking that
    its prefix selects no descendant modules. SIGTERM targets only this new
    Popen process through its pidfd. Keep the shared slot until actual exit.
    """
    assert Path(command[0]).name == 'leanchecker', 'This guard is scoped to stock leanchecker'
    assert 0 < max_rss_kib <= 4 * 1024 * 1024, 'The memory budget must not be raised'
    assert 0 < poll_seconds <= 0.1
    log_path, receipt_path = Path(log_path), Path(receipt_path)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    record = {'status': 'STARTING', 'command': list(command), 'cwd': str(cwd),
              'max_rss_kib_budget': max_rss_kib, 'poll_seconds': poll_seconds,
              'guard_source_sha256': sha(__file__), 'checker_sha256': sha(command[0]),
              'scope': 'Owned checker RSS guard, not an OS hard memory limit',
              'signals_sent': [], 'samples': 0, 'max_observed_rss_kib': 0,
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    def save():
        receipt_path.write_text(json.dumps(record, indent=2) + '\n')
    save()
    with log_path.open('wb') as log:
        started = time.monotonic()
        proc = subprocess.Popen(command, cwd=cwd, env=env, stdout=log,
                                stderr=subprocess.STDOUT, start_new_session=True)
        fd = None
        limit_seen = False
        guard_error = None
        last_save = started
        try:
            fd = os.pidfd_open(proc.pid)
            identity = snapshot(proc.pid)
            assert identity['pgrp'] == proc.pid
            record.update(status='RUNNING', child_pid=proc.pid, initial_identity=identity)
            save()
            while True:
                ended, wait_status, usage = os.wait4(proc.pid, os.WNOHANG)
                if ended:
                    proc.returncode = os.waitstatus_to_exitcode(wait_status)
                    break
                try:
                    current = snapshot(proc.pid)
                except FileNotFoundError:
                    # The next wait4 obtains the actual terminal and its usage.
                    time.sleep(poll_seconds)
                    continue
                assert current['starttime_ticks'] == identity['starttime_ticks']
                assert current['pgrp'] == proc.pid
                rss = current['status'].get('VmRSS', 0)
                record['samples'] += 1
                if rss > record['max_observed_rss_kib']:
                    record.update(max_observed_rss_kib=rss, peak_observed_snapshot=current)
                if rss > max_rss_kib and not limit_seen:
                    limit_seen = True
                    record.update(status='RESOURCE_LIMIT_SIGNAL_PENDING', limit_snapshot=current)
                    save()
                    try:
                        signal.pidfd_send_signal(fd, signal.SIGTERM)
                        record['signals_sent'].append({'signal': int(signal.SIGTERM),
                            'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                            'identity': current})
                        record['status'] = 'RESOURCE_LIMIT_WAITING_FOR_TRUE_TERMINAL'
                    except ProcessLookupError:
                        record['status'] = 'RESOURCE_LIMIT_OBSERVED_PROCESS_ALREADY_EXITED'
                    save()
                if time.monotonic() - last_save >= 1:
                    save()
                    last_save = time.monotonic()
                time.sleep(poll_seconds)
        except BaseException as error:
            # Never let a guard/parser failure release the caller's shared
            # slot with its checker still alive. Stop only our owned pidfd,
            # then wait for the real terminal before returning a failed gate.
            guard_error = f'{type(error).__name__}: {error}'
            record.update(status='GUARD_ERROR_WAITING_FOR_OWNED_TERMINAL', guard_error=guard_error)
            if proc.returncode is None:
                try:
                    if fd is not None:
                        signal.pidfd_send_signal(fd, signal.SIGTERM)
                    else:
                        # This is our newly spawned, never-waited child. Its
                        # PID cannot be reused until we reap it. This fallback
                        # is exclusively for pidfd initialization failure.
                        os.kill(proc.pid, signal.SIGTERM)
                    record['signals_sent'].append({'signal': int(signal.SIGTERM),
                        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                        'reason': 'guard error; avoid releasing shared slot with owned child alive',
                        'mechanism': 'pidfd' if fd is not None else 'owned-never-reaped-child-pid'})
                except ProcessLookupError:
                    pass
                _, wait_status, usage = os.wait4(proc.pid, 0)
                proc.returncode = os.waitstatus_to_exitcode(wait_status)
        finally:
            if fd is not None:
                os.close(fd)
    max_rss = usage.ru_maxrss
    over_budget = limit_seen or max_rss > max_rss_kib
    record.update(status='GUARD_ERROR' if guard_error else 'RESOURCE_LIMIT' if over_budget else
                  ('PASS' if proc.returncode == 0 else 'CHECKER_FAILED'),
                  returncode=proc.returncode, wall_seconds=round(time.monotonic() - started, 3),
                  max_rss_kib=max_rss, user_cpu_seconds=usage.ru_utime,
                  system_cpu_seconds=usage.ru_stime, log_path=str(log_path),
                  log_sha256=sha(log_path), finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  mathematical_failure_claimed=False)
    save()
    return record
