"""Linux sampled aggregate process-tree RSS supervision (not a kernel memory cap).

Samples /proc every poll_seconds; peak_rss_bytes is an observed peak, NOT an
absolute instantaneous peak. Counts RSS per process (shared pages double count).
Single active supervise() call per supervisor process is required. Linux child
subreaping lets us retain orphaned/setsid descendants after their parent exits.
"""
import ctypes
import os
from pathlib import Path
import signal
import subprocess
import time

PAGE_SIZE = os.sysconf('SC_PAGE_SIZE')

def _snapshot():
    result = {}
    for entry in Path('/proc').iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            raw = (entry / 'stat').read_text()
            fields = raw[raw.rfind(')') + 2:].split()
            result[int(entry.name)] = dict(state=fields[0], ppid=int(fields[1]),
                pgrp=int(fields[2]), start=int(fields[19]),
                rss=max(0, int(fields[21])) * PAGE_SIZE)
        except (OSError, ValueError, IndexError):
            pass  # Process may exit between enumeration and stat read.
    return result

def supervise(command, *, cwd=None, stdout=None, stderr=subprocess.STDOUT,
              memory_bytes=6144 * 1024**2, timeout_seconds=1800,
              batch_deadline=None, poll_seconds=0.05, kill_grace_seconds=5):
    """Run command and return a JSON-serializable receipt; kill on limit breach.

    batch_deadline is an absolute time.monotonic() deadline (e.g. start+16200).
    Exits only after observed tree termination, or reports surviving identities.
    reason: completed / memory_limit / timeout / interrupted / supervisor_error.
    A command that exits leaving live descendants is NOT yet completed.
    """
    if memory_bytes <= 0 or timeout_seconds <= 0 or poll_seconds <= 0:
        raise ValueError('limits and polling interval must be positive')
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
        raise OSError(ctypes.get_errno(), 'PR_SET_CHILD_SUBREAPER failed')
    me = os.getpid()
    initial = _snapshot()
    baseline_children = {(pid, s['start']) for pid, s in initial.items() if s['ppid'] == me}
    start = time.monotonic()
    deadline = min(start + timeout_seconds, batch_deadline if batch_deadline is not None else float('inf'))
    if deadline <= start:
        return dict(reason='timeout', exit_code=124, launched=False, termination_verified=True,
                    peak_rss_bytes=0, samples=0, survivors=[], elapsed_seconds=0)
    proc = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=stderr, start_new_session=True)
    known = {}; peak = 0; samples = 0; reason = 'completed'; error = None
    def discover():
        nonlocal peak, samples
        snap = _snapshot()
        # Seed own session/group and new adopted children, then follow arbitrary
        # descendants, including descendants that create a separate session.
        selected = {pid for pid, s in snap.items() if
            known.get(pid) == s['start'] or pid == proc.pid or s['pgrp'] == proc.pid or
            (s['ppid'] == me and (pid, s['start']) not in baseline_children)}
        while True:
            extra = {pid for pid, s in snap.items() if s['ppid'] in selected}
            if extra <= selected: break
            selected |= extra
        for pid in selected: known[pid] = snap[pid]['start']
        live = {pid: snap[pid] for pid in selected if snap[pid]['state'] not in ('Z', 'X')}
        rss = sum(s['rss'] for s in live.values()); samples += 1; peak = max(peak, rss)
        return live, rss
    def terminate():
        # SIGKILL immediately avoids allocating further during a grace period.
        end = time.monotonic() + kill_grace_seconds
        while True:
            live, _ = discover()
            for pid, s in live.items():
                try:
                    current = _snapshot().get(pid)
                    if current and current['start'] == s['start']: os.kill(pid, signal.SIGKILL)
                except ProcessLookupError: pass
            proc.poll()
            if not live: return []
            if time.monotonic() >= end:
                return [{'pid': pid, 'start': s['start']} for pid, s in discover()[0].items()]
            time.sleep(min(poll_seconds, 0.05))
    survivors = []
    try:
        while True:
            live, rss = discover(); code = proc.poll()
            if rss > memory_bytes: reason = 'memory_limit'; break
            if not live and code is not None: break
            if time.monotonic() >= deadline: reason = 'timeout'; break
            time.sleep(min(poll_seconds, max(0, deadline-time.monotonic())))
        if reason != 'completed': survivors = terminate()
    except BaseException as exc:
        reason = 'interrupted' if isinstance(exc, (KeyboardInterrupt, SystemExit)) else 'supervisor_error'
        error = repr(exc); survivors = terminate()
    finally:
        proc.poll()
        # Reap adopted zombies without consuming unrelated pre-existing children.
        for pid in known:
            if pid == proc.pid: continue
            try: os.waitpid(pid, os.WNOHANG)
            except ChildProcessError: pass
    return dict(reason=reason, exit_code=(proc.returncode if reason == 'completed' else 124 if reason == 'timeout' else 137 if reason == 'memory_limit' else 125),
        root_returncode=proc.returncode, launched=True, termination_verified=not survivors,
        survivors=survivors, peak_rss_bytes=peak, samples=samples, elapsed_seconds=time.monotonic()-start,
        memory_bytes=memory_bytes, poll_seconds=poll_seconds,
        memory_semantics='sampled aggregate process RSS; shared pages double-counted; transient peaks may be missed',
        observed_processes=[{'pid': p, 'start': t} for p,t in sorted(known.items())], error=error)
