#!/usr/bin/env python3
"""Bound a guarded aggregate command; receipts are diagnostics, not proof acceptance.

Linux /proc is required. Runtime compiler guarding is deliberately external.
Existing evidence is never overwritten. A killed runner can leave a 'running'
receipt; only this runner's observed terminal child status completes it.
"""
import argparse
import datetime as dt
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def process(pid):
    """Read identity as (pid, kernel start tick), tolerating disappearing tasks."""
    try:
        root = Path('/proc') / str(pid)
        stat = (root / 'stat').read_text()
        end = stat.rindex(')')
        fields = stat[end + 2:].split()
        argv = (root / 'cmdline').read_bytes().decode(errors='replace').split('\0')
        argv = [s for s in argv if s]
        sources = [s for s in argv[1:] if s.endswith('.lean')]
        setup = []
        for i, arg in enumerate(argv):
            if arg == '--setup' and i + 1 < len(argv):
                setup.append(argv[i + 1])
            elif arg.startswith('--setup='):
                setup.append(arg.split('=', 1)[1])
        ticks = os.sysconf('SC_CLK_TCK')
        return dict(pid=pid, ppid=int(fields[1]), process=stat[stat.index('(')+1:end],
                    start_ticks=int(fields[19]),
                    cpu_seconds=(int(fields[11])+int(fields[12])) / ticks,
                    rss_bytes=int(fields[21]) * os.sysconf('SC_PAGE_SIZE'),
                    argv=argv, source_paths=sources, setup_paths=setup)
    except (OSError, ValueError, IndexError):
        return None


def descendants(root_pid):
    table = {int(p.name): process(int(p.name)) for p in Path('/proc').iterdir()
             if p.name.isdigit()}
    table = {p: v for p, v in table.items() if v is not None}
    selected = {root_pid}
    while True:
        more = {p for p, v in table.items() if v['ppid'] in selected}
        if more <= selected:
            break
        selected |= more
    uptime = float(Path('/proc/uptime').read_text().split()[0])
    ticks = os.sysconf('SC_CLK_TCK')
    rows = [table[p] for p in sorted(selected) if p in table]
    for row in rows:
        row['elapsed_seconds'] = max(0, uptime - row['start_ticks'] / ticks)
    return rows


def compiler(row):
    names = {row['process'], Path(row['argv'][0]).name if row['argv'] else ''}
    return bool(names & {'lean', 'lean-runtime', 'lean-real'}) and bool(
        row['source_paths'] or row['setup_paths'])


def signal_identity(pid, start_ticks, sig):
    current = process(pid)
    if current and current['start_ticks'] == start_ticks:
        try:
            os.kill(pid, sig)
            return True
        except ProcessLookupError:
            pass
    return False


def group_signal(pgid, sig):
    try:
        os.killpg(pgid, sig)
    except ProcessLookupError:
        pass


def write_receipt(path, receipt):
    temporary = path.with_name(path.name + '.tmp')
    with temporary.open('x') as f:
        json.dump(receipt, f, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    temporary.replace(path)


def run(args):
    if not Path('/proc/self/stat').exists():
        raise RuntimeError('Linux /proc is required')
    paths = [args.log, args.heartbeat, args.receipt, args.source_events]
    if len({p.absolute() for p in paths}) != 4:
        raise ValueError('Evidence paths must be distinct')
    if any(p.exists() for p in paths) or args.receipt.with_name(args.receipt.name+'.tmp').exists():
        raise ValueError('Evidence exists; refusing overwrite')
    if min(args.timeout, args.source_timeout, args.poll_interval,
           args.heartbeat_interval, args.kill_grace) <= 0:
        raise ValueError('All time bounds must be positive')
    for p in paths:
        p.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    receipt = dict(started_at=utc(), status='running', command=args.command,
                   timeout_seconds=args.timeout, source_timeout_seconds=args.source_timeout,
                   source_timeouts=[], child_returncode=None)
    # Exclusive initial creation prevents two runners sharing receipts.
    with args.receipt.open('x') as f:
        json.dump(receipt, f, indent=2)
    child = None
    interrupted = []
    old_handlers = {}
    for sig in (signal.SIGTERM, signal.SIGINT):
        old_handlers[sig] = signal.signal(sig, lambda s, frame: interrupted.append(s))
    reason = None
    stop_at = None
    source_kills = {}
    active_since = {}
    last_heartbeat = -float('inf')
    error = None
    try:
        with args.log.open('xb') as log, args.heartbeat.open('x') as beats, args.source_events.open('x') as events:
            child = subprocess.Popen(args.command, stdout=log, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            receipt['process_group'] = child.pid
            write_receipt(args.receipt, receipt)
            while child.poll() is None:
                now = time.monotonic()
                elapsed = now - started
                rows = descendants(child.pid)
                for row in rows:
                    if compiler(row):
                        key = (row['pid'], row['start_ticks'])
                        # A guard wrapper execs Lean in the same PID after flock.
                        # /proc starttime includes lock wait, so begin the source
                        # budget only when the process first becomes a compiler.
                        active_since.setdefault(key, now)
                        row['active_elapsed_seconds'] = now - active_since[key]
                if now - last_heartbeat >= args.heartbeat_interval:
                    beats.write(json.dumps(dict(timestamp=utc(), runner_elapsed_seconds=elapsed,
                                                process_group=child.pid, processes=rows))+'\n')
                    beats.flush()
                    last_heartbeat = now
                if reason is None:
                    if interrupted:
                        reason = 'interrupted'
                    elif args.stop_file and args.stop_file.exists():
                        reason = 'stop_requested'
                    elif elapsed >= args.timeout:
                        reason = 'timeout'
                    if reason:
                        stop_at = now
                        group_signal(child.pid, signal.SIGTERM)
                if reason and now - stop_at >= args.kill_grace:
                    group_signal(child.pid, signal.SIGKILL)
                if reason is None:
                    for row in rows:
                        key = (row['pid'], row['start_ticks'])
                        if compiler(row) and row['active_elapsed_seconds'] >= args.source_timeout and key not in source_kills:
                            event = dict(timestamp=utc(), action='source_timeout_term', **row)
                            event['signal_sent'] = signal_identity(*key, signal.SIGTERM)
                            events.write(json.dumps(event)+'\n'); events.flush()
                            receipt['source_timeouts'].append(event)
                            source_kills[key] = now
                            write_receipt(args.receipt, receipt)
                    for key, when in list(source_kills.items()):
                        if when is not None and now - when >= args.kill_grace:
                            sent = signal_identity(*key, signal.SIGKILL)
                            events.write(json.dumps(dict(timestamp=utc(), action='source_timeout_kill',
                                                         pid=key[0], start_ticks=key[1], signal_sent=sent))+'\n')
                            events.flush()
                            source_kills[key] = None
                time.sleep(args.poll_interval)
            # Complete pending individual termination even if the aggregate leader exits.
            for key, when in source_kills.items():
                if when is not None and process(key[0]):
                    time.sleep(max(0, args.kill_grace - (time.monotonic() - when)))
                    sent = signal_identity(*key, signal.SIGKILL)
                    events.write(json.dumps(dict(timestamp=utc(), action='source_timeout_kill',
                                                 pid=key[0], start_ticks=key[1], signal_sent=sent))+'\n')
                    events.flush()
            # The leader can exit before descendants after TERM: do not leak its group.
            if reason:
                group_signal(child.pid, signal.SIGTERM)
                time.sleep(args.kill_grace)
                group_signal(child.pid, signal.SIGKILL)
    except BaseException as exc:
        error = f'{type(exc).__name__}: {exc}'
        reason = 'runner_error' if not isinstance(exc, KeyboardInterrupt) else 'interrupted'
        if child:
            group_signal(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=args.kill_grace)
            except subprocess.TimeoutExpired:
                pass
            group_signal(child.pid, signal.SIGKILL)
            child.wait()
    finally:
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
    actual = child.returncode if child else None
    status = reason or ('source_timeout' if receipt['source_timeouts'] else
                        'success' if actual == 0 else 'failure')
    code = (124 if status in ('timeout', 'source_timeout') else
            130 if status in ('interrupted', 'stop_requested') else
            2 if status == 'runner_error' else actual if actual is not None and actual >= 0 else 1)
    receipt.update(status=status, child_returncode=actual, exit_code=code,
                   finished_at=utc(), elapsed_seconds=time.monotonic()-started)
    if interrupted:
        receipt['received_signals'] = interrupted
    if error:
        receipt['error'] = error
    write_receipt(args.receipt, receipt)
    return code


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--timeout', type=float, default=16200)
    p.add_argument('--source-timeout', type=float, default=1800)
    p.add_argument('--poll-interval', type=float, default=1)
    p.add_argument('--heartbeat-interval', type=float, default=30)
    p.add_argument('--kill-grace', type=float, default=10)
    for name in ('log', 'heartbeat', 'receipt', 'source-events'):
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--stop-file', type=Path)
    p.add_argument('command', nargs=argparse.REMAINDER)
    a = p.parse_args()
    if a.command[:1] == ['--']:
        a.command = a.command[1:]
    if not a.command:
        p.error('Missing child command')
    try:
        return run(a)
    except (ValueError, OSError, RuntimeError) as exc:
        p.error(str(exc))


if __name__ == '__main__':
    sys.exit(main())
