"""Small subprocess tests only; never invoke Lean or Lake."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

import bounded_source_build as runner


@unittest.skipUnless(Path('/proc/self/stat').exists(), 'Linux /proc required')
class BoundedBuildTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def command(self, code, *extra, bounds=()):
        cmd = [sys.executable, str(Path(runner.__file__).resolve()),
               '--log', str(self.root/'build.log'), '--heartbeat', str(self.root/'heartbeat.jsonl'),
               '--receipt', str(self.root/'receipt.json'), '--source-events', str(self.root/'sources.jsonl'),
               '--poll-interval', '.02', '--heartbeat-interval', '.02', '--kill-grace', '.08',
               '--timeout', '5', '--source-timeout', '3', *bounds,
               '--', sys.executable, '-c', code, *extra]
        return cmd

    def invoke(self, code, *extra, bounds=()):
        result = subprocess.run(self.command(code, *extra, bounds=bounds), capture_output=True, timeout=8)
        receipt = json.loads((self.root/'receipt.json').read_text())
        return result, receipt

    def test_success_and_failure_actual_status(self):
        result, receipt = self.invoke("print('observed output'); raise SystemExit(7)")
        self.assertEqual(result.returncode, 7)
        self.assertEqual(receipt['status'], 'failure')
        self.assertEqual(receipt['child_returncode'], 7)
        self.assertIn(b'observed output', (self.root/'build.log').read_bytes())

    def test_success(self):
        result, receipt = self.invoke("print('done')")
        self.assertEqual(result.returncode, 0)
        self.assertEqual(receipt['status'], 'success')
        self.assertEqual(receipt['child_returncode'], 0)
        self.assertEqual(receipt['source_timeouts'], [])

    def test_wall_timeout_kills_group(self):
        code = "import subprocess,sys,time; p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(20)']); print(p.pid,flush=True);time.sleep(20)"
        result, receipt = self.invoke(code, bounds=('--timeout', '.15'))
        self.assertEqual(result.returncode, 124)
        self.assertEqual(receipt['status'], 'timeout')
        self.assertLess(receipt['child_returncode'], 0)
        pid = int((self.root/'build.log').read_text().strip())
        task = runner.process(pid)
        if task:  # A reparented zombie may await init's reaper; it is not running.
            stat = Path(f'/proc/{pid}/stat').read_text().split(') ', 1)[1]
            self.assertEqual(stat[0], 'Z')

    def test_waiting_python_guard_is_not_a_compiler(self):
        fake = "import ctypes,time;ctypes.CDLL(None).prctl(15,b'lean-runtime',0,0,0);time.sleep(.07)"
        # Simulate waiting for a serial compiler lock, then spawning the real
        # compiler. The wrapper's .lean argument must not start its source clock.
        code = f"import subprocess,sys,time;time.sleep(.35);raise SystemExit(subprocess.call([sys.executable,'-c',{fake!r},'Queued.lean']))"
        result, receipt = self.invoke(code, 'Queued.lean', bounds=('--source-timeout', '.2'))
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(receipt['status'], 'success')
        self.assertEqual(receipt['source_timeouts'], [])
        beats = [json.loads(s) for s in (self.root/'heartbeat.jsonl').read_text().splitlines()]
        rows = [row for beat in beats for row in beat['processes']]
        waiting = [row for row in rows if row['pid'] == receipt['process_group']
                   and row['elapsed_seconds'] > .2]
        self.assertTrue(waiting)
        self.assertTrue(all(row['source_paths'] == ['Queued.lean'] for row in waiting))
        self.assertTrue(all(not runner.compiler(row) for row in waiting))
        active = [row for row in rows if runner.compiler(row)]
        self.assertTrue(active)
        self.assertTrue(all(row['pid'] != receipt['process_group'] for row in active))
        self.assertTrue(all(row['elapsed_seconds'] < .2 for row in active))

    def test_same_pid_guard_to_compiler_gets_fresh_source_budget(self):
        # prctl changes the same PID's observed name just as exec of
        # lean-runtime does, retaining /proc's pre-lock process start tick.
        code = "import ctypes,time;time.sleep(.35);ctypes.CDLL(None).prctl(15,b'lean-runtime',0,0,0);time.sleep(.07)"
        result, receipt = self.invoke(code, 'Queued.lean', bounds=('--source-timeout', '.2'))
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(receipt['status'], 'success')
        self.assertEqual(receipt['source_timeouts'], [])
        beats = [json.loads(s) for s in (self.root/'heartbeat.jsonl').read_text().splitlines()]
        active = [row for beat in beats for row in beat['processes'] if runner.compiler(row)]
        self.assertTrue(active)
        self.assertTrue(all(row['pid'] == receipt['process_group'] for row in active))
        self.assertTrue(all(row['elapsed_seconds'] >= .3 for row in active))
        self.assertTrue(all(row['active_elapsed_seconds'] < .2 for row in active))

    def test_source_timeout_retained_even_when_aggregate_returns_zero(self):
        fake = "import ctypes,signal,time;ctypes.CDLL(None).prctl(15,b'lean-runtime',0,0,0);signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(20)"
        code = f"import subprocess,sys; p=subprocess.Popen([sys.executable,'-c',{fake!r},'Example.lean','--setup=Example.setup.json']);p.wait();print('aggregate continued')"
        result, receipt = self.invoke(code, bounds=('--source-timeout', '.15'))
        self.assertEqual(result.returncode, 124)
        self.assertEqual(receipt['status'], 'source_timeout')
        self.assertEqual(receipt['child_returncode'], 0)
        self.assertEqual(len(receipt['source_timeouts']), 1)
        event = receipt['source_timeouts'][0]
        self.assertEqual(event['source_paths'], ['Example.lean'])
        self.assertEqual(event['setup_paths'], ['Example.setup.json'])
        self.assertIn('aggregate continued', (self.root/'build.log').read_text())
        events = [json.loads(s) for s in (self.root/'sources.jsonl').read_text().splitlines()]
        self.assertTrue(any(e['action'] == 'source_timeout_kill' and e['signal_sent'] for e in events))
        beats = [json.loads(s) for s in (self.root/'heartbeat.jsonl').read_text().splitlines()]
        self.assertTrue(any(len(b['processes']) > 1 for b in beats))

    def test_stop_file(self):
        stop = self.root/'stop'
        stop.touch()
        result, receipt = self.invoke('import time;time.sleep(20)', bounds=('--stop-file', str(stop)))
        self.assertEqual(result.returncode, 130)
        self.assertEqual(receipt['status'], 'stop_requested')

    def test_signal_interruption_receipt(self):
        child = subprocess.Popen(self.command('import time;time.sleep(20)'), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.addCleanup(lambda: child.poll() is None and child.kill())
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            p = self.root/'receipt.json'
            try:
                if 'process_group' in json.loads(p.read_text()):
                    break
            except (OSError, ValueError):
                pass
            time.sleep(.01)
        child.send_signal(signal.SIGTERM)
        child.communicate(timeout=3)
        self.assertEqual(child.returncode, 130)
        receipt = json.loads((self.root/'receipt.json').read_text())
        self.assertEqual(receipt['status'], 'interrupted')
        self.assertEqual(receipt['received_signals'], [signal.SIGTERM])
        self.assertIsNotNone(receipt['child_returncode'])

    def test_existing_evidence_is_not_overwritten(self):
        self.invoke("print('first')")
        original = {p.name: p.read_bytes() for p in self.root.iterdir()}
        result = subprocess.run(self.command("print('second')"), capture_output=True, timeout=3)
        self.assertEqual(result.returncode, 2)
        self.assertEqual(original, {p.name: p.read_bytes() for p in self.root.iterdir()})

    def test_start_failure_is_not_success(self):
        command = self.command('unused')
        boundary = command.index('--')
        command[boundary+1:] = ['/definitely/not/a/real/executable']
        result = subprocess.run(command, capture_output=True, timeout=3)
        self.assertEqual(result.returncode, 2)
        receipt = json.loads((self.root/'receipt.json').read_text())
        self.assertEqual(receipt['status'], 'runner_error')
        self.assertIsNone(receipt['child_returncode'])
        self.assertIn('FileNotFoundError', receipt['error'])

    def test_identity_mismatch_does_not_signal(self):
        row = runner.process(os.getpid())
        self.assertFalse(runner.signal_identity(os.getpid(), row['start_ticks'] + 1, signal.SIGTERM))


if __name__ == '__main__':
    unittest.main()
