import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class WorkflowLifecycleTest(unittest.TestCase):
    def test_required_final_job_fails_closed_and_keeps_all_gates(self):
        text = (ROOT / '.github/workflows/lean.yml').read_text()
        final = text.split('  lean:\n', 1)[1]
        self.assertIn('needs: compile-shard-4', final)
        self.assertIn('always() && !cancelled()', final.split('runs-on:', 1)[0])
        self.assertIn('test "$STAGING_RESULT" = success', final)
        self.assertIn('test "$CACHE_EXACT" = true', final)
        self.assertIn('test "$CACHE_MATCHED" = "$REQUIRED_CACHE"', final)
        for outcome in ['RUNTIME', 'BUILD', 'LEANCHECKER', 'AXIOM_AUDIT',
                        'ROUND3_TYPES', 'ROUND4_TARGETS', 'ROUND4_TYPES', 'ROUND6_TYPES']:
            self.assertIn(f'test "${outcome}_OUTCOME" = success', final)
        self.assertIn('full_source_inventory.py --targets', final)
        self.assertIn('lake build "${targets[@]}"', final)
        for index in range(1, 5):
            job = text.split(f'  compile-shard-{index}:\n', 1)[1].split('\n  ', 1)[0]
            # Check the complete job region without interpreting YAML booleans.
            start = text.index(f'  compile-shard-{index}:\n')
            end = text.find('\n  compile-shard-', start + 1)
            if end < 0:
                end = text.index('\n  lean:', start)
            job = text[start:end]
            self.assertIn(f'shard-index: {index}', job)
            if index > 1:
                self.assertIn(f'needs: compile-shard-{index - 1}', job)

    def test_internal_timeout_retains_failed_stage_receipt(self):
        text = (ROOT / '.github/workflows/full-source-shard.yml').read_text()
        start = text.index("<<'BASH'\n") + len("<<'BASH'\n")
        end = text.index('\n          BASH', start)
        script = '\n'.join(line[10:] for line in text[start:end].splitlines()) + '\n'
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'lean-verification-logs').mkdir()
            stage = root / 'run-stage'
            stage.write_text(script)
            env = dict(os.environ, RUNNER_TEMP=tmp,
                       GITHUB_OUTPUT=str(root / 'output'),
                       GITHUB_STEP_SUMMARY=str(root / 'summary'))
            result = subprocess.run(['bash', str(stage), 'test-timeout', 'timeout',
                                     '--signal=TERM', '--kill-after=0.1s', '0.2s',
                                     'bash', '-c', 'sleep 30'], env=env,
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 124, result.stdout + result.stderr)
            log = (root / 'lean-verification-logs/test-timeout.log').read_text()
            timing = (root / 'lean-verification-logs/test-timeout.timing.tsv').read_text()
            self.assertIn('finished=', log)
            self.assertIn('exit_code=124', log)
            self.assertTrue(timing.rstrip().endswith('\t124'))


if __name__ == '__main__':
    unittest.main()
