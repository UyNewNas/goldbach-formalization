"""Regression: required revisions must be enforced even with Python -O."""
import json
import subprocess
import sys
import unittest
from pathlib import Path

from build_p34_fourier_k import MATHLIB

VALID = {
    str(MATHLIB): 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
    '/workspace/goldbach-p3/.lake/packages/goldbach': '09b97db5764ade1246bfb77206baa1b124760958',
    '/workspace/goldbach-p3/.lake/packages/LeanArchitect': '78dd66840d3efe8c824c699fc03381cec817c271',
    str(MATHLIB / '.lake/packages/example'): 'locked-transitive-revision',
}
LOCKED = [{'name': 'example', 'rev': 'locked-transitive-revision'}]


class RequiredPins(unittest.TestCase):
    def run_validation(self, pins, optimized):
        code = ('import json,sys; from build_p34_fourier_k import validate_package_pins; '
                'validate_package_pins(json.loads(sys.argv[1]), json.loads(sys.argv[2]))')
        return subprocess.run([sys.executable, *(['-O'] if optimized else []), '-B', '-c', code,
            json.dumps(pins), json.dumps(LOCKED)], cwd=Path(__file__).parent,
            capture_output=True, text=True)

    def test_valid_revisions_work_in_both_modes(self):
        for optimized in (False, True):
            result = self.run_validation(VALID, optimized)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_each_required_revision_is_rejected_in_both_modes(self):
        for key in VALID:
            for optimized in (False, True):
                with self.subTest(package=key, optimized=optimized):
                    pins = {**VALID, key: 'wrong-revision'}
                    result = self.run_validation(pins, optimized)
                    self.assertNotEqual(result.returncode, 0,
                        'Wrong dependency revision accepted with optimized=' + str(optimized))


if __name__ == '__main__':
    unittest.main()
