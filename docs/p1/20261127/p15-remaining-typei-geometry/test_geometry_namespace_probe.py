"""Only new namespace-repair and historical-failure binding boundaries."""
from pathlib import Path
from types import SimpleNamespace
import importlib.util
import json
import tempfile
import unittest
from unittest.mock import patch
HERE = Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('repaired_geometry_probe', HERE/'probe_geometry.py')
probe=importlib.util.module_from_spec(spec); spec.loader.exec_module(probe)
class NewRepairBoundaries(unittest.TestCase):
    def test_only_exact_notation_repair_is_accepted(self):
        old=(HERE/'P1OriginalSingletonRemainingTypeIGeometry.AK.failed.lean').read_bytes()
        new=(HERE/'P1OriginalSingletonRemainingTypeIGeometry.lean').read_bytes()
        probe.require_corrected_source(old,new)
        for a,b in [(old,old),(old,new+b'\n'),(new,new)]:
            with self.subTest(old_bytes=len(a),new_bytes=len(b)), self.assertRaises(RuntimeError):
                probe.require_corrected_source(a,b)
    def test_old_canonical_allowed_only_before_no_output_probe(self):
        slots={str(i):None for i in range(21)}
        probe.require_fresh_slot(probe.ORIGINAL_SOURCE_FP,slots,[])
        with self.assertRaises(RuntimeError):
            probe.require_fresh_slot({'bytes':1,'sha256':'different'},slots,[])
    def test_original_failed_probe_not_relabelled(self):
        actual=json.loads((HERE/'AK_FAILED_GEOMETRY_PROBE.json').read_bytes())['result']
        actual.pop('result_path',None)
        with tempfile.TemporaryDirectory() as d:
            root=Path(d); path=root/probe.AK/'runs/attempt-00000/ACTUAL_GEOMETRY_PROBE_RESULT.json'
            path.parent.mkdir(parents=True)
            raw=(json.dumps(actual,indent=2,sort_keys=True)+'\n').encode()
            self.assertEqual(probe.raw_fp(raw),probe.FAILED_PROBE_FP)
            path.write_bytes(raw)
            base=SimpleNamespace(fp=lambda p:probe.raw_fp(Path(p).read_bytes()))
            c=SimpleNamespace(readers={'ag':SimpleNamespace(tree_inventory=lambda p:{'saved-tree':str(p)})})
            with patch.object(probe,'PROBE_ROOT',root):
                result=probe.failed_probe_snapshot(base,c)
                self.assertEqual(result['result']['sha256'],probe.FAILED_PROBE_FP['sha256'])
                actual['probe_passed']=True
                path.write_text(json.dumps(actual))
                with self.assertRaisesRegex(RuntimeError,'failed probe receipt differs'):
                    probe.failed_probe_snapshot(base,c)
if __name__=='__main__': unittest.main(verbosity=2)
