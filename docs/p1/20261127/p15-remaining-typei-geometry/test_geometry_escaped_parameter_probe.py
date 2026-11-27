"""New escaped-argument and second failed-run preservation boundaries."""
from pathlib import Path
from types import SimpleNamespace
import importlib.util,json,tempfile,unittest
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('geometry_v3',HERE/'probe_geometry.py')
probe=importlib.util.module_from_spec(spec);spec.loader.exec_module(probe)
class NewEscapedParameterBoundaries(unittest.TestCase):
 def test_exact_two_source_edits_without_statement_changes(self):
  original=(HERE/'P1OriginalSingletonRemainingTypeIGeometry.AK.failed.lean').read_bytes()
  previous=(HERE/'P1OriginalSingletonRemainingTypeIGeometry.AL.failed.lean').read_bytes()
  source=(HERE/'P1OriginalSingletonRemainingTypeIGeometry.lean').read_bytes()
  probe.require_corrected_source(original,source)
  self.assertEqual(source.replace('(«R» := R cj)'.encode(),b'(R := R cj)'),previous)
  for invalid in (original,previous,source+b'\n'):
   with self.subTest(bytes=len(invalid)),self.assertRaises(RuntimeError):
    probe.require_corrected_source(original,invalid)
 def test_second_failure_identity_remains_failed_and_bound_to_AL(self):
  raw=(HERE/'AL_FAILED_GEOMETRY_RESULT.json').read_bytes()
  self.assertEqual(probe.raw_fp(raw),probe.SECOND_FAILED_PROBE_FP)
  with tempfile.TemporaryDirectory() as d:
   root=Path(d);p=root/probe.AL/'runs/attempt-00000/ACTUAL_GEOMETRY_PROBE_RESULT.json'
   p.parent.mkdir(parents=True);p.write_bytes(raw)
   base=SimpleNamespace(fp=lambda p:probe.raw_fp(Path(p).read_bytes()))
   c=SimpleNamespace(readers={'ag':SimpleNamespace(tree_inventory=lambda p:{'tree':str(p)})})
   with patch.object(probe,'PROBE_ROOT',root):
    probe.second_failed_probe_snapshot(base,c)
    changed=json.loads(raw);changed['source_origin']['commit']=probe.AK;p.write_text(json.dumps(changed))
    with self.assertRaisesRegex(RuntimeError,'receipt differs'):
     probe.second_failed_probe_snapshot(base,c)
    spoofed=SimpleNamespace(fp=lambda p:probe.SECOND_FAILED_PROBE_FP)
    with self.assertRaisesRegex(RuntimeError,'identity or result differs'):
     probe.second_failed_probe_snapshot(spoofed,c)
if __name__=='__main__':unittest.main(verbosity=2)
