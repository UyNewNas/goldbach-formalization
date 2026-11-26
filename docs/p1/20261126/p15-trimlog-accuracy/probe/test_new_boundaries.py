#!/usr/bin/env python3
"""Only the four new draft/current-runtime boundaries; no old suite or compiler."""
from pathlib import Path
from types import ModuleType, SimpleNamespace
from unittest.mock import patch
import copy
import json
import tempfile
import unittest

DIR = Path('/tmp/p15-trimlog-probe')
SCRIPT = DIR / 'probe_trimlog.py'

def load():
    m = ModuleType('trimlog_boundary_test'); m.__file__ = str(SCRIPT)
    exec(compile(SCRIPT.read_bytes(), str(SCRIPT), 'exec'), m.__dict__)
    return m

def spec(path, selected):
    manifest = json.loads(Path(path).read_bytes())
    graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    active, todo = set(), list(selected)
    while todo:
        module = todo.pop()
        if module not in active:
            active.add(module); todo.extend(graph[module])
    return SimpleNamespace(manifest=manifest, graph=graph, active=active,
        dependency_pins={m: None for m in active-set(selected)},
        sources={m: row['sha256'] for m, row in manifest['project_sources'].items()})

class NewTrimLogBoundaries(unittest.TestCase):
    def setUp(self):
        self.m = load()
        self.ae = spec('/tmp/p15-entrypoint-ae/SOURCE_MANIFEST.json', self.m.ACCEPTED)
        self.ag = spec('/tmp/p15-entrypoint-ag/SOURCE_MANIFEST.json', self.m.CURRENT_ACCEPTED)

    def test_wrong_AD_candidate_holds_before_any_subprocess(self):
        with tempfile.TemporaryDirectory(prefix='trimlog-boundary-', dir='/tmp') as directory:
            candidate = Path(directory)/'wrong.lean'
            raw = (DIR/'P1OriginalSingletonAtlasTrimLogAccuracy.lean').read_bytes()
            candidate.write_bytes(raw + b'\n')
            with patch.object(self.m.subprocess, 'check_output') as command:
                with self.assertRaises(RuntimeError):
                    self.m.run(candidate)
                command.assert_not_called()

    def test_current_AG_postimage_accepted_old_AE_preimage_rejected(self):
        observed = {m: {k: row[k] for k in ('bytes', 'sha256')}
                    for m, row in self.ag.manifest['project_sources'].items()}
        self.m.require_current_sources(observed, self.ag.manifest)
        self.assertNotEqual(observed[self.m.RESERVEBRANCHES]['sha256'], self.ae.sources[self.m.RESERVEBRANCHES])
        old = self.ae.manifest['project_sources'][self.m.RESERVEBRANCHES]
        observed[self.m.RESERVEBRANCHES] = {k: old[k] for k in ('bytes', 'sha256')}
        with self.assertRaises(RuntimeError):
            self.m.require_current_sources(observed, self.ag.manifest)

    def test_new_canonical_source_and_project_outputs_must_stay_absent(self):
        absent = {'fixture-slot-'+str(i): None for i in range(21)}
        self.m.require_uninstalled_draft(None, absent)
        with self.assertRaises(RuntimeError):
            self.m.require_uninstalled_draft(self.m.CANDIDATE_FP, absent)
        present = {**absent, 'fixture-slot-0': {'bytes': 1, 'sha256': '0'*64}}
        with self.assertRaises(RuntimeError):
            self.m.require_uninstalled_draft(None, present)

    def test_separate_actual_scopes_allow_only_outside_prefix_source_delta(self):
        self.assertEqual((len(self.ae.active), len(self.ag.active), len(self.ae.active | self.ag.active)), (153, 144, 157))
        self.assertNotIn(self.m.RESERVEBRANCHES, self.ae.active)
        self.m.require_runtime_scopes(self.ae, self.ag)
        changed_prefix = copy.deepcopy(self.ag)
        changed_prefix.sources[self.m.ATLASTRIM] = '0'*64
        with self.assertRaises(RuntimeError):
            self.m.require_runtime_scopes(self.ae, changed_prefix)
        registered = copy.deepcopy(self.ag)
        registered.graph[self.m.DRAFT_MODULE] = [self.m.ATLASTRIM]
        with self.assertRaises(RuntimeError):
            self.m.require_runtime_scopes(self.ae, registered)

if __name__ == '__main__':
    unittest.main(verbosity=2)
