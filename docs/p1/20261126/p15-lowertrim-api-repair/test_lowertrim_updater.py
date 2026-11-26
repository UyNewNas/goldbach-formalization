#!/usr/bin/env python3
"""Focused local updater checks with original helpers; no cloud or Lean execution."""
from pathlib import Path
from types import ModuleType, SimpleNamespace as NS
from unittest.mock import patch
import copy
import hashlib
import json
import os
import tempfile
import unittest

BASE = Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')
DIR = Path('/tmp/p15-lowertrim-repair')
SCRIPT = DIR / 'apply_lowertrim_repair.py'


def load(path, name):
    module = ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


class LowerTrim(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix='lowertrim-updater-test-', dir='/tmp')
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        m = self.m = load(SCRIPT, 'lowertrim_updater')
        m.ROOT, m.PROJECT, m.OLD_ROOT = root/'new', root/'project', root/'old'
        d = load(BASE/'docs/p1/20261125/batch10-resume/resume_batch10.py', 'actual_primitives')
        api = load(BASE/'docs/p1/20261125/batch13-repairs/run_repairs.py', 'actual_api')
        h = load(BASE/api.HELPER, 'actual_installer')
        driver = load(Path('/tmp/p15-entrypoint-ac/run_selected.py'), 'actual_AC_reader')
        reader = load(Path('/tmp/p15-ac-actual/collect_ac_acceptance.py'), 'actual_AC_collector')
        self.assertEqual(m.raw_fp(Path(driver.__file__).read_bytes()), m.DRIVER_FP)
        self.assertEqual(hashlib.sha256((BASE/'docs/p1/20261125/batch13-repairs/run_repairs.py').read_bytes()).hexdigest(), driver.API_SHA)
        for path in (api.HELPER, api.PRIMITIVES):
            self.assertEqual(hashlib.sha256((BASE/path).read_bytes()).hexdigest(), api.PINS[path])
        driver.PROJECT = m.PROJECT
        c = self.c = NS(commit='b'*40, s=NS(d=d, api=api, h=h), driver=driver, reader=reader,
                       before=(BASE/m.SOURCE).read_bytes(), after=(DIR/Path(m.SOURCE).name).read_bytes())
        self.payload = b'exact LowerTrim failed-setup fixture\n'
        m.SETUP_FP = m.raw_fp(self.payload)
        c.identity = {'execution_commit': c.commit, 'script': {'path': m.SCRIPT, **m.raw_fp(SCRIPT.read_bytes())},
            'repair_source_commit': m.AD, 'failed_source_commit': m.AC, 'failed_job': m.FAILED_JOB,
            'module': m.TARGET, 'source_path': m.SOURCE, 'source_before': m.BEFORE, 'source_after': m.AFTER,
            'failed_setup': {'path': m.SETUP, **m.SETUP_FP}, 'published_AD_inputs': m.PINS}
        self.active = m.PROJECT/m.SETUP
        self.active.parent.mkdir(parents=True)
        self.active.write_bytes(self.payload)
        self.source = m.PROJECT/m.SOURCE
        self.source.parent.mkdir(parents=True, exist_ok=True)
        self.source.write_bytes(c.before)
        self.run = m.ROOT/c.commit/'runs/attempt-00000'
        self.run.mkdir(parents=True)
        self.state = NS(artifacts=m.artifact_inventory(c, [m.TARGET]), archives={})
        self.receipt = self.run/'FAILED_SETUP_ARCHIVE.json'
        self.archive = self.run/'failed-artifacts'/m.ARCHIVE_NAME

    def archive_once(self):
        return self.m.archive_setup(self.c, self.state, self.run)

    def test_unbound_AD_holds_before_subprocess(self):
        with patch.object(self.m, 'INPUTS', None), patch.object(self.m.subprocess, 'check_output') as command:
            with self.assertRaises(RuntimeError):
                self.m.load('a'*40)
            command.assert_not_called()

    def test_durable_archive_and_exact_resume(self):
        synced, fsync, unlink = [], os.fsync, Path.unlink
        def sync(fd):
            synced.append(os.readlink('/proc/self/fd/'+str(fd)))
            fsync(fd)
        def remove(path, *args, **kwargs):
            if path == self.active:
                for required in (self.archive, self.receipt, self.run, self.m.ROOT):
                    self.assertIn(str(required), synced)
            return unlink(path, *args, **kwargs)
        with patch.object(os, 'fsync', sync), patch.object(Path, 'unlink', remove):
            result = self.archive_once()
        self.assertFalse(self.active.exists())
        self.assertEqual(self.archive.read_bytes(), self.payload)
        self.state.artifacts = self.m.artifact_inventory(self.c, [self.m.TARGET])
        self.state.archives = self.m.prior_archive(self.c)
        self.assertEqual(result['bindings'], self.state.archives)
        self.assertEqual(self.archive_once()['action'], 'ALREADY_ARCHIVED_AND_ABSENT')

    def test_missing_wrong_identity_and_wrong_basename_rejected(self):
        self.active.unlink()
        with self.assertRaises(RuntimeError):
            self.m.prior_archive(self.c)
        self.active.write_bytes(self.payload)
        self.archive_once()
        original = json.loads(self.receipt.read_bytes())
        for key in original['identity']:
            bad = copy.deepcopy(original)
            bad['identity'][key] = 'changed'
            self.receipt.write_text(json.dumps(bad))
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                self.m.prior_archive(self.c)
        bad = copy.deepcopy(original)
        bad['archive_path'] = str(self.archive.with_name('P5OriginalSharpPrimeSynthesis.setup.json'))
        self.receipt.write_text(json.dumps(bad))
        with self.assertRaises(RuntimeError):
            self.m.prior_archive(self.c)

    def test_interruption_after_unlink_recovers(self):
        sync = self.m.fsync_directory
        def fail(path):
            if path == self.active.parent:
                raise OSError('fixture interruption after unlink')
            sync(path)
        with patch.object(self.m, 'fsync_directory', fail), self.assertRaises(OSError):
            self.archive_once()
        self.state.artifacts = self.m.artifact_inventory(self.c, [self.m.TARGET])
        self.state.archives = self.m.prior_archive(self.c)
        self.assertEqual(self.archive_once()['action'], 'ALREADY_ARCHIVED_AND_ABSENT')

    def test_source_after_and_symlink_hold(self):
        self.m.require_preimage(self.c)
        self.source.write_bytes(self.c.after)
        with self.assertRaises(RuntimeError):
            self.m.require_preimage(self.c)
        other = self.source.with_name('other.lean')
        other.write_bytes(self.c.before)
        self.source.unlink()
        self.source.symlink_to(other)
        with self.assertRaises(RuntimeError):
            self.m.require_preimage(self.c)

    def test_original_AC_preflight_failure_prevents_install(self):
        m, c = self.m, self.c
        self.state.sources, self.state.evidence, self.state.retained, self.state.accepted = {}, {}, {}, {}
        self.state.spec, self.state.context, self.state.git = NS(baseline={}), {}, {}
        def hold(s, commit, selected):
            self.assertEqual((commit, selected), (m.AC, m.REMAINING))
            self.assertFalse(self.active.exists())
            self.assertEqual(self.archive.read_bytes(), self.payload)
            self.assertEqual(self.source.read_bytes(), c.before)
            raise RuntimeError('original AC held')
        with patch.object(c.s.d, 'verify_lane'), patch.object(m, 'prepare', return_value=self.state), \
             patch.object(m, 'unchanged'), patch.object(c.driver, 'preflight', hold), \
             patch.object(c.s.h, 'install_sources') as installer:
            with self.assertRaises(RuntimeError):
                m.apply_repair(c, self.run)
            installer.assert_not_called()

    def test_original_installer_changes_only_LowerTrim(self):
        m, c = self.m, self.c
        other = m.PROJECT/c.s.h.module_path(m.SYNTHESIS)
        other.write_bytes(b'accepted Synthesis fixture\n')
        artifacts = m.artifact_inventory(c, [m.TARGET, m.SYNTHESIS])
        update = {'module': m.TARGET, 'path': m.SOURCE, 'before_sha256': m.BEFORE['sha256'],
                  'after_sha256': m.AFTER['sha256'], 'cloud_source_mutation_required': True}
        rows = c.s.h.install_sources(m.PROJECT, [update], {m.SOURCE: c.after}, self.run/'backups')
        self.assertEqual([r['module'] for r in rows], [m.TARGET])
        self.assertEqual(self.source.read_bytes(), c.after)
        self.assertEqual((self.run/'backups'/m.SOURCE).read_bytes(), c.before)
        self.assertEqual(other.read_bytes(), b'accepted Synthesis fixture\n')
        self.assertEqual(m.artifact_inventory(c, [m.TARGET, m.SYNTHESIS]), artifacts)

    def test_actual_AC_graph_scope_one_splice_and_AD_inputs(self):
        m, c = self.m, self.c
        manifest = json.loads(Path('/tmp/p15-entrypoint-ac/SOURCE_MANIFEST.json').read_bytes())
        graph = {key: row['imports'] for key, row in manifest['project_sources'].items()}
        active, prefix = [c.s.h.closure(graph, group) for group in (m.REMAINING, m.ACCEPTED)]
        self.assertEqual((len(active), len(active)-4, len(prefix), len(prefix)-1), (157, 153, 112, 111))
        self.assertEqual(len(active | set(c.driver.TARGETS)), 160)
        current = (active & set(c.driver.TARGETS)) - set(manifest['previously_accepted_targets'])
        self.assertEqual(current, set(m.ACCEPTED+m.REMAINING))
        self.assertEqual(len(current), 5)
        suppliers = (active & set(manifest['accepted_suppliers'])) | (active & set(manifest['previously_accepted_targets']))
        result = json.loads(Path('/tmp/p15-ac-actual/attempt-00001-RESULT.json').read_bytes())
        self.assertEqual(suppliers, set(result['original_supplier_acceptance_bindings']))
        self.assertEqual(len(suppliers), 26)
        self.assertEqual(c.s.d.compile_order([], m.REMAINING, graph), m.REMAINING)
        repair = json.loads((DIR/'REPAIR_CANDIDATE.json').read_bytes())
        parts, end = [], 0
        for row in repair['splices']:
            self.assertEqual(c.before[row['start']:row['end']], row['before'].encode())
            parts.extend((c.before[end:row['start']], row['after'].encode()))
            end = row['end']
        self.assertEqual(len(repair['splices']), 1)
        self.assertEqual(b''.join(parts)+c.before[end:], c.after)
        self.assertEqual(c.s.h.imports(c.before), c.s.h.imports(c.after))
        self.check_actual_AD_inputs_and_original_collector_bindings()

    def check_actual_AD_inputs_and_original_collector_bindings(self):
        m, c = self.m, self.c
        if m.INPUTS is None:
            self.skipTest('AD has not yet been published and bound')
        local = {m.REPAIR: DIR/'REPAIR_CANDIDATE.json', m.PROBE: DIR/'ACTUAL_LOWERTRIM_PROBE_RESULT.json',
            m.DIAGNOSTICS: Path('/tmp/p15-ac-actual/ACTUAL_AC_METADATA.json'),
            m.READ: Path('/tmp/p15-ac-actual/ACTUAL_AC_ACCEPTANCE_READ.json'),
            m.COLLECTOR: Path('/tmp/p15-ac-actual/collect_ac_acceptance.py'),
            m.PUBLIC_SYNTHESIS: Path('/tmp/p15-ac-actual/SYNTHESIS_AC_PUBLIC_ACCEPTANCE.json')}
        self.assertEqual(set(local), set(m.PINS))
        for key, path in local.items():
            self.assertEqual(m.raw_fp(path.read_bytes()), m.PINS[key], key)
        read = json.loads(local[m.READ].read_bytes())
        repair = json.loads(local[m.REPAIR].read_bytes())
        probe = json.loads(local[m.PROBE].read_bytes())
        self.assertEqual(m.value_fp(c.reader.PINNED), read['frozen_actual_input_binding'])
        self.assertEqual(c.reader.PINNED['runs'][1]['compiler_job'], m.FAILED_JOB)
        self.assertEqual(read['public_summaries']['SYNTHESIS_AC_PUBLIC_ACCEPTANCE'],
                         json.loads(local[m.PUBLIC_SYNTHESIS].read_bytes()))
        self.assertEqual(read['selected_owners_revalidated'], [m.SYNTHESIS])
        self.assertEqual((read['current_read_live_source_count'], read['current_read_preserved_dependency_count']), (112, 111))
        self.assertEqual(set(read['complete_original_AC_AA_Y_W_U_S_Q_evidence_inventory']), {m.AC, m.AA, m.Y, m.W, m.U, m.S, m.Q})
        self.assertEqual(repair['actual_whole_module_probe'], {
            'path': str(Path(probe['candidate']['path']).parent/'ACTUAL_LOWERTRIM_PROBE_RESULT.json'),
            **m.PINS[m.PROBE], 'compiler_job': m.PROBE_JOB, 'exit_code': 0})
        self.assertNotIn('prior_failed_whole_module_probes', repair)
        probe_reader = load(DIR/'probe_lowertrim_repair.py', 'actual_lowertrim_probe')
        self.assertEqual(m.INHERITED_EXTRA_PINS, probe_reader.RETAINED_EXTRA_PINS)
        self.assertEqual(len(m.INHERITED_EXTRA_PINS), 5)
        self.assertEqual(sum('p15-synthesis-api-probe-v1/' in path for path in m.INHERITED_EXTRA_PINS), 3)
        self.assertEqual(m.INPUTS['after'], m.AFTER)
        self.assertEqual(m.raw_fp(c.before), m.BEFORE)
        self.assertEqual(m.raw_fp(c.after), m.AFTER)


if __name__ == '__main__':
    unittest.main(verbosity=2)
