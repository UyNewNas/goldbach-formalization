"""Receipt tests with synthetic audited data; no compiler/cache/network access."""
import copy
import json
import unittest

from full_source_build_report import make_report
from full_source_shards import make_manifest, select_targets
from full_source_shard_receipt import GUARD, PINS, canonical, create_receipt, sha, verify_receipts
from test_full_source_shards import fixture


def encoded(value):
    return json.dumps(value, indent=2).encode()


class ReceiptTests(unittest.TestCase):
    def setUp(self):
        self.source = fixture()
        self.manifest = make_manifest(self.source)
        self.pins = {name: 'c' * 64 for name in (*PINS, GUARD)}
        self.pins['toolchain_pin'] = 'leanprover/lean4:v4.33.0-rc1'
        self.state = {'guard_sha256': self.pins[GUARD], 'lean_memory_mib': 6144, 'lean_elab_async': False,
                      'environment': {'P0_LEAN_ELAB_ASYNC': 'false', 'CI_LEAN_MEMORY_MIB': '6144',
                                      'ELAN_TOOLCHAIN': self.pins['toolchain_pin']},
                      'input_sha256': {'/repo/' + name: self.pins[name] for name in PINS},
                      'realbin': '/toolchain/bin',
                      'runtime_sha256': {'/toolchain/bin/' + name: 'd' * 64 for name in
                                         ('lean', 'lake', 'leanchecker', 'leanir', 'clang', 'leanc', 'llvm-ar', 'leantar')}}
        self.state_raw = encoded(self.state)
        self.audit = {'status': 'PASS_RUNTIME_GUARD_ONLY', 'compiler_commands': 4, 'source_commands': 2,
                      'probe': True, 'lean_memory_mib': 6144, 'lean_elab_async': False,
                      'state_sha256': sha(self.state_raw), 'command_log_sha256': 'e' * 64}

    def create(self, index, report=None, audit=None, state_raw=None):
        selected = select_targets(self.manifest, index)
        report = report if report is not None else make_report(self.source, b'compile log', 0, selected=selected)
        return create_receipt(self.source, self.manifest, encoded(report), encoded(audit or self.audit),
                              state_raw or self.state_raw, self.pins, f'cache-{index}', index, 4)

    def receipts(self):
        return {f'shard-{index}.json': self.create(index) for index in range(1, 5)}

    def test_complete_receipts_only_assert_staging_provenance(self):
        result = verify_receipts(self.source, self.manifest, self.receipts(), self.pins, 4, self.state)
        self.assertEqual(result['verified_shards'], 4)
        self.assertEqual(result['status'], 'PASS_STAGING_CACHE_PROVENANCE_ONLY')
        self.assertFalse(result['all_production_targets_passed'])
        self.assertTrue(result['final_authoritative_build_still_required'])

    def test_missing_and_extra_receipts_rejected(self):
        receipts = self.receipts()
        receipts.pop('shard-3.json')
        with self.assertRaisesRegex(ValueError, 'missing'):
            verify_receipts(self.source, self.manifest, receipts, self.pins, 4, self.state)
        receipts = self.receipts()
        receipts['shard-5.json'] = receipts['shard-1.json']
        with self.assertRaises(ValueError):
            verify_receipts(self.source, self.manifest, receipts, self.pins, 4, self.state)

    def test_tampered_receipt_and_wrong_head_rejected_even_rehashed(self):
        for field, value in [('source_head', 'f' * 40), ('cache_key', ''), ('index', 2)]:
            receipts = self.receipts()
            envelope = receipts['shard-1.json']
            envelope['receipt'][field] = value
            envelope['receipt_sha256'] = sha(canonical(envelope['receipt']).encode())
            with self.subTest(field=field), self.assertRaises(ValueError):
                verify_receipts(self.source, self.manifest, receipts, self.pins, 4, self.state)
        receipts = self.receipts()
        receipts['shard-1.json']['receipt']['source_files'][0]['sha256'] = 'f' * 64
        with self.assertRaisesRegex(ValueError, 'tampered'):
            verify_receipts(self.source, self.manifest, receipts, self.pins, 4, self.state)

    def test_partial_failed_or_wrong_scope_build_rejected(self):
        selected = select_targets(self.manifest, 1)
        for report in [make_report(self.source, b'', 1, selected=selected),
                       make_report(self.source, b'', 0, selected=[selected[0]]),
                       make_report(self.source, b'', 0)]:
            with self.subTest(report=report), self.assertRaises(ValueError):
                self.create(1, report=report)
        report = make_report(self.source, b'', 0, selected=selected)
        report['all_production_targets_passed'] = True
        with self.assertRaisesRegex(ValueError, 'partial scope'):
            self.create(1, report=report)

    def test_audit_and_runtime_requirements(self):
        for field, value in [('status', 'FAIL'), ('source_commands', 0), ('probe', False),
                             ('lean_elab_async', True), ('lean_memory_mib', 4096), ('state_sha256', 'f' * 64)]:
            audit = dict(self.audit)
            audit[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.create(1, audit=audit)
        for field, value in [('guard_sha256', 'f' * 64), ('runtime_sha256', {}), ('lean_elab_async', True)]:
            state = copy.deepcopy(self.state)
            state[field] = value
            state_raw = encoded(state)
            audit = dict(self.audit, state_sha256=sha(state_raw))
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.create(1, audit=audit, state_raw=state_raw)

    def test_final_job_runtime_must_match_cached_shards(self):
        receipts = self.receipts()
        current = copy.deepcopy(self.state)
        current['runtime_sha256']['/toolchain/bin/lean'] = 'f' * 64
        with self.assertRaisesRegex(ValueError, 'current final-job runtime'):
            verify_receipts(self.source, self.manifest, receipts, self.pins, 4, current)
        current = copy.deepcopy(self.state)
        current['realbin'] = '/different-runner/pinned/bin'
        current['runtime_sha256'] = {path.replace('/toolchain/bin', current['realbin']): digest
                                    for path, digest in current['runtime_sha256'].items()}
        result = verify_receipts(self.source, self.manifest, receipts, self.pins, 4, current)
        self.assertEqual(result['verified_shards'], 4)
        current['runtime_sha256'].pop('/different-runner/pinned/bin/leanchecker')
        with self.assertRaisesRegex(ValueError, 'incomplete'):
            verify_receipts(self.source, self.manifest, receipts, self.pins, 4, current)

    def test_nonproduction_receipt_success_and_false_outcomes_rejected(self):
        self.source['files'].append({'path': 'verification/Historical.lean', 'module': None,
                                     'exists': True, 'sha256': 'f' * 64, 'bytes': 20,
                                     'disposition': 'historical_verification_evidence_do_not_compile_automatically'})
        self.manifest = make_manifest(self.source)
        result = verify_receipts(self.source, self.manifest, self.receipts(), self.pins, 4, self.state)
        self.assertEqual(result['verified_shards'], 4)
        selected = select_targets(self.manifest, 1)
        for field, value in [('run_status', 'compiled'), ('compiled_by_this_build', True),
                             ('build_reason', 'production_library_compile_independent_target')]:
            report = make_report(self.source, b'compile log', 0, selected=selected)
            report['files'][-1][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'nonproduction'):
                self.create(1, report=report)

    def test_current_guard_source_and_partition_changes_rejected(self):
        receipts = self.receipts()
        pins = dict(self.pins, **{GUARD: 'f' * 64})
        with self.assertRaises(ValueError):
            verify_receipts(self.source, self.manifest, receipts, pins, 4, self.state)
        source = copy.deepcopy(self.source)
        source['files'][0]['sha256'] = 'f' * 64
        with self.assertRaises(ValueError):
            verify_receipts(source, make_manifest(source), receipts, self.pins, 4, self.state)
        manifest = copy.deepcopy(self.manifest)
        manifest['shards'][0]['targets'].pop()
        with self.assertRaises(ValueError):
            verify_receipts(self.source, manifest, receipts, self.pins, 4, self.state)


if __name__ == '__main__':
    unittest.main()
