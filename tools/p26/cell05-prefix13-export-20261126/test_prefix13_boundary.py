#!/usr/bin/env python3
"""Synthetic partial-index boundary checks; no Lean or actual proof acceptance."""
from pathlib import Path
import copy
import json
import sys
import unittest

sys.dont_write_bytecode = True
import export_prefix13 as P

HERE = Path(__file__).absolute().parent
FROZEN = HERE.parent / 'cell05-connections14-run-20261126/releases/v1' / P.TOOL
sys.path.insert(0, str(FROZEN))
import receipt_checks as R


class PrefixBoundary(unittest.TestCase):
    def setUp(self):
        self.context = {'targets': json.loads((FROZEN / 'CONNECTIONS14_VERIFIER.json').read_bytes())['targets']}
        self.reusable = {}
        records = []
        for ordinal, module in enumerate(P.MODULES):
            obj = {'path': str(P.STAGE / 'objects' / (module.replace('.', '/') + '.olean')),
                   'bytes': ordinal + 1, 'sha256': str(ordinal).zfill(64)}
            for mode in P.MODES:
                if ordinal == 13:
                    self.reusable[module, mode] = None
                    continue
                attempt = P.PILOT if ordinal == 0 else P.CONTINUATION
                identity = {'path': str(P.STAGE / 'verification' / attempt / module.split('.')[-1] / (mode + '-accepted.json')),
                            'bytes': 1, 'sha256': '0' * 64}
                item = {'accepted': identity, 'result': {'object': obj}}
                self.reusable[module, mode] = item
                records.append({'module': module, 'mode': mode, 'accepted': identity,
                                'disposition': 'reused' if ordinal == 0 else 'executed'})
        self.stopped = {'status': 'stopped', 'failed_result': {'synthetic': True}, 'records': records,
                        'newly_executed_steps': 37, 'reused_steps': 3}
        self.pilot = {'status': 'stopped', 'reason': 'new_step_budget', 'accepted_steps': 3,
                      'accepted_targets': 1, 'newly_executed_steps': 3, 'reused_steps': 0,
                      'whole_geometry_decoded': False, 'P2_6_complete': False,
                      'records': [{**row, 'disposition': 'executed'} for row in records[:3]]}

    def test_39_acceptances_with_37_raw_new_commands(self):
        self.assertEqual(R.require_accepted_prefix(self.context, self.reusable), 39)
        steps, objects = P.check_indexes(self.context, self.reusable, self.pilot, self.stopped)
        self.assertEqual((len(steps), len(objects)), (39, 13))

    def test_failure_command_is_neither_lost_nor_counted_as_acceptance(self):
        for wrong in (36, 39, 40):
            stopped = {**self.stopped, 'newly_executed_steps': wrong}
            with self.subTest(raw_newly=wrong), self.assertRaises(ValueError):
                P.check_indexes(self.context, self.reusable, self.pilot, stopped)

    def test_thirteen_target_reconstructed_context_is_rejected(self):
        context = {'targets': self.context['targets'][:13]}
        with self.assertRaises(ValueError):
            P.check_indexes(context, self.reusable, self.pilot, self.stopped)

    def test_missing_middle_receipt_cannot_be_skipped(self):
        reusable = dict(self.reusable)
        reusable[P.MODULES[7], 'kernel'] = None
        with self.assertRaises(ValueError):
            R.require_accepted_prefix(self.context, reusable)

    def test_shape_acceptance_cannot_be_hidden_in_prefix_export(self):
        reusable = dict(self.reusable)
        reusable[P.MODULES[13], 'normal'] = self.reusable[P.MODULES[0], 'normal']
        with self.assertRaises(ValueError):
            P.check_indexes(self.context, reusable, self.pilot, self.stopped)

    def test_pilot_replacement_and_three_mode_object_disagreement_rejected(self):
        pilot = copy.deepcopy(self.pilot)
        pilot['records'][0]['accepted']['sha256'] = '1' * 64
        with self.assertRaises(ValueError):
            P.check_indexes(self.context, self.reusable, pilot, self.stopped)
        reusable = copy.deepcopy(self.reusable)
        reusable[P.MODULES[12], 'owned']['result']['object'] = {'path': 'different', 'bytes': 1, 'sha256': '1' * 64}
        with self.assertRaises(ValueError):
            P.check_indexes(self.context, reusable, self.pilot, self.stopped)


if __name__ == '__main__':
    unittest.main()
