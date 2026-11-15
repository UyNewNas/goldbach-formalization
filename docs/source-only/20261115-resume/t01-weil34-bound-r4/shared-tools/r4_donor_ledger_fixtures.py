"""GitHub-only donor ledger transition fixtures; fake bytes give no proof credit."""
from contextlib import ExitStack,contextmanager
import copy
import hashlib
import os
from pathlib import Path
import re
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch

if os.environ.get('GITHUB_ACTIONS')!='true':
    raise SystemExit('Never execute donor-ledger fixtures locally')

import carrier_originals as co
import qualified_algebra as qa
import qualified_direct as qd
import weil_cache as wc
import weil_proof as wp


class R4DonorLedgerCases(unittest.TestCase):
    def setUp(self):
        temporary=tempfile.TemporaryDirectory(prefix='r4-fake-donor-ledger-')
        self.addCleanup(temporary.cleanup);self.directory=Path(temporary.name)
        self.original=b'FAKE ORIGINAL STREAM ONLY'
        self.digest=hashlib.sha256(self.original).hexdigest()
        self.inputs=self.directory/'original-inputs'/'r3';self.inputs.mkdir(parents=True)
        self.old_path='/home/runner/work/_temp/weil34-evidence/cache-processes/fake-stream.stdout'
        self.pin=dict(original_path=self.old_path,bytes=len(self.original),sha256=self.digest,
                      donor_input_relative_path='raw/objects/'+self.digest)
        self.row=dict(original_path=self.old_path,resolved_path=self.old_path,
                      bytes=len(self.original),sha256=self.digest,payload='objects/'+self.digest)
        self.donor=self.inputs.parent/'raw/objects'/self.digest
        self.donor.parent.mkdir(parents=True);self.donor.write_bytes(self.original)
        self.target=self.inputs/'raw/objects'/self.digest
        self.setup=self.directory/'Fake.setup.json';self.setup.write_bytes(b'{}')
        self.contexts=[]

    @contextmanager
    def actual_transition(self):
        # Only upstream stock/history are fixture seams. The actual qd.admit,
        # qd.validate/full equality, R3Direct original_file/restore composition,
        # donor method, checked bytes and ordered records are never mocked.
        original_class=qd.R3Direct;receipts={}
        session=SimpleNamespace(binding=dict(fake_unit_metadata_only=True),require_fixtures=lambda:None)
        def emit(name,value):receipts[name]=dict(binding=session.binding,**copy.deepcopy(value))
        session.emit=emit;session.receipt=lambda name:copy.deepcopy(receipts[name])
        setup_input=dict(files=[qa.file_record(self.setup)],setup={},setup_path=str(self.setup))
        def context_factory(actual_session,module):
            context=object.__new__(original_class);context.session=actual_session;context.module=module
            context.inputs=self.inputs;context.cp=dict(files={self.old_path:copy.deepcopy(self.row)})
            context.used_payloads={};context.body_sources={};context.current_authenticated_streams=[]
            authority=object.__new__(co.CarrierOriginals);authority.root=self.inputs;authority.used={};authority.original_files={}
            authority.authority=dict(deduplicated_authentic_prior_R1_streams=[copy.deepcopy(self.pin)])
            context._genuine_carrier=authority
            context.light_json=lambda member:copy.deepcopy(setup_input)
            self.contexts.append(context);return context
        def upstream_history(context,standard,restore=False):
            context.original_file(self.old_path)
            return dict(authentic_original_payloads=list(context.used_payloads.values()),
                        fixture_only_not_proof_or_cache_credit=True)
        with ExitStack() as stack:
            stack.enter_context(patch.object(qd,'installed',return_value=None))
            stack.enter_context(patch.object(qd,'selection',return_value={}))
            stack.enter_context(patch.object(wc.WeilSession,'stock_qualification_inputs',return_value={}))
            stack.enter_context(patch.object(qa,'admit',return_value=None))
            stack.enter_context(patch.object(qa,'validate',return_value=dict(fake_R1_upstream_only=True)))
            stack.enter_context(patch.object(qa.PriorDirect,'restore_and_compare',new=upstream_history))
            stack.enter_context(patch.object(wp,'setup_value',return_value=({},self.setup,{})))
            stack.enter_context(patch.object(qd,'R3Direct',new=context_factory))
            yield session

    def test_donor_first_admit_then_fresh_validate_full_dict_equal(self):
        self.assertFalse(self.target.exists())
        with self.actual_transition() as session:
            qd.admit(session)
            self.assertTrue(self.target.is_file())
            value=qd.validate(session,{})
            self.assertEqual(session.receipt('WEIL_R4_DIRECT_QUALIFICATION.json'),dict(binding=session.binding,**value))
            for module in qd.PROTECTED[1:]:
                self.assertEqual([x['path'] for x in value['modules'][module]['authentic_original_payloads']],
                                 [str(self.donor),str(self.target)])
            self.assertEqual(len(self.contexts),28)
            self.assertTrue(all(list(c.carrier().original_files)==[str(self.donor),str(self.target)] for c in self.contexts))

    def test_donor_changed_after_admit_rejected_before_full_equality(self):
        with self.actual_transition() as session:
            qd.admit(session)
            self.donor.write_bytes(bytes([self.original[0]^1])+self.original[1:])
            with self.assertRaisesRegex(ValueError,'^Changed payload: '+re.escape(str(self.donor))+'$'):
                qd.validate(session,{})

    def test_donor_missing_after_admit_rejected_with_existing_target(self):
        with self.actual_transition() as session:
            qd.admit(session);self.assertTrue(self.target.is_file());self.donor.unlink()
            with self.assertRaisesRegex(ValueError,'^Missing/nonregular payload: '+re.escape(str(self.donor))+'$'):
                qd.validate(session,{})

    def test_existing_target_changed_after_admit_rejected(self):
        with self.actual_transition() as session:
            qd.admit(session)
            self.target.write_bytes(bytes([self.original[0]^1])+self.original[1:])
            with self.assertRaisesRegex(ValueError,'^Changed payload: '+re.escape(str(self.target))+'$'):
                qd.validate(session,{})
