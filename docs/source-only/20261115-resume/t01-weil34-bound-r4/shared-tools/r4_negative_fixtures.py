"""Additional real R4 gate negatives. GitHub fixture phase only; never local."""
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import re
from types import SimpleNamespace
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import zipfile

if os.environ.get('GITHUB_ACTIONS') != 'true':
    raise SystemExit('Never execute R4 fixtures locally')

import qualified_algebra as qa
import qualified_direct as qd
import weil_retention as wr
from cache_preexec_policy import classify


class R4ProtectionCases(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='r4-fake-negative-metadata-')
        self.addCleanup(temporary.cleanup); self.root = Path(temporary.name)
        self.project = self.root/'project'; self.project.mkdir()
        self.logs = self.root/'logs'; self.logs.mkdir()

    def put(self,path,content=b'FAKE ONLY NO PROOF CREDIT'):
        path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(content)
        return qa.file_record(path)

    def selected(self):
        return copy.deepcopy(qa.read(qa.BUNDLE/'direct-reuse/R4_DIRECT_SELECTION.json'))

    def test_r4_not_ready_selection_denied(self):
        value = self.selected(); value['reuseReady'] = False
        bundle = self.root/'bundle'; path = bundle/'direct-reuse/R4_DIRECT_SELECTION.json'
        path.parent.mkdir(parents=True); path.write_text(json.dumps(value))
        binding = dict(source_commit=qd.SOURCE,run_id='FAKE_DISTINCT_R4_RUN')
        control = dict(driver_base=qd.R3_HEAD,driver_branch='ci/weil34-26a6-20261115',
                       multi_direct_selection_sha256=qa.sha(path))
        with patch.object(qd,'BUNDLE',bundle),patch.object(qd,'bind',return_value=(control,binding)),\
             self.assertRaisesRegex(ValueError,'^R4 HOLD: raw physical inputs and full protocol review are not ready$'):
            qd.selection(SimpleNamespace(binding=binding))

    def test_r4_failed_ClassGhost_cannot_be_protected(self):
        value = self.selected(); value['protected_modules'][-1] = qd.FAILED
        with self.assertRaisesRegex(ValueError,'^R4 exact15 protected and19 fresh partition changed or failed ClassGhost promoted$'):
            qd.check_partition(value)

    def test_r4_Algebra_carrier_cannot_become_R3_producer(self):
        value = self.selected(); value['producers']['R3']['modules'].insert(0,qa.MODULE)
        with self.assertRaisesRegex(ValueError,'^R4 genuine producer ownership changed; R3 Algebra is only a carrier$'):
            qd.check_partition(value)

    def test_r4_duplicate_R3_selection_rejected(self):
        value = self.selected(); value['r3_modules'][1] = value['r3_modules'][0]
        with self.assertRaisesRegex(ValueError,'^R4 duplicate, missing or reordered R3 module selection$'):
            qd.check_partition(value)

    def test_r4_changed_protected_source_rejected(self):
        prior = dict(module='Fake',installation_path='Fake.lean',bytes=1,sha256='a'*64,
                     git_blob='b'*40,imports=['Init'],source_module_mode=True)
        current = copy.deepcopy(prior); current['sha256'] = 'c'*64
        with self.assertRaisesRegex(ValueError,'^R4 protected source/header/import/actual producer identity changed$'):
            qd.check_source(current,prior,dict(bytes=1,sha256='a'*64))

    def test_r4_wrong_artifact_producer_rejected(self):
        anchor = dict(artifact=1,artifactBytes=1,githubWholeArtifactDigest='a'*64,run=int(qd.R3_RUN),head_sha=qd.R3_HEAD)
        metadata = dict(expired=False,id=1,size_in_bytes=1,digest='sha256:'+'a'*64,
                        workflow_run=dict(id=43643644264,head_sha=qa.PRIOR_HEAD))
        with self.assertRaisesRegex(ValueError,'^R4 original R3 artifact id/run/head/size/digest changed$'):
            qd.check_artifact_producer(metadata,anchor)

    def test_r4_duplicate_acquisition_destination_rejected(self):
        index = dict(schema='weil34-r4-finite-physical-acquisition-v1',
            status='READY_EXACT_RANGES_AND_RAW_IDENTITIES_REVIEWED',large_whole_archives_permitted=False,
            light=dict(bytes=53784325,sha256=qd.R3_LIGHT,bounded_small_archive_only=True,input_relative_path='same'),
            frozen_receipts=[dict(input_relative_path='same')],artifacts=[])
        with self.assertRaisesRegex(ValueError,'^R4 duplicate physical acquisition destination$'):
            qd.check_acquisition_layout(index)

    def test_r4_whole_tar_member_acquisition_rejected(self):
        index = dict(schema='weil34-r4-finite-physical-acquisition-v1',
            status='READY_EXACT_RANGES_AND_RAW_IDENTITIES_REVIEWED',large_whole_archives_permitted=False,
            light=dict(bytes=53784325,sha256=qd.R3_LIGHT,bounded_small_archive_only=True,input_relative_path='light.zip'),
            frozen_receipts=[],artifacts=[dict(members=[dict(member='weil-source-object-inputs.tar.gz',input_relative_path='forbidden')])])
        with self.assertRaisesRegex(ValueError,'^R4 whole CP/proof/tar/container member acquisition denied$'):
            qd.check_acquisition_layout(index)

    def test_r4_dependency_order_rejected(self):
        order = list(qd.PROTECTED)+['Fake.'+str(i) for i in range(19)]
        rows = {name:dict(imports=[]) for name in order}
        rows[qd.PROTECTED[1]]['imports'] = [qd.PROTECTED[2]]
        with self.assertRaisesRegex(ValueError,'^R4 dependency was not installed before its consumer$'):
            qd.check_dependency_order(order,rows)

    def test_r4_missing_sixth_facet_rejected(self):
        row = self.selected()['r3_modules'][0]; row['prior_output_facets'] = row['prior_output_facets'][:-1]
        with self.assertRaisesRegex(ValueError,'^R4 exact six original modern physical outputs required$'):
            qd.check_six_outputs(row['module'],row)

    def test_r4_missing_actual_input_file_rejected(self):
        setup = self.put(self.project/'Fake.setup.json',b'{}')
        private = self.put(self.project/'Fake.olean.private')
        value = dict(files=[setup],setup={},setup_path=setup['path'])
        with self.assertRaisesRegex(ValueError,'^R4 original full actual input file set/setup differs from current resolved physical inputs$'):
            qd.check_input_file_set(value,{},Path(setup['path']),{private['path']:private})

    def test_r4_nonempty_historical_stream_cannot_be_synthesized(self):
        context = object.__new__(qd.R3Direct); context.inputs = self.root/'originals'; context.inputs.mkdir()
        context.used_payloads = {}; context.body_sources = {}; context.current_authenticated_streams = []
        path = '/home/runner/work/_temp/weil34-evidence/cache-processes/runtime-audit.stdout'
        raw = b'AUTHENTIC NONEMPTY BYTES NOT AVAILABLE'
        context.cp = dict(files={path:dict(bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),payload='objects/missing')})
        light = self.root/'tiny.zip'
        with zipfile.ZipFile(light,'w') as archive: archive.writestr('authentic-empty',b'')
        with zipfile.ZipFile(light) as archive:
            context.light = archive
            with self.assertRaisesRegex(ValueError,'^Missing/nonregular payload: '): context.original_file(path)

    def test_r4_all15_source_outputs_hash_setup_trace_native_paths_denied(self):
        policy = dict(admitted_commands=[dict(source=dict(path=str(self.project/Path(*n.split('.')).with_suffix('.lean'))))
            for n in qd.PROTECTED],deny_exact_paths=[],deny_roots=[])
        protected = qd.protect_policy(policy,self.project)
        self.assertEqual(protected['admitted_commands'],[])
        for name in qd.PROTECTED:
            for path in qd.protected_denial_paths(name,self.project):
                with self.subTest(module=name,path=path),self.assertRaisesRegex(RuntimeError,'^Protected cache source/output: '+re.escape(str(Path(path).resolve()))+'$'):
                    classify('lean',[path],self.project,protected)

    def census(self):
        return {name:0 if name in qd.PROTECTED else 1 for name in [*qd.PROTECTED,*['Fake.'+str(n) for n in range(19)]]}

    def test_r4_second_producer_protected_compile_rejected(self):
        counts = self.census(); counts[qd.PROTECTED[-1]] = 1
        with self.assertRaisesRegex(ValueError,'^R4 protected source compiler event denied$'): qd.validate_census(counts,True)

    def test_r4_missing_necessary_fresh_compile_rejected(self):
        counts = self.census(); counts['Fake.18'] = 0
        with self.assertRaisesRegex(ValueError,'^R4 missing necessary fresh source compiler event$'): qd.validate_census(counts,True)

    def test_r4_duplicate_fresh_compile_rejected(self):
        counts = self.census(); counts['Fake.18'] = 2
        with self.assertRaisesRegex(ValueError,'^R4 repeated fresh source compiler event denied$'): qd.validate_census(counts,True)

    def capture_case(self,omit_role):
        contexts = {}
        rows = []
        for index,name in enumerate(qd.PROTECTED):
            def part(role):
                row = self.put(self.project/(str(index)+'-'+role),role.encode()); rows.append(row); return row
            value = dict(current_source=part('source'),current_setup=part('setup'),
                current_all_prior_actual_inputs=[part('actual-input')],
                current_five_facets=[part('output'+str(n)) for n in range(5)],
                current_additional_ilean=part('ilean'),authentic_original_payloads=[part('original-evidence')])
            contexts[name] = value
        target = contexts[qd.PROTECTED[-1]]
        missing = dict(source=target['current_source'],setup=target['current_setup'],
            input=target['current_all_prior_actual_inputs'][0],output=target['current_five_facets'][3],
            prior=target['authentic_original_payloads'][0])[omit_role]
        for name in ['T01Audit.lean','T01_PROVENANCE.json','LEANPOOL_LICENSE','lakefile.toml','lake-manifest.json','lean-toolchain']:
            rows.append(self.put(self.project/name))
        path = self.logs/'direct-inputs/T01Audit.json'; path.parent.mkdir()
        path.write_text(json.dumps(dict(source=qa.file_record(self.project/'T01Audit.lean'),files=[])))
        rows.append(qa.file_record(path))
        archive = self.logs/'weil-source-object-inputs.tar.gz'; captured = []
        with tarfile.open(archive,'w:gz') as tar:
            for index,row in enumerate(rows):
                if row['path'] == missing['path']: continue
                content = Path(row['path']).read_bytes(); member = 'fake/'+str(index)
                info = tarfile.TarInfo(member); info.size = len(content); tar.addfile(info,io.BytesIO(content))
                captured.append(dict(row,archive_member=member))
        value = dict(archive=archive.name,integrity_errors=[],archive_sha256=qa.sha(archive),files=captured)
        session = SimpleNamespace(project=self.project,logs=self.logs)
        self.assertTrue(Path(missing['path']).is_file())
        with patch.object(wr,'data',return_value=dict(compile_order=[qa.MODULE])),\
             patch.object(qa,'validate',return_value=contexts[qa.MODULE]),\
             patch.object(qd,'validate',return_value=dict(modules=contexts)),\
             self.assertRaisesRegex(ValueError,'^R4 protected current source/setup/all actual inputs/six outputs/original evidence omitted from complete raw capture$'):
            wr.validate_capture(session,value,dict(complete_source_private_closure={}))

    def test_r4_second_producer_source_missing_from_tar_rejected(self):
        self.capture_case('source')

    def test_r4_second_producer_setup_missing_from_tar_rejected(self):
        self.capture_case('setup')

    def test_r4_second_producer_actual_input_missing_from_tar_rejected(self):
        self.capture_case('input')

    def test_r4_second_producer_output_missing_from_tar_rejected(self):
        self.capture_case('output')

    def test_r4_second_producer_original_evidence_missing_from_tar_rejected(self):
        self.capture_case('prior')
