"""GitHub-only negative tests of actual R3 gates; fake bytes earn no credit."""
import copy
import hashlib
import io
import json
import os
from pathlib import Path
from types import SimpleNamespace
import tarfile
import tempfile
import unittest
from unittest.mock import patch

if os.environ.get('GITHUB_ACTIONS') != 'true':
    raise SystemExit('Never execute R3 fixtures locally')

import qualified_algebra as qa
import weil_cache as wc
import weil_retention as wr
from cache_preexec_policy import classify


def record(path):
    raw = path.read_bytes()
    return dict(path=str(path),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())


class R3ProtectionCases(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix='r3-fake-negative-metadata-')
        self.addCleanup(directory.cleanup); self.root = Path(directory.name)
        self.project = self.root/'project'; self.project.mkdir()
        self.logs = self.root/'logs'; self.logs.mkdir()

    def put(self,path,raw=b'FAKE METADATA ONLY'):
        path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(raw)
        return record(path)

    def selected_case(self):
        selected = copy.deepcopy(qa.read(qa.BUNDLE/'direct-reuse/PRIOR_DIRECT_SELECTION.json'))
        selected['status'] = 'READY_EXACT_RAW_PAYLOADS_INDEPENDENTLY_REVIEWED'; selected['reuseReady'] = True
        bundle = self.root/'fake-bundle'; path = bundle/'direct-reuse/PRIOR_DIRECT_SELECTION.json'
        path.parent.mkdir(parents=True)
        binding = dict(fake_unit_data=True,source_commit=qa.CONSUMER_SOURCE,run_id='FAKE_DIFFERENT_RUN')
        session = SimpleNamespace(binding=binding)
        return selected,bundle,path,binding,session

    def call_selection(self,selected,bundle,path,binding,session):
        path.write_text(json.dumps(selected))
        with patch.object(qa,'BUNDLE',bundle), patch.object(qa,'bind',return_value=(dict(direct_reuse_selection_sha256=qa.sha(path)),binding)):
            return qa.selection(session)

    def test_r3_not_ready_selection_denied(self):
        selected,bundle,path,binding,session = self.selected_case(); selected['reuseReady'] = False
        with self.assertRaisesRegex(ValueError,'HOLD: actual raw input and whole protocol review are not ready'): self.call_selection(selected,bundle,path,binding,session)

    def test_r3_wrong_prior_producer_denied(self):
        selected,bundle,path,binding,session = self.selected_case(); selected['prior_binding']['driver_commit'] = '0'*40
        with self.assertRaisesRegex(ValueError,'Wrong genuine prior producer'): self.call_selection(selected,bundle,path,binding,session)

    def test_r3_wrong_original_body_denied(self):
        context = object.__new__(qa.PriorDirect); context.inputs = self.root/'originals'; context.inputs.mkdir()
        body = self.put(context.inputs/'raw/objects/original'); body['payload'] = 'objects/original'
        context.cp = dict(files={'/original/fake.olean':body}); context.used_payloads = {}
        (context.inputs/'raw/objects/original').write_bytes(b'CHANGED BODY')
        with self.assertRaises(ValueError): context.original_file('/original/fake.olean')

    def test_r3_protected_source_and_all_six_outputs_denied(self):
        source = str(self.project/Path(*qa.MODULE.split('.')).with_suffix('.lean'))
        policy = dict(admitted_commands=[dict(source=dict(path=source))],deny_exact_paths=[],deny_roots=[])
        protected = qa.protect_policy(policy,self.project)
        self.assertEqual(protected['admitted_commands'],[])
        stem = str(self.project/'.lake/build/lib/lean'/Path(*qa.MODULE.split('.')))
        for path in [source,*[stem+s for s in ['.olean','.olean.server','.olean.private','.ir.sig','.ir','.ilean']]]:
            with self.subTest(path=path), self.assertRaises(RuntimeError): classify('lean',[path],self.project,protected)

    def census(self,protected=0,missing=False,duplicate=False):
        rows = [dict(module=qa.MODULE,installation_path='Protected.lean')]
        rows += [dict(module='Fake.Fresh'+str(n),installation_path='Fresh'+str(n)+'.lean') for n in range(33)]
        session = object.__new__(wc.WeilSession); session.project = self.project; session.logs = self.logs
        session.policy_audit = lambda: None
        events = []
        for index,row in enumerate(rows):
            count = protected if index == 0 else 0 if missing and index == 1 else 2 if duplicate and index == 1 else 1
            for _ in range(count): events.append(dict(classification='EXACT_CURRENT_WEIL34_SOURCE',physical_inputs=[dict(path=str(self.project/row['installation_path'])),{}]))
        (self.logs/'CACHE_PREEXEC_EVENTS.jsonl').write_text(''.join(json.dumps(e)+'\n' for e in events))
        with patch.object(wc,'data',return_value=dict(source_rows=rows)):
            return wc.WeilSession.compile_census(session,True)

    def test_r3_protected_compile_census_denied(self):
        with self.assertRaises(ValueError): self.census(protected=1)

    def test_r3_missing_fresh_compile_census_denied(self):
        with self.assertRaises(ValueError): self.census(missing=True)

    def test_r3_repeated_fresh_compile_census_denied(self):
        with self.assertRaises(ValueError): self.census(duplicate=True)

    def protected_output_case(self):
        context = object.__new__(qa.PriorDirect)
        context.session = SimpleNamespace(project=self.project,logs=self.logs)
        context.inputs = self.root/'originals'; context.inputs.mkdir()
        context.used_payloads = {}; context.cp = dict(files={})
        source_path = self.project/Path(*qa.MODULE.split('.')).with_suffix('.lean')
        source = self.put(source_path)
        stem = self.project/'.lake/build/lib/lean'/Path(*qa.MODULE.split('.'))
        facets = [self.put(Path(str(stem)+s),s.encode()) for s in ['.olean','.olean.server','.olean.private','.ir.sig','.ir']]
        ilean = self.put(Path(str(stem)+'.ilean'),b'FAKE ILEAN')
        setup = self.put(self.project/'.lake/build/ir'/Path(*qa.MODULE.split('.')).with_suffix('.setup.json'),b'{}')
        for row in [source,*facets,ilean,setup]:
            payload = 'objects/'+row['sha256']; self.put(context.inputs/'raw'/payload,Path(row['path']).read_bytes())
            context.cp['files'][row['path']] = dict(row,payload=payload)
        context.selected = dict(original_source=source,prior_output_facets=facets,additional_ilean=ilean,prior_setup_identity=setup,
            hash_sidecars=[dict(path=r['path']+'.hash',present=False) for r in [*facets,ilean]],Lake_trace=dict(path=str(stem)+'.trace'))
        blob = hashlib.sha1(b'blob '+str(source['bytes']).encode()+b'\0'+source_path.read_bytes()).hexdigest()
        identity = dict(modern=True,facets=facets,source=source,source_provenance=dict(git_blob=blob))
        context.validate_history = lambda standard:(dict(output_identity=identity),dict(files=[],source=source))
        row = dict(module=qa.MODULE,bytes=source['bytes'],sha256=source['sha256'],git_blob=blob)
        return context,dict(source_rows=[row]),facets,ilean

    def test_r3_missing_current_ir_signature_denied(self):
        context,scope,facets,ilean = self.protected_output_case(); Path(facets[3]['path']).unlink()
        with patch.object(qa,'data',return_value=scope), self.assertRaises(ValueError): context.restore_and_compare({})

    def test_r3_missing_current_ilean_denied(self):
        context,scope,facets,ilean = self.protected_output_case(); Path(ilean['path']).unlink()
        with patch.object(qa,'data',return_value=scope), self.assertRaises(ValueError): context.restore_and_compare({})

    def test_r3_changed_current_private_physical_input_denied(self):
        source = self.put(self.project/'Fake.lean'); private = self.put(self.project/'Fake.olean.private')
        receipt = dict(source=source,files=[private]); Path(private['path']).write_bytes(b'CHANGED PRIVATE')
        with self.assertRaises(ValueError): qa.check_current_prior_files(receipt)

    def test_r3_changed_current_private_closure_denied(self):
        old = dict(source_private_closure={'Fake':dict(owner='original')},importArts={},search_path_value={})
        current = copy.deepcopy(old); current['source_private_closure']['Fake']['owner'] = 'changed'
        with self.assertRaises(ValueError): qa.compare_standard_inputs(old,current)

    def test_r3_changed_current_ABI_bytes_denied(self):
        runtime = {str(self.root/('runtime'+str(i))):self.put(self.root/('runtime'+str(i)))['sha256'] for i in range(11)}
        state = dict(shadow=str(self.root/'shadow'),tools=[],runtime_sha256=runtime)
        abi = []
        for i in range(8):
            path = self.root/('abi'+str(i)); row = self.put(path)
            abi.append(dict(original_path=str(path),resolved_path=str(path.resolve()),bytes=row['bytes'],sha256=row['sha256']))
        cp = dict(native_and_toolchain_library_ABI_receipts=abi,packages=[])
        Path(abi[0]['original_path']).write_bytes(b'CHANGED ABI')
        with self.assertRaises(ValueError): qa.verify_current_runtime_abi(state,copy.deepcopy(state),cp,copy.deepcopy(cp))

    def acquisition_case(self):
        root = self.root/'acquired'; root.mkdir()
        row = self.put(root/'original.bin'); expected = [dict(input_relative_path='original.bin',bytes=row['bytes'],sha256=row['sha256'])]
        index = self.root/'index.json'; index.write_text('{}')
        acquired = dict(status='EXACT_ORIGINAL_BYTES_ONLY_NOT_REUSE_OR_PROOF_ACCEPTANCE',index_sha256=qa.sha(index),source_compiler_events=0,
            large_whole_archives_downloaded=False,files=[row])
        return root,index,expected,acquired

    def test_r3_acquired_member_identity_denied(self):
        root,index,expected,acquired = self.acquisition_case(); acquired['files'][0]['path'] = str(root/'different.bin')
        with self.assertRaises(ValueError): qa.validate_acquired_files(acquired,index,expected,root)

    def test_r3_acquired_member_length_denied(self):
        root,index,expected,acquired = self.acquisition_case(); acquired['files'][0]['bytes'] += 1
        with self.assertRaises(ValueError): qa.validate_acquired_files(acquired,index,expected,root)

    def test_r3_acquired_member_sha_denied(self):
        root,index,expected,acquired = self.acquisition_case(); acquired['files'][0]['sha256'] = '0'*64
        with self.assertRaises(ValueError): qa.validate_acquired_files(acquired,index,expected,root)

    def test_r3_acquisition_artifact_producer_denied(self):
        anchor = dict(artifact=1,run=43643644264,artifactBytes=10,githubWholeArtifactDigest='a'*64,head_sha=qa.PRIOR_HEAD)
        metadata = dict(id=1,size_in_bytes=10,digest='sha256:'+'a'*64,expired=False,workflow_run=dict(id=43643644264,head_sha='0'*40))
        with self.assertRaises(ValueError): qa.check_acquisition_producer(metadata,anchor)

    def test_r3_current_protected_setup_omitted_from_tar_denied(self):
        source = self.put(self.project/'Protected.lean')
        setup = self.put(self.project/'Algebra.setup.json',b'CURRENT LIVE SETUP')
        old_setup = self.put(self.root/'prior-original/old-setup',b'OLD ORIGINAL SETUP')
        private = self.put(self.project/'private-input.olean.private')
        facets = [self.put(self.project/('Protected'+s),s.encode()) for s in ['.olean','.olean.server','.olean.private','.ir.sig','.ir']]
        ilean = self.put(self.project/'Protected.ilean')
        protected = dict(authentic_original_payloads=[old_setup],current_source=source,current_setup=setup,
            current_all_prior_actual_inputs=[private,setup],current_five_facets=facets,current_additional_ilean=ilean)
        inventory = dict(complete_source_private_closure={'Fake':dict(identity=dict(source=source,facets=facets))})
        more = [self.put(self.project/n) for n in ['T01Audit.lean','T01_PROVENANCE.json','LEANPOOL_LICENSE','lakefile.toml','lake-manifest.json','lean-toolchain']]
        receipt_path = self.logs/'direct-inputs/T01Audit.json'; receipt_path.parent.mkdir()
        receipt_path.write_text(json.dumps(dict(source=more[0],files=[]))); more.append(record(receipt_path))
        # Everything required except the current setup is physically in this tar.
        # The old raw setup and live current setup both still exist.
        rows = [source,old_setup,private,*facets,ilean,*more]
        archive = self.logs/'weil-source-object-inputs.tar.gz'
        capture_rows = []
        with tarfile.open(archive,'w:gz') as tar:
            for n,row in enumerate(rows):
                raw = Path(row['path']).read_bytes(); name = 'fake/'+str(n)
                info = tarfile.TarInfo(name); info.size = len(raw); tar.addfile(info,io.BytesIO(raw))
                capture_rows.append(dict(row,archive_member=name))
        capture = dict(archive=archive.name,integrity_errors=[],archive_sha256=qa.sha(archive),files=capture_rows)
        session = SimpleNamespace(project=self.project,logs=self.logs)
        self.assertTrue(Path(setup['path']).is_file()); self.assertTrue(Path(old_setup['path']).is_file())
        with patch.object(wr,'data',return_value=dict(compile_order=[qa.MODULE])),patch.object(qa,'validate',return_value=protected),self.assertRaisesRegex(ValueError,'omitted from complete raw capture'):
            wr.validate_capture(session,capture,inventory)
