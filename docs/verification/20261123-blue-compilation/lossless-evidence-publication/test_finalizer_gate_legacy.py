"""Isolated read-only gate fixtures; no publisher main, Lean, or live records."""
import ast,copy,hashlib,json,tempfile,unittest
from pathlib import Path
SCRIPT=Path('/workspace/p1-complete-proof/lossless-large-evidence-publication/publish_verified_member_batch.candidate.py')
# Load only real imports/functions until the publisher has a safe main guard.
ns={};tree=ast.parse(SCRIPT.read_text());safe=ast.Module(body=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom,ast.FunctionDef))],type_ignores=[]);exec(compile(safe,str(SCRIPT),'exec'),ns)
def digest(b):return hashlib.sha256(b).hexdigest()
def write(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
def rec(p,name):b=(p/name).read_bytes();return{'path':name,'bytes':len(b),'sha256':digest(b)}
CAUSE='Finalizer stdout appended the exact FINAL_RELEASE.json bytes after its publication manifest captured an empty log. Proof/source/validation logs are unaffected.'
IMPACT='Only this auxiliary stdout manifest entry; normal/kernel/audit logs, selected sources, proof outputs and full-owned acceptance evidence are unaffected.'
class PublisherGate(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.p=Path(self.tmp.name);(self.p/'M').mkdir();(self.p/'M/candidate.lean').write_bytes(b'theorem original : True := by trivial\n');self.empty={'path':'finalizer.log','bytes':0,'sha256':digest(b'')};self.manifest={'files':[self.empty.copy(),rec(self.p,'M/candidate.lean')]};write(self.p/'PUBLICATION_FILES.json',self.manifest);self.pubsha=digest((self.p/'PUBLICATION_FILES.json').read_bytes());write(self.p/'FINAL_RELEASE.json',{'status':'FINAL_RELEASE','publication_files_sha256':self.pubsha});(self.p/'finalizer.log').write_bytes((self.p/'FINAL_RELEASE.json').read_bytes());self.review={'status':'PASS_SIX_MODULE_ACCEPTANCE_CHAIN_WITH_MINOR_METADATA_ADDENDUM','findings':[{'severity':'minor_metadata','path':'PUBLICATION_FILES.json / finalizer.log','impact':IMPACT}]};self.binding={'schema':'late_finalizer_stdout_manifest_binding_v1','original_publication_manifest_sha256':self.pubsha,'original_empty_finalizer_entry':self.empty.copy(),'actual_finalizer_log':rec(self.p,'finalizer.log'),'exact_stdout_equals_final_release':{**rec(self.p,'FINAL_RELEASE.json'),'byte_for_byte_equal':True},'original_records_unchanged_by_review':True};self.save()
 def save(self):
  write(self.p/'LATE_FINALIZER_LOG_BINDING.json',self.binding);write(self.p/'INDEPENDENT_REVIEW.json',self.review);write(self.p/'FINAL_REVIEW_NEW_FILES_MANIFEST.json',{'original_publication_manifest_sha256':self.pubsha,'old_records_unchanged':True,'files':[rec(self.p,'LATE_FINALIZER_LOG_BINDING.json'),rec(self.p,'INDEPENDENT_REVIEW.json')]})
 def run_gate(self):
  fn=ns.get('prepare_publication_files');self.assertTrue(callable(fn),'strict importable finalizer gate not implemented');before={str(p.relative_to(self.p)):p.read_bytes()for p in self.p.rglob('*')if p.is_file()};m=copy.deepcopy(self.manifest)
  try:return fn(self.p,m,self.review)
  finally:
   self.assertEqual(m,self.manifest,'gate mutated input manifest');self.assertEqual(before,{str(p.relative_to(self.p)):p.read_bytes()for p in self.p.rglob('*')if p.is_file()},'gate wrote fixture files')
 def reject(self):
  with self.assertRaises((AssertionError,ValueError,KeyError,FileNotFoundError)):self.run_gate()
 def legacy(self):
  actual=rec(self.p,'finalizer.log');final=rec(self.p,'FINAL_RELEASE.json');self.binding={'schema':'immutable_late_finalizer_stdout_log_binding_v1','original_publication':{**rec(self.p,'PUBLICATION_FILES.json'),'path':str(self.p/'PUBLICATION_FILES.json')},'original_manifest_entry':self.empty.copy(),'actual_finalizer_log':{**actual,'path':str(self.p/'finalizer.log')},'actual_FINAL_RELEASE':{**final,'path':str(self.p/'FINAL_RELEASE.json')},'actual_finalizer_log_equals_FINAL_RELEASE_bytes':True,'cause':CAUSE,'old_records_unchanged':True,'original_manifest_and_log_not_rewritten':True};self.review={'status':'PASS_EXISTING_NORMAL_KERNEL_FULL_OWNED_CHAIN_WITH_LATE_FINALIZER_BINDING','findings':[{'severity':'minor_metadata','file':'finalizer.log','original_manifest_entry':self.empty.copy(),'current_actual':self.binding['actual_finalizer_log'].copy(),'cause':CAUSE,'actual_log_equals_FINAL_RELEASE_original_bytes':True}]};self.save()
 def third(self):
  self.binding={'schema':'immutable_late_finalizer_stdout_binding_v1','original_publication_manifest':{**rec(self.p,'PUBLICATION_FILES.json'),'path':str(self.p/'PUBLICATION_FILES.json')},'original_final_release':{**rec(self.p,'FINAL_RELEASE.json'),'path':str(self.p/'FINAL_RELEASE.json')},'publication_entry_count':2,'other_original_entries_rehashed_and_exact':1,'only_mismatch':{'original_manifest_entry':self.empty.copy(),'current_actual_file':{**rec(self.p,'finalizer.log'),'path':str(self.p/'finalizer.log')}},'finalizer_stdout_bytes_exactly_equal_final_release':True,'permitted_publication_exception_exact_path':'finalizer.log','old_manifest_log_release_result_source_objects_unchanged':True};self.save()
 def test_third_explicit_schema_accepts_same_single_stdout(self):
  self.third()
  try:files,exception=self.run_gate()
  except ValueError as e:self.fail('third precise format not implemented: '+str(e))
  self.assertEqual(files,[rec(self.p,'finalizer.log'),self.manifest['files'][1]]);self.assertEqual(exception['binding_schema'],'immutable_late_finalizer_stdout_binding_v1')
 def test_third_rejects_wrong_publication_path(self):self.third();self.binding['original_publication_manifest']['path']=str(self.p/'OTHER.json');self.save();self.reject()
 def test_third_rejects_wrong_release_digest(self):self.third();self.binding['original_final_release']['sha256']='0'*64;self.save();self.reject()
 def test_third_rejects_wrong_old_entry(self):self.third();self.binding['only_mismatch']['original_manifest_entry']['path']='M/candidate.lean';self.save();self.reject()
 def test_third_rejects_wrong_current_actual_path(self):self.third();self.binding['only_mismatch']['current_actual_file']['path']=str(self.p/'OTHER.log');self.save();self.reject()
 def test_third_rejects_false_unchanged_flag(self):self.third();self.binding['old_manifest_log_release_result_source_objects_unchanged']=False;self.save();self.reject()
 def test_third_rejects_wrong_permitted_exception_path(self):self.third();self.binding['permitted_publication_exception_exact_path']='M/candidate.lean';self.save();self.reject()
 def test_third_rejects_source_impact_finding(self):self.third();self.review['findings'][0]['source_or_validation_impact']=True;self.save();self.reject()
 def test_third_rejects_wrong_other_entry_count(self):self.third();self.binding['other_original_entries_rehashed_and_exact']=2;self.save();self.reject()
 def test_third_rejects_changed_stdout(self):self.third();(self.p/'finalizer.log').write_bytes(b'changed');self.reject()
 def test_canonical_accepts_only_late_stdout_and_preserves_other_record(self):
  files,exception=self.run_gate();self.assertEqual(files,[rec(self.p,'finalizer.log'),self.manifest['files'][1]]);self.assertEqual(exception['original_manifest_entry'],self.empty);self.assertEqual(exception['actual_finalizer_log'],rec(self.p,'finalizer.log'))
 def test_immutable_explicit_mapping_accepts_same_stdout(self):
  self.legacy();files,exception=self.run_gate();self.assertEqual(files,[rec(self.p,'finalizer.log'),self.manifest['files'][1]]);self.assertEqual(exception['binding_schema'],'immutable_late_finalizer_stdout_log_binding_v1')
 def test_unchanged_manifest_needs_no_exception(self):
  (self.p/'finalizer.log').write_bytes(b'');self.review={'status':'PASS_INDEPENDENT_REVIEW','findings':[]};files,exception=self.run_gate();self.assertEqual(files,self.manifest['files']);self.assertIsNone(exception)
 def test_rejects_unknown_schema(self):self.binding['schema']='arbitrary';self.save();self.reject()
 def test_rejects_missing_binding(self):(self.p/'LATE_FINALIZER_LOG_BINDING.json').unlink();self.reject()
 def test_rejects_missing_final_review_manifest(self):(self.p/'FINAL_REVIEW_NEW_FILES_MANIFEST.json').unlink();self.reject()
 def test_rejects_unbound_late_record(self):
  x=json.loads((self.p/'FINAL_REVIEW_NEW_FILES_MANIFEST.json').read_bytes());x['files']=[z for z in x['files']if z['path']!='LATE_FINALIZER_LOG_BINDING.json'];write(self.p/'FINAL_REVIEW_NEW_FILES_MANIFEST.json',x);self.reject()
 def test_rejects_changed_binding_after_hash(self):self.binding['explanation']='late';write(self.p/'LATE_FINALIZER_LOG_BINDING.json',self.binding);self.reject()
 def test_rejects_wrong_publication_sha(self):self.binding['original_publication_manifest_sha256']='0'*64;self.save();self.reject()
 def test_rejects_nonempty_original_entry(self):self.binding['original_empty_finalizer_entry']['bytes']=1;self.save();self.reject()
 def test_rejects_wrong_actual_file(self):self.binding['actual_finalizer_log']['path']='M/candidate.lean';self.save();self.reject()
 def test_rejects_changed_stdout(self):(self.p/'finalizer.log').write_bytes(b'changed');self.reject()
 def test_rejects_changed_FINAL_even_when_stdout_digest_still_bound(self):(self.p/'FINAL_RELEASE.json').write_bytes(b'other');self.reject()
 def test_rejects_source_drift(self):(self.p/'M/candidate.lean').write_bytes(b'weakened');self.reject()
 def test_rejects_extra_source_finding(self):self.review['findings'].append({'severity':'source_math','path':'M/candidate.lean'});self.save();self.reject()
 def test_rejects_minor_finding_for_another_file(self):self.review['findings'][0]['path']='M/candidate.lean';self.save();self.reject()
 def test_rejects_claim_of_source_impact(self):self.review['findings'][0]['source_or_validation_impact']=True;self.save();self.reject()
 def test_rejects_hidden_math_blocker(self):self.review['blocking_source_or_math_findings']=['gap'];self.save();self.reject()
 def test_rejects_changed_review_after_hash(self):self.review['status']='PASS_CHANGED';write(self.p/'INDEPENDENT_REVIEW.json',self.review);self.reject()
 def test_rejects_duplicate_original_finalizer(self):self.manifest['files'].append(self.empty.copy());self.reject()
 def test_immutable_rejects_wrong_publication_absolute_path(self):self.legacy();self.binding['original_publication']['path']=str(self.p/'OTHER.json');self.save();self.reject()
 def test_immutable_rejects_wrong_finalizer_absolute_path(self):self.legacy();self.binding['actual_finalizer_log']['path']=str(self.p/'OTHER.log');self.save();self.reject()
 def test_immutable_rejects_wrong_FINAL_absolute_path(self):self.legacy();self.binding['actual_FINAL_RELEASE']['path']=str(self.p/'OTHER.json');self.save();self.reject()
 def test_immutable_rejects_missing_unmodified_flag(self):self.legacy();self.binding['original_manifest_and_log_not_rewritten']=False;self.save();self.reject()
 def test_immutable_rejects_wrong_finding_file(self):self.legacy();self.review['findings'][0]['file']='M/candidate.lean';self.save();self.reject()
 def test_immutable_rejects_mismatched_current_record(self):self.legacy();self.review['findings'][0]['current_actual']['bytes']=1;self.save();self.reject()
 def test_immutable_rejects_non_equivalent_impact_cause(self):self.legacy();self.binding['cause']=self.review['findings'][0]['cause']='Source proofs may be affected';self.save();self.reject()
 def test_immutable_rejects_false_stdout_equivalence(self):self.legacy();self.review['findings'][0]['actual_log_equals_FINAL_RELEASE_original_bytes']=False;self.save();self.reject()
if __name__=='__main__':unittest.main()
