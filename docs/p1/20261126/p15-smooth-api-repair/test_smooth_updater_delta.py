#!/usr/bin/env python3
"""Provisional, local Smooth updater delta review; V/W publication is unbound."""
from pathlib import Path
from types import ModuleType,SimpleNamespace
from unittest.mock import patch
import ast,copy,hashlib,json,re,sys,tempfile,unittest
sys.dont_write_bytecode=True
BASE=Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126');DIR=Path('/tmp/p15-smooth-repair')
old=(BASE/'apply_word_repair.py').read_text();tree=ast.parse(old)
assert hashlib.sha256(old.encode()).hexdigest()=='e7058d2214b2119f1985cf21a073cc87d66603a930d7c49f29cf6e8705d390f4'
names=['need','raw_fp','value_fp','pin','git_file','file_fp','source_inventory','artifact_inventory','normal_path','require_preimage','archive_binding','prior_archive','fsync_directory','archive_setup']
fns={n.name:ast.get_source_segment(old,n) for n in tree.body if isinstance(n,ast.FunctionDef)}
helpers='\n\n'.join(fns[n] for n in names).replace('S/T/U/script-bound','U/V/W/script-bound')
helpers=re.sub(r'\bS\b','U',helpers).replace('WordDictionary','SmoothLicence')
header=(DIR/'smooth_updater_header.py.txt').read_text();body=(DIR/'smooth_updater_body.py.txt').read_text()
repair=json.loads((DIR/'REPAIR_CANDIDATE.json').read_text())
m=ModuleType('isolated_unbound_smooth_updater');m.__file__='unbound-local-fixture.py'
exec(compile(header+'\nV="UNBOUND_TEST_ONLY"\nAFTER='+repr(repair['after'])+'\nPINS={}\n'+helpers+'\n'+body,m.__file__,'exec'),m.__dict__)
reader=ModuleType('frozen_U_collector');reader.__file__=str(BASE/'collect_u_acceptance.py')
exec(compile((BASE/'collect_u_acceptance.py').read_bytes(),reader.__file__,'exec'),reader.__dict__)
manifest=json.loads(Path('/tmp/p15-entrypoint-u/SOURCE_MANIFEST.json').read_text());graph={k:v['imports'] for k,v in manifest['project_sources'].items()}
read=json.loads(Path('/tmp/p15-u-actual/ACTUAL_U_ACCEPTANCE_READ.json').read_text())
metadata=json.loads(Path('/tmp/p15-u-actual/ACTUAL_U_METADATA.json').read_text())
publics={m.READ:read,m.PUBLIC_WORD:json.loads(Path('/tmp/p15-u-actual/WORD_U_PUBLIC_ACCEPTANCE.json').read_text()),m.PUBLIC_ALLGROUP:json.loads(Path('/tmp/p15-u-actual/ALLGROUP_U_PUBLIC_ACCEPTANCE.json').read_text())}
results=[json.loads(Path('/tmp/p15-u-actual/attempt-%05d-RESULT.json'%i).read_text()) for i in (0,1)]
bindings={owner:results[index]['acceptance_bindings'][owner] for owner,index in ((m.WORD,0),(m.ALLGROUP,1))}
def closure(roots):
 seen=set();todo=list(roots)
 while todo:
  x=todo.pop()
  if x not in seen:seen.add(x);todo.extend(graph[x])
 return seen
accepted=closure(m.ACCEPTED);active=closure(m.REMAINING);watch=active|set(manifest['targets'])

def retained_fixture():
 # Execute the actual three new prepare assignments, not a copied filter.
 prepare=next(n for n in ast.parse(body).body if isinstance(n,ast.FunctionDef) and n.name=='prepare')
 nodes=[n for n in prepare.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in {'mutable','extras','retained'} for t in n.targets)]
 failure=metadata['failures'][m.TARGET]
 ns={**m.__dict__,'c':SimpleNamespace(reader=reader),'expected_normal':Path(failure['normal_metadata']['path']),
     'failure':failure,'normal_log':{'path':failure['normal_command']['log'],'bytes':failure['normal_command']['log_bytes'],'sha256':failure['normal_command']['log_sha256']},
     'candidate':Path('/tmp/isolated-smooth-probe/candidate.lean'),'log':Path('/tmp/isolated-smooth-probe/probe.log'),
     'probe':{'log':{'bytes':1,'sha256':'1'*64}},'PINS':{m.PROBE:{'bytes':1,'sha256':'2'*64}},
     'original_context':{'retained_original_evidence':{}},'archives':{'/tmp/isolated-archive/receipt.json':{'bytes':1,'sha256':'3'*64}}}
 exec(compile(ast.Module(body=nodes,type_ignores=[]),'actual-prepare-retained-assignments','exec'),ns)
 return ns['mutable'],ns['retained']

class Delta(unittest.TestCase):
 def test_actual_U_scope_and_next_order(self):
  self.assertEqual((len(accepted),len(accepted)-2,len(active),len(active)-8,len(watch)),(139,137,157,149,160))
  self.assertNotIn(m.TARGET,accepted)
  initial=(active&set(manifest['targets']))-set(manifest['previously_accepted_targets'])
  self.assertEqual(initial,set(m.ACCEPTED+m.REMAINING));self.assertEqual(len(initial),10)
  self.assertEqual(len(results[1]['original_supplier_acceptance_bindings']),21)
  self.assertEqual(results[1]['targets'][2:],m.REMAINING)
 def test_real_five_splices_and_imports(self):
  before=(Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')/m.SOURCE).read_bytes()
  after=(DIR/'P1OriginalSingletonSmoothLicence.lean').read_bytes()
  self.assertEqual(m.raw_fp(before),m.BEFORE);self.assertEqual(m.raw_fp(after),m.AFTER)
  pieces=[];end=0
  for s in repair['splices']:
   self.assertEqual(before[s['start']:s['end']],s['before'].encode());self.assertLessEqual(end,s['start'])
   pieces.extend((before[end:s['start']],s['after'].encode()));end=s['end']
  self.assertEqual(len(repair['splices']),5);self.assertEqual(b''.join(pieces)+before[end:],after)
  self.assertEqual([x for x in before.splitlines() if x.startswith(b'import ')],[x for x in after.splitlines() if x.startswith(b'import ')])
  self.assertIn("len(repair['splices']) == 5",body)
 def test_unbound_publication_holds_without_subprocess(self):
  with patch.object(m.subprocess,'check_output',side_effect=AssertionError('unexpected command')) as proc:
   with self.assertRaises(RuntimeError):m.load('0'*40)
   proc.assert_not_called()
 def test_only_two_exact_mutable_paths_removed(self):
  mutable,retained=retained_fixture()
  self.assertEqual(mutable,{str(m.PROJECT/m.SOURCE),str(m.PROJECT/m.SETUP)})
  self.assertFalse(mutable&set(retained))
  for path,fp in reader.PINNED['extra_pins'].items():
   if path not in mutable:self.assertEqual(retained[path],fp)
  self.assertIn(metadata['failures'][m.TARGET]['normal_metadata']['path'],retained)
  self.assertIn(metadata['word_install']['path'],retained)
 def read_originals(self,changed=None):
  docs=copy.deepcopy(publics)
  if changed:changed(docs)
  spec=SimpleNamespace(graph=graph,active=accepted,dependency_pins={x:{} for x in accepted-set(m.ACCEPTED)},baseline={'isolated':True})
  driver=SimpleNamespace(acceptance_binding=lambda s,commit,module:bindings[module])
  c=SimpleNamespace(docs=docs,reader=reader,driver=driver,s=None)
  runs=[(results[i],{'isolated_context':i},read['original_runs'][i]) for i in (0,1)]
  def owner(_driver,_s,_spec,_runs,module,index,_fixed):return publics[m.PUBLIC_WORD if module==m.WORD else m.PUBLIC_ALLGROUP]['owners'][module]
  with patch.object(reader,'read_run',side_effect=lambda *a:runs[a[3]]),patch.object(reader,'read_owner',side_effect=owner),\
       patch.object(m,'value_fp',side_effect=lambda x:read['current_read_snapshot'] if x is spec.baseline else reader.value_fp(x)):
   return m.read_originals(c,spec)
 def test_real_U_public_summaries_reconstructed(self):
  later,context,owners=self.read_originals()
  self.assertEqual(later,results[1]);self.assertEqual(owners,bindings)
 def test_changed_public_counts_or_joint_scope_rejected(self):
  for mutate in [lambda d:d[m.PUBLIC_WORD]['owners'][m.WORD].update(owned_count=16),
                 lambda d:d[m.READ].update(current_read_live_source_count=157),
                 lambda d:d[m.PUBLIC_ALLGROUP].update(original_group_all_selected_owners_accepted=True)]:
   with self.assertRaises(RuntimeError):self.read_originals(mutate)
 def unchanged(self,alter=None,archived=True,installed=True):
  mutable,retained=retained_fixture()
  sources={x:m.pin(row) for x,row in manifest['project_sources'].items()}
  artifacts={x:{} for x in watch};artifacts[m.TARGET]={m.SETUP:m.SETUP_FP,'unrelated-output':None}
  spec=SimpleNamespace(graph=graph,baseline={'accepted-context':True})
  state=SimpleNamespace(sources=sources,artifacts=artifacts,spec=spec,watch=watch,evidence={'frozen':True},retained=retained,
       accepted=bindings,git={'same':True})
  current=copy.deepcopy(sources);current[m.TARGET]=m.AFTER
  output=copy.deepcopy(artifacts);output[m.TARGET][m.SETUP]=None
  if alter:alter(current,output)
  driver=SimpleNamespace(snapshot=lambda *a:spec.baseline,acceptance_binding=lambda _s,commit,module:bindings[module])
  c=SimpleNamespace(driver=driver,s=SimpleNamespace(d=SimpleNamespace(original_git_state=lambda *a:state.git)))
  def immutable_fp(_c,path):
   self.assertNotIn(str(path),mutable)
   return retained[str(path)]
  with patch.object(m,'source_inventory',return_value=current),patch.object(m,'artifact_inventory',return_value=output),\
       patch.object(m,'tree_inventory',return_value=state.evidence),patch.object(m,'file_fp',side_effect=immutable_fp),\
       patch.object(m,'normal_path',side_effect=lambda x:Path('/tmp/isolated-no-U-normal')/x):
   m.unchanged(c,state,archived=archived,installed=installed)
 def test_authorized_archive_and_install_allowed(self):self.unchanged()
 def test_no_extra_slot_or_source_changes_allowed(self):
  with self.assertRaises(RuntimeError):self.unchanged(installed=False)
  with self.assertRaises(RuntimeError):self.unchanged(archived=False)
  with self.assertRaises(RuntimeError):self.unchanged(lambda src,out:src.update({m.WORD:m.AFTER}))
  with self.assertRaises(RuntimeError):self.unchanged(lambda src,out:out[m.TARGET].update({'unrelated-output':m.SETUP_FP}))
 def archive_fixture(self,action):
  with tempfile.TemporaryDirectory(prefix='smooth-updater-delta-',dir='/tmp') as d:
   base=Path(d);project=base/'project';root=base/'repair';commit='b'*40;run=root/commit/'runs/attempt-00000'
   run.mkdir(parents=True);setup=project/'cache/failed.setup.json';setup.parent.mkdir(parents=True)
   raw=b'isolated exact failed setup';setup.write_bytes(raw);fixed=m.raw_fp(raw)
   def fingerprint(_s,path):
    self.assertTrue(path.is_file());self.assertFalse(path.is_symlink());return m.raw_fp(path.read_bytes())
   def save(path,value):path.write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')
   c=SimpleNamespace(commit=commit,identity={'fixture_U_V_W_identity':True},
       driver=SimpleNamespace(regular_fingerprint=fingerprint),
       s=SimpleNamespace(api=SimpleNamespace(read_json=lambda p:json.loads(p.read_bytes())),d=SimpleNamespace(save=save)))
   state=SimpleNamespace(artifacts={m.TARGET:{'cache/failed.setup.json':fixed}},archives={})
   with patch.multiple(m,PROJECT=project,ROOT=root,SETUP='cache/failed.setup.json',SETUP_FP=fixed,ARCHIVE_NAME='fixed.setup.json'):
    action(c,state,run,setup,raw)
 def test_archive_before_unlink_and_exact_resume(self):
  def action(c,state,run,setup,raw):
   move=m.archive_setup(c,state,run);self.assertFalse(setup.exists())
   self.assertEqual((run/'failed-artifacts/fixed.setup.json').read_bytes(),raw)
   receipt=json.loads((run/'FAILED_SETUP_ARCHIVE.json').read_bytes());self.assertTrue(receipt['archive_fsync_verified'])
   state.artifacts[m.TARGET][m.SETUP]=None;state.archives=m.prior_archive(c)
   self.assertEqual(m.archive_setup(c,state,run)['action'],'ALREADY_ARCHIVED_AND_ABSENT')
   wrong=copy.copy(c);wrong.identity={'different_execution':True}
   with self.assertRaises(RuntimeError):m.prior_archive(wrong)
  self.archive_fixture(action)
 def test_archive_gate_failure_preserves_active_setup(self):
  def action(c,state,run,setup,raw):
   with patch.object(m,'archive_binding',side_effect=RuntimeError('simulated receipt rejection')):
    with self.assertRaises(RuntimeError):m.archive_setup(c,state,run)
   self.assertEqual(setup.read_bytes(),raw)
   self.assertTrue((run/'failed-artifacts/fixed.setup.json').is_file())
  self.archive_fixture(action)
 def test_source_after_is_held(self):
  with tempfile.TemporaryDirectory(prefix='smooth-preimage-',dir='/tmp') as d:
   project=Path(d);source=project/'source.lean';before=b'old';source.write_bytes(b'new')
   c=SimpleNamespace(before=before,driver=SimpleNamespace(regular_fingerprint=lambda s,p:m.raw_fp(p.read_bytes())),s=None)
   with patch.multiple(m,PROJECT=project,SOURCE='source.lean',BEFORE=m.raw_fp(before)):
    with self.assertRaises(RuntimeError):m.require_preimage(c)

if __name__=='__main__':unittest.main(verbosity=2)
