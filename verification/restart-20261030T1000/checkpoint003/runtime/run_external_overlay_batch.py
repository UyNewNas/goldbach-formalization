from pathlib import Path
import subprocess,hashlib,json,datetime,time,sys,fcntl,os,signal
from rss_supervisor import supervise
import overlay_validator as overlay
import empty_aggregator_binding as empty
root=Path('/workspace/scratch/ec89760698e5/goldbach-formalization'); base=Path(__file__).parent
graphPath=Path(sys.argv[1]).resolve(); graph=json.loads(graphPath.read_text())
overlayPath=Path(sys.argv[2]).resolve()
batch=sys.argv[3]; modules=sys.argv[4:];out=base/batch;out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
r={'status':'RUNNING','started':now(),'base':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'modules':modules,'overlayManifestFile':str(overlayPath),'overlayValidatorSha256':sha(base/'overlay_validator.py'),'dependencyGraphFile':str(graphPath),'dependencyGraphSha256':sha(graphPath),'stages':[],'policy':{'trust':0,'memoryMiB':4096,'aggregateRSSMiB':6144,'threads':2,'memoryScope':'Lean -M4096 plus sampled aggregate process-tree RSS6144MiB; transient peaks may be missed, not a kernel hard cap','perSourceSeconds':1800,'totalSeconds':16200,'serialCompiler':True,'absoluteRoundDeadlineUtc':overlay.DEADLINE},'compileScope':'selected genuine Lake build with original CI guard M4096/full setup/output arguments; local sampled aggregate RSS6144; not full CI workflow','sourceFreezeScope':'all project, all goldbach and LeanArchitect Lean sources and all11 package configs','runnerFile':Path(__file__).name,'runnerSha256':sha(Path(__file__)),'rssSupervisorSha256':sha(base/'rss_supervisor.py'),'rssSupervisorTestsSha256':sha(base/'rss-supervisor-test-results.json'),'auditTemplateSha256':sha(root/'verification/parts/p0/queue/AuditTemplate.lean'),'guardLogStart':len((base/'runtime/compiler-commands.jsonl').read_text().splitlines()),'dependencyScope':'Explicit approved overlay over original dependency pin; original base source and patched source separately bound, selected full-own-axiom audit and exact replay; no full-root claim'}
toolTests=json.loads((base/'exact-tests001/receipt.json').read_text());toolComparison=json.loads((base/'ExactReplay-source-comparison.json').read_text())
assert toolTests['status']=='PASS_AUDIT_UTILITY_TESTS' and all(x['passed'] for x in toolTests['tests'])
assert sha(base/'exact-replay')==toolTests['binarySha256'] and sha(base/'ExactReplay.lean')==toolTests['sourceSha256']==toolComparison['candidate_source_sha256']
assert toolComparison['copied_function_identical']
r['kernelEntry']={'mode':'exact target, official replayFromImports copied byte-for-byte; no prefix enumeration or parallel target scheduling','sourceSha256':sha(base/'ExactReplay.lean'),'binarySha256':sha(base/'exact-replay'),'functionSha256':toolComparison['function_sha256'],'sourceComparisonSha256':sha(base/'ExactReplay-source-comparison.json'),'testReceiptSha256':sha(base/'exact-tests001/receipt.json'),'buildReceiptSha256':sha(base/'exact-build001/receipt.json'),'scope':'all own target declarations from most-private data replayed against imported environment, not fresh replay of imports'}
source_deadline=None
start=time.monotonic(); round_deadline=min(start+16200,start+(datetime.datetime.fromisoformat(overlay.DEADLINE.replace('Z','+00:00'))-datetime.datetime.now(datetime.timezone.utc)).total_seconds()); lock=open(base/'batch.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def save(): (out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
def freeze():
 paths=set((root/'ImbalancedChen').rglob('*.lean'))
 for package in [x['name'] for x in json.loads((root/'lake-manifest.json').read_text())['packages']]:
  d=root/'.lake/packages'/package
  assert d.is_dir(), 'missing pinned package '+package
  if package in ['goldbach','LeanArchitect']: paths.update(d.rglob('*.lean'))
  for filename in ['lean-toolchain','lakefile.lean','lakefile.toml','lake-manifest.json']:
   if (d/filename).is_file(): paths.add(d/filename)
 paths.update(root/p for p in ['ImbalancedChen.lean','lean-toolchain','lakefile.toml','lake-manifest.json'])
 return {str(p.relative_to(root)):sha(p) for p in sorted(paths)}

def run(label,cmd,limit=1800):
 if source_deadline is not None: assert time.monotonic()<source_deadline, "combined source deadline exhausted"
 remaining=int(round_deadline-time.monotonic());assert remaining>0, 'absolute or relative round deadline exhausted'
 t=time.monotonic(); stage={'label':label,'command':cmd,'started':now()};r['active']=stage;save()
 with (out/(label+'.log')).open('w') as f:
  supervision=supervise(cmd,cwd=root,stdout=f,memory_bytes=6144*1024*1024,timeout_seconds=min(limit,remaining,max(0.01, source_deadline-time.monotonic()) if source_deadline else limit),batch_deadline=min(round_deadline,source_deadline) if source_deadline else round_deadline,poll_seconds=0.02)
  stage['supervision']=supervision;code=supervision['exit_code']
  if not supervision['termination_verified']: code=125
 stage.update(exitCode=code,seconds=time.monotonic()-t,logSha256=sha(out/(label+'.log')));r['stages'].append(stage);r.pop('active');save();print(label,code,flush=True)
 if code: raise RuntimeError(label+' failed '+str(code))
try:
 assert time.monotonic()<round_deadline, 'absolute round deadline expired'
 assert modules, 'no targets'
 r['approvedDependencyOverlay']=overlay.validate(root,overlayPath,out/'approved-overlay')
 assert modules, 'at least one external module required'
 assert sha(root/'lake-manifest.json')==graph['manifest_sha256'], 'manifest differs from reviewed frontier'
 archivedGraph=out/'reviewed-frontier.json';archivedGraph.write_bytes(graphPath.read_bytes())
 assert sha(archivedGraph)==r['dependencyGraphSha256']
 r['archivedDependencyGraphFile']=archivedGraph.name
 manifest=json.loads((root/'lake-manifest.json').read_text());r['packages']={}
 for package in manifest['packages']:
  d=root/'.lake/packages'/package['name']
  head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()
  assert head==package['rev'], 'package pin mismatch '+package['name']
  status=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=d,text=True)
  if package['name']!='goldbach': assert not status, 'tracked package modification '+package['name']
  r['packages'][package['name']]={'head':head,'expectedPin':package['rev'],'trackedClean':not bool(status),'approvedOverlay':package['name']=='goldbach'}
 r['toolchainVersion']=subprocess.check_output(['lean','--version'],cwd=root,text=True).strip()
 assert '4.33.0-rc1' in r['toolchainVersion']
 before=freeze();(out/'source-before.json').write_text(json.dumps(before,sort_keys=True));r['sourceBeforeSha256']=sha(out/'source-before.json');save()
 template=(root/'verification/parts/p0/queue/AuditTemplate.lean').read_text()
 for i,m in enumerate(modules):
  source_deadline=min(time.monotonic()+1800,round_deadline)
  assert m in graph['safe_fixed_external_topological_order'], 'module outside reviewed external frontier'
  package=graph['safe_fixed_external_packages'][m]; assert package=='goldbach', 'only reviewed goldbach frontier allowed'
  relative=m.replace('.','/')+'.lean';packageRoot=root/'.lake/packages'/package
  source=str((packageRoot/relative).relative_to(root))
  assert source==graph['source_paths'][m], 'graph source mapping mismatch'
  pinned=subprocess.check_output(['git','show','HEAD:'+relative],cwd=packageRoot)
  assert hashlib.sha256(pinned).hexdigest()==graph['source_sha256'][m], 'reviewed graph does not match original base-pin source'
  if relative in r['approvedDependencyOverlay']['files']:
   binding=r['approvedDependencyOverlay']['files'][relative]
   assert binding['baseSha256']==graph['source_sha256'][m] and sha(root/source)==binding['patchedSha256']
  else: assert hashlib.sha256(pinned).hexdigest()==sha(root/source), 'unlisted source differs from original pinned Git blob'
  emptyBinding=None
  if m==empty.MODULE:
   raise RuntimeError('Empty aggregator overlay ancestor binding not yet approved in this runner revision')
   assert r['packages'][package]['head']==empty.GOLDBACH_PIN
   emptyBinding=empty.validate_source(m,(root/source).read_bytes())
   tests=json.loads((base/'empty-audit-tests002/receipt.json').read_text())
   assert tests['status']=='PASS_EMPTY_AGGREGATOR_AUDIT_TESTS' and all(t['passed'] for t in tests['tests']), 'empty gate negative tests not passed'
   assert tests['runnerSha256']==sha(base/'test_empty_aggregator_audit.py'), 'empty tests runner changed'
   expectedTests=['exact-fixed-source-allowed','reject-different-module','reject-wrong-sha','reject-changed-import','reject-added-declaration-source','Empty-compile','Empty-audit','Empty-exact-replay','Nonempty-compile','Nonempty-audit','Changed-compile','Changed-audit']
   assert [t['name'] for t in tests['tests']]==expectedTests, 'empty gate test inventory incomplete'
   assert tests['auditTemplateSha256']==sha(base/'EmptyAggregatorAudit.lean') and tests['bindingHelperSha256']==sha(base/'empty_aggregator_binding.py')
   emptyBinding['testRunnerSha256']=sha(base/'test_empty_aggregator_audit.py')
   emptyBinding['testReceiptSha256']=sha(base/'empty-audit-tests002/receipt.json')
   emptyBinding['auditTemplateSha256']=sha(base/'EmptyAggregatorAudit.lean')
   emptyBinding['bindingHelperSha256']=sha(base/'empty_aggregator_binding.py')
   emptyBinding['closureBefore']=empty.bind_closure(root,graph,base)
   r.setdefault('emptyAggregatorEvidence',{})[m]=emptyBinding
  obj=str((packageRoot/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')).relative_to(root))
  (root/obj).parent.mkdir(parents=True,exist_ok=True)
  ilean=str(Path(obj).with_suffix('.ilean'));cfile=str((packageRoot/'.lake/build/ir'/(m.replace('.','/')+'.c')).relative_to(root))
  (root/cfile).parent.mkdir(parents=True,exist_ok=True)
  logStart=len((base/'runtime/compiler-commands.jsonl').read_text().splitlines())
  run(f'{i}-compile',['lake','build','@'+package+'/+'+m])
  setup=str((packageRoot/'.lake/build/ir'/(m.replace('.','/')+'.setup.json')).relative_to(root))
  assert (root/setup).is_file(), 'genuine Lake setup file absent'
  commands=[json.loads(line) for line in (base/'runtime/compiler-commands.jsonl').read_text().splitlines()[logStart:]]
  def resolves_source(record):
   for arg in record['input_args']:
    if not arg.endswith('.lean'): continue
    p=Path(arg);p=p if p.is_absolute() else Path(record['cwd'])/p
    if p.resolve()==(root/source).resolve(): return True
   return False
  targetCommands=[record for record in commands if record['tool']=='lean' and resolves_source(record)]
  assert len(targetCommands)==1, 'target must be freshly compiled exactly once, not only cache replay'
  argv=targetCommands[0]['command']
  assert all(flag in argv for flag in ['-t0','-j2','-M4096','-o','-i','-c','--setup','--json']), 'missing genuine compile output/setup/guard argument'
  actualSetup=Path(argv[argv.index('--setup')+1]);actualSetup=actualSetup if actualSetup.is_absolute() else Path(targetCommands[0]['cwd'])/actualSetup
  assert actualSetup.resolve()==(root/setup).resolve(), 'unexpected setup path'
  for flag,expected in [('-o',obj),('-i',ilean),('-c',cfile)]:
   actual=Path(argv[argv.index(flag)+1]);actual=actual if actual.is_absolute() else Path(targetCommands[0]['cwd'])/actual
   assert actual.resolve()==(root/expected).resolve(), 'unexpected output path '+flag
  archivedSetup=out/f'{i}-setup.json';archivedSetup.write_bytes((root/setup).read_bytes())
  r.setdefault('lakeSetup',{})[m]={'path':setup,'sha256':sha(root/setup),'archivedFile':archivedSetup.name,'archivedSha256':sha(archivedSetup),'compilerCommand':targetCommands[0]}
  assert sha(archivedSetup)==sha(root/setup)


  r.setdefault('generatedOutputs',{})[m]={p:sha(root/p) for p in [obj,ilean,cfile]}

  r.setdefault('compiledObjects',{})[m]={str(p.relative_to(root)):sha(p) for p in (root/obj).parent.glob((root/obj).stem+'.*')};save()
  assert r['compiledObjects'][m], 'compiled object parts absent'
  audit=root/'verification/rebuild-20261030'/f'{m.split(".")[-1]}Audit.lean';audit.parent.mkdir(exist_ok=True);audit.write_text((base/'EmptyAggregatorAudit.lean').read_text() if emptyBinding is not None else template.replace('TARGET_IMPORT',m).replace('TARGET_NAME',m))
  auditHash=sha(audit)
  run(f'{i}-axioms',['lake','env','lean',str(audit.relative_to(root))])
  run(f'{i}-kernel',['lake','env','flock',str(base/'runtime/compiler.lock'),str(base/'exact-replay'),m])
  if emptyBinding is not None:
   assert emptyBinding['closureBefore']==empty.bind_closure(root,graph,base), 'empty aggregator imported closure changed'
   assert sha(base/'EmptyAggregatorAudit.lean')==emptyBinding['auditTemplateSha256'] and sha(base/'empty_aggregator_binding.py')==emptyBinding['bindingHelperSha256']
   assert sha(base/'test_empty_aggregator_audit.py')==emptyBinding['testRunnerSha256']
   assert sha(base/'empty-audit-tests002/receipt.json')==emptyBinding['testReceiptSha256']
  assert sha(audit)==auditHash, 'generated audit source changed'
  assert r['compiledObjects'][m]=={str(p.relative_to(root)):sha(p) for p in (root/obj).parent.glob((root/obj).stem+'.*')}, 'object parts changed between compile and audit/replay'
  assert sha(archivedSetup)==r['lakeSetup'][m]['archivedSha256'], 'archived setup changed'
  assert sha(root/setup)==r['lakeSetup'][m]['sha256'], 'Lake setup changed during audit/replay'
  assert r['generatedOutputs'][m]=={p:sha(root/p) for p in [obj,ilean,cfile]}, 'generated outputs changed between compile and audit/replay'
  r.setdefault('objects',{})[m]={str(p.relative_to(root)):sha(p) for p in (root/obj).parent.glob((root/obj).stem+'.*')};save()
 source_deadline=None
 assert sha(archivedGraph)==r['dependencyGraphSha256'], 'archived frontier changed during acceptance'
 assert sha(graphPath)==r['dependencyGraphSha256'], 'reviewed frontier changed during acceptance'
 for package in manifest['packages']:
  d=root/'.lake/packages'/package['name']
  assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()==package['rev']
  if package['name']!='goldbach': assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=d,text=True), 'package modified during batch'
 assert overlay.validate(root,overlayPath)==r['approvedDependencyOverlay'], 'approved overlay changed during batch'
 assert sha(base/'overlay_validator.py')==r['overlayValidatorSha256'], 'overlay validator changed during batch'
 after=freeze();(out/'source-after.json').write_text(json.dumps(after,sort_keys=True));r['sourceAfterSha256']=sha(out/'source-after.json');assert before==after,'source changed during acceptance'
 run('runtime-audit',['python3',str(base/'runtime_guard.py'),'audit','--state',str(base/'runtime/state.json'),'--require-source'])
 assert sha(base/'exact-replay')==r['kernelEntry']['binarySha256'] and sha(base/'ExactReplay.lean')==r['kernelEntry']['sourceSha256'], 'kernel audit utility changed during batch'
 assert sha(base/'ExactReplay-source-comparison.json')==r['kernelEntry']['sourceComparisonSha256'] and sha(base/'exact-tests001/receipt.json')==r['kernelEntry']['testReceiptSha256'], 'kernel utility evidence changed during batch'
 r['kernelEntry']['sourceSha256After']=sha(base/'ExactReplay.lean');r['kernelEntry']['binarySha256After']=sha(base/'exact-replay')
 assert sha(root/'verification/parts/p0/queue/AuditTemplate.lean')==r['auditTemplateSha256'], 'audit template changed during batch'
 assert sha(Path(__file__))==r['runnerSha256'], 'runner changed during batch'
 r['guardLogEnd']=len((base/'runtime/compiler-commands.jsonl').read_text().splitlines()); r['auditSourceSha256']={str(p.relative_to(root)):sha(p) for p in (root/'verification/rebuild-20261030').glob('*Audit.lean')}; r['status']='PASS_APPROVED_OVERLAY_EXTERNAL_MODULES'
except BaseException as e:r['status']='FAILED';r['failure']=str(e)
finally:r['finished']=now();save()
sys.exit(0 if r['status']=='PASS_APPROVED_OVERLAY_EXTERNAL_MODULES' else 1)
