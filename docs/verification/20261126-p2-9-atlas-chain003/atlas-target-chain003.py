from pathlib import Path
import os,sys,hashlib,json,shutil,subprocess,time,tarfile
target='ImbalancedChen.'+sys.argv[1]
attempt=sys.argv[2]; parent=Path('/workspace/p29-atlas-20261126');spec=json.loads((parent/'spec-chain003.json').read_text())
version=attempt+'-'+target.split('.')[-1]
root=parent/('run-'+version); old=Path('/workspace/p2-9-20261125')
run_receivers=json.loads(sys.argv[3])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,v):
 p.parent.mkdir(exist_ok=True,parents=True)
 p.write_text(json.dumps(v,sort_keys=True,indent=2)+'\n')
def require(test,msg):
 if not test:raise ValueError(msg)
root.mkdir(parents=True,exist_ok=False)
os.chdir(root)
out=root/'.lake/p2-private';lib=out/'lib'
drivers=old/'verification/part2';sys.path.insert(0,str(drivers))
import run_winner9_private_audit as audit
import run_winner9_private_checks as checks
require(sha(drivers/'run_winner9_private_audit.py')=='571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5','audit driver mismatch')
records={};originals={};prepared=set()
def install(n):
 if n in prepared:return
 prepared.add(n);entry=spec[n];rel=Path(*n.split('.'));src=root/rel.with_suffix('.lean');src.parent.mkdir(exist_ok=True,parents=True)
 if n==target:
  src.write_text(entry['source_text'])
  require('source_text' in entry and n not in run_receivers,'refuse duplicate target')
 else:
  origin=Path(run_receivers.get(n,entry.get('existing_root','__missing__')))
  require(origin.is_absolute(), 'missing bound existing object '+n)
  reg=origin/'.lake/p2-private/records.json'
  if origin==old:require(sha(reg)=='e95c1c2aeaad29c651c897ec0c2ec6669f0719a5554148c68c4421745f3b5ed8','old family records mismatch')
  if origin.name=='p2-saving16-20261125':require(sha(reg)=='939901a3e66ea7f5b233b48b73e20b72fbe7a878afeefb8165a2558a3e3a9d93','log-box records mismatch')
  if origin==Path('/workspace/p29-atlas-20261126/logbox-frozen-20261126'):require(sha(reg)=='6cfe940c2fecc1a015458ae7b7814274e78289f47d5fe4b9f9f5f25478b58028','frozen log-box records mismatch')
  rec=json.loads(reg.read_text())[n]
  originsrc=origin/rel.with_suffix('.lean');oldobj=reg.parent/'lib'/rel.with_suffix('.olean')
  if not entry.get('object_sha256'):
   accepted=json.loads((reg.parent/'audit'/n/'latest.json').read_text())
   require(accepted['accepted'] is True and accepted['object_sha256']==rec['object_sha256'],'upstream audit')
  expected=entry.get('object_sha256') or rec['object_sha256']
  require(sha(oldobj)==rec['object_sha256']==expected and sha(originsrc)==rec['source_sha256']==entry['source_sha256'],'provenance '+n)
  originals[n]={'source':str(originsrc),'object':str(oldobj),'source_sha256':sha(originsrc),'object_sha256':sha(oldobj)}
  shutil.copy2(originsrc,src)
  for q in oldobj.parent.glob(oldobj.stem+'.*'):
   if q.is_file():
    dest=lib/rel.parent/q.name;dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(q,dest)
  records[n]=rec
 require(sha(src)==entry['source_sha256'],'selected source '+n)
 for d in checks.imports(src):install(d)
install(target)
shutil.copy2(parent/'logbox-frozen-20261126/ORIGIN_BINDING.json',root/'LOGBOX_ORIGIN_BINDING.json')
shutil.copy2(Path(__file__),root/'normal-controller.py')
shutil.copy2(parent/'spec-chain003.json',root/'source-selection.json')
target_source_hash=spec[target]['source_sha256'];target_blob=spec[target]['source_blob']
git=lambda p,cmd:subprocess.check_output(['git',*cmd],cwd=p,text=True).strip()
require(git(checks.MATHLIB,['rev-parse','HEAD'])==checks.PIN,'mathlib pin')
toolchain=dict(lean_version=subprocess.check_output([checks.LEAN,'--version'],text=True).strip(),lean_binary_sha256=sha(Path(checks.LEAN)),mathlib_commit=checks.PIN)
nodes=audit.project_nodes(root,target)
require(set(nodes)==prepared,'source closure mismatch')
frozen=lambda ns:audit.snapshot(root,lib,ns,toolchain)
dep_nodes={n:node for n,node in nodes.items() if n!=target}
prev=frozen(dep_nodes)
audit.verify_compilation(records,dep_nodes,prev)
deps=nodes[target]['deps'];source=nodes[target]['source'];obj=lib/Path(*target.split('.')).with_suffix('.olean')
require(not obj.exists(),'target object already exists')
env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
# Prefer the isolated project roots. The compiler service normally exports locked Mathlib package paths.
mp=Path(checks.MATHLIB);mathpaths=[mp/'.lake/build/lib/lean',*sorted((mp/'.lake/packages').glob('*/.lake/build/lib/lean'))]
env['LEAN_PATH']=':'.join([str(lib),*(str(p) for p in mathpaths if p.is_dir())])
log=out/'logs'/f'{target}.attempt1.log';log.parent.mkdir(parents=True,exist_ok=True)
cmd=[checks.LEAN,'-t0','-j1','-M11264','-DwarningAsError=true','-DmaxRecDepth=50000','-DmaxHeartbeats=40000000','-o',str(obj),str(source.relative_to(root))]
start=time.monotonic()
with log.open('w') as f:
 result=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
after=frozen(dep_nodes)
print('NORMAL',result.returncode,log.read_text()[:12000],flush=True)
require(result.returncode==0,'target normal source compile failed')
require(prev==after and sha(source)==target_source_hash,'normal source/closure changed')
audit.verify_compilation(records,dep_nodes,after)
fd={n:{k:prev['project'][n][k] for k in ('source_sha256','object_sha256')} for n in sorted(prev['project'])}
rec={'module':target,'source':str(source.relative_to(root)),'source_sha256':sha(source),'object':str(obj),'object_sha256':sha(obj),'toolchain':toolchain,'deps':{n:records[n]['object_sha256'] for n in deps},'dependency_signatures':{n:records[n]['closure_signature'] for n in deps},'cache_schema':2,'seconds':round(time.monotonic()-start,3),'command':cmd,'exit_code':result.returncode,'log':str(log.relative_to(root)),'attempts':[{'command':cmd,'exit_code':result.returncode,'log':str(log.relative_to(root))}],'new_strict_compile':True,'dependency_file_check':{'modules':len(fd),'expected_sha256':checks.json_digest(fd),'before_sha256':checks.json_digest(fd),'after_sha256':checks.json_digest(fd),'before_matches_records':True,'after_matches_records':True},'lean':'4.33.0-rc1','mathlib_commit':checks.PIN,'provenance':'New direct strict source compile in isolated private directory; unchanged original audit driver and schema-2 gates.'}
rec['closure_signature']=checks.closure_signature(rec);records[target]=rec
write(out/'records.json',records)
write(root/'normal-snapshots.json',{'before':prev,'after':after,'real_project_source_closure':list(nodes),'compile_command':cmd,'provider_recompiles':0,'mathlib_boundary':toolchain,'lean_path':env['LEAN_PATH']})
audit.verify_compilation(records,nodes,frozen(nodes))
rc=subprocess.run([sys.executable,str(drivers/'run_winner9_private_audit.py'),target,'--summary-name','p29-chart.json','--memory-mb','11264'],env=env,cwd=root).returncode
latest=out/'audit'/target/'latest.json'
receipt=json.loads(latest.read_text()) if latest.is_file() else {}
require(rc==0 and receipt.get('accepted') is True and receipt['replay']['inputs_unchanged'] and receipt['audit']['inputs_unchanged'],'original audit failed '+str(receipt.get('error')))
for art,dgst in receipt['artifacts'].items():require(sha(root/art)==dgst,'artifact hash '+art)
require(sha(obj)==receipt['object_sha256']==rec['object_sha256'],'target postcheck')
for n,origin in originals.items():
 require(sha(Path(origin['source']))==origin['source_sha256'] and sha(Path(origin['object']))==origin['object_sha256'],'original provider drift')
require(frozen(dep_nodes)==prev,'provider final postcheck')
include=list(sorted(q for q in root.rglob('*') if q.is_file()))
files={str(q.relative_to(root)):{'sha256':sha(q),'bytes':q.stat().st_size} for q in include}
manifest={'target':target,'source_blob':target_blob,'source_sha256':sha(source),'object_sha256':sha(obj),'declarations':receipt['audit']['declaration_count'],'axioms':receipt['audit']['axiom_counts'],'normal_compiles':[target],'provider_modules':sorted(originals),'receipt_sha256':sha(latest),'files':files,'normal_driver_sha256':sha(Path(__file__)),'original_audit_driver_sha256':sha(drivers/'run_winner9_private_audit.py')}
write(root/'manifest.json',manifest)
arch=parent/('qualified-'+version+'.tar.gz')
with tarfile.open(arch,'x:gz') as tf:
 for q in [*include,root/'manifest.json']:tf.add(q,arcname=str(q.relative_to(root)),recursive=False)
with tarfile.open(arch) as tf:
 for it in tf.getmembers():require(hashlib.sha256(tf.extractfile(it).read()).hexdigest()==sha(root/it.name),'archive recheck')
print(json.dumps({k:v for k,v in manifest.items() if k!='files'}),flush=True)
print('ARCHIVE',str(arch),arch.stat().st_size,sha(arch),'MANIFEST',sha(root/'manifest.json'),'MEMBERS',len(include)+1,flush=True)
