from pathlib import Path
import sys,json,hashlib,io,tarfile,lzma,base64,datetime
sys.dont_write_bytecode=True
root=Path('/workspace/p29-atlas-20261126/run-007-Part5OriginalCausalSmoothAtlas')
target='ImbalancedChen.Part5OriginalCausalSmoothAtlas'
out=root/'.lake/p2-private'
directory=out/'audit'/target
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
stamp=lambda p:[p.stat().st_dev,p.stat().st_ino,p.stat().st_size,p.stat().st_mtime_ns,p.stat().st_ctime_ns]
source=root/'ImbalancedChen/Part5OriginalCausalSmoothAtlas.lean'
obj=out/'lib/ImbalancedChen/Part5OriginalCausalSmoothAtlas.olean'
assert sha(source)=='7c5060c0abd5fdf7b5d9fea1f768d8570a8fbc7d6b97e77e17b8173add35c027'
records=json.loads((out/'records.json').read_text())
record=records[target]
assert record['exit_code']==0 and record['source_sha256']==sha(source) and record['object_sha256']==sha(obj)
latest=json.loads((directory/'latest.json').read_text())
assert latest['source_sha256']==sha(source) and latest['object_sha256']==sha(obj)
assert not latest['accepted']
drivers=Path('/workspace/p2-9-20261125/verification/part2')
assert sha(drivers/'run_winner9_private_audit.py')=='571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5'
members={}
for p in [source,root/'normal-controller.py',root/'source-selection.json',root/'normal-snapshots.json',root/'LOGBOX_ORIGIN_BINDING.json',out/'records.json',out/'audit/p29-chart.json']:
 assert p.is_file()
 members[str(p.relative_to(root))]=p
for key in ['log']:
 p=root/record[key];assert p.is_file();members[str(p.relative_to(root))]=p
for p in sorted(directory.rglob('*')):
 if p.is_file():members[str(p.relative_to(root))]=p
for name in ['run_winner9_private_audit.py','winner9_private_audit_template.lean']:
 members['original-auditor/'+name]=drivers/name
snap={str(p):{'stat':stamp(p),'sha256':sha(p),'bytes':p.stat().st_size}for p in [*members.values(),obj]}
for r in latest.get('artifacts',{}):assert sha(root/r)==latest['artifacts'][r]
archive=io.BytesIO()
with tarfile.open(fileobj=archive,mode='w')as t:
 for name,p in sorted(members.items()):t.add(p,arcname=name,recursive=False)
payload=lzma.compress(archive.getvalue(),preset=6)
manifest={name:{'bytes':p.stat().st_size,'sha256':sha(p)}for name,p in members.items()}
assert all(stamp(Path(p))==r['stat']and sha(Path(p))==r['sha256']for p,r in snap.items())
meta={'schema':'p29_causal007_original_audit_readonly_diagnostic_v1','root':str(root),'target':target,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':snap[str(source)],'object':snap[str(obj)],'normal_record':record,'audit_receipt':latest,'manifest':manifest,'archive_bytes':len(payload),'archive_sha256':hashlib.sha256(payload).hexdigest(),'all_original_inputs_and_outputs_unchanged':True,'lean_invocations':0,'existing_file_mutations':0,'new_proof_credit':0}
print('P29_CAUSAL007_DIAGNOSTIC '+json.dumps(meta,sort_keys=True),flush=True)
if len(payload)>1200000:
 for field in ['replay','audit']:
  if field in latest:
   p=root/latest[field]['log'];print('P29_BOUND_LAST_LOG '+field+' '+p.read_text()[-24000:],flush=True)
 raise RuntimeError('Full diagnostic archive exceeds bounded output: report exact identity; do not truncate or rerun a proof')
print('P29_CAUSAL007_XZ '+base64.b64encode(payload).decode(),flush=True)
