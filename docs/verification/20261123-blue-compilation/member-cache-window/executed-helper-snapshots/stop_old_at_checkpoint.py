"""At an acquired original Member compiler lock, preserve results and stop only the old Lake/waiters."""
from pathlib import Path
import os,signal,json,hashlib,re,time,datetime
R=Path('/workspace/blue-member-aggregate-evidence');G=R/'checkpoint-v1';STATE=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json');OLD=18089
S=json.loads(STATE.read_text());SHADOW=S['shadow'];LOG=Path('/tmp/member-root-tent-build.log');P=Path('/workspace/blue-member-build')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def proc(pid):
 p=Path('/proc')/str(pid)
 try:
  tail=(p/'stat').read_text().rsplit(')',1)[1].strip().split();argv=[a for a in (p/'cmdline').read_bytes().decode().split('\0') if a]
  return {'pid':int(pid),'ppid':int(tail[1]),'state':tail[0],'starttime':int(tail[19]),'argv':argv}
 except (FileNotFoundError,ProcessLookupError,PermissionError,UnicodeDecodeError):return None
def allproc():return {int(p.name):x for p in Path('/proc').iterdir() if p.name.isdigit() and (x:=proc(p.name)) is not None}
def descendants(pid,ps):
 result=set();change=True
 while change:
  new={p for p,x in ps.items() if x['ppid']==pid or x['ppid'] in result};change=not new<=result;result|=new
 return result
def same(x):
 p=proc(x['pid']);return p is not None and p['starttime']==x['starttime'] and p['argv']==x['argv']
def active_source(ps):return [x for x in ps.values() if x['argv'] and x['argv'][0]==SHADOW+'/bin/lean-runtime']
while not (G/'GATE_ACQUIRED.json').exists():time.sleep(.2)
acquired=json.loads((G/'GATE_ACQUIRED.json').read_text());gate=proc(acquired['pid']);assert gate and '/workspace/blue-build-tools/hold_compiler_gate.py' in gate['argv']
assert acquired['slot']==S['slot'];st=Path(S['slot']).stat();assert (st.st_dev,st.st_ino)==(acquired['slot_device'],acquired['slot_inode'])
locks=Path('/proc/locks').read_text().splitlines();owned=[]
for l in locks:
 a=l.split()
 if '->' in a or len(a)<8 or a[1:4]!=['FLOCK','ADVISORY','WRITE']:continue
 try:dev=a[5].split(':');ok=int(a[4])==acquired['pid'] and int(dev[0],16)==os.major(st.st_dev) and int(dev[1],16)==os.minor(st.st_dev) and int(dev[2])==st.st_ino
 except (ValueError,IndexError):continue
 if ok:owned.append(l)
assert len(owned)==1,owned
ps=allproc();assert not active_source(ps),active_source(ps)
old=ps[OLD];assert old['argv']==['lake','build','ImbalancedChen.Part5OriginalH430RootTentScreen:olean'],old
own_ids=descendants(OLD,ps);own=[ps[p] for p in sorted(own_ids)];allowed={SHADOW+'/bin/'+t for t in ['lean','clang','leanc','leanir','llvm-ar']};waiters=[];unexpected=[]
for x in own:
 a=x['argv']
 if len(a)>=2 and a[1] in allowed:waiters.append(x)
 elif x['state']=='Z':pass
 else:unexpected.append(x)
assert not unexpected,unexpected
write(G/'PROCESS_BEFORE_TERMINATION.json',{'old_lake':old,'captured_old_descendants':own,'captured_waiting_wrappers':waiters,'global_member_shadow_active_runtime':active_source(ps),'other_member_shadow_waiting_wrappers_preserved':[x for x in ps.values() if len(x['argv'])>=2 and x['argv'][1] in allowed and x['pid'] not in own_ids],'exclusive_gate_lock_line':owned[0],'utc':now()})
# A printed Built result is followed by a committed Lake trace. Let last completed result settle.
last_size=LOG.stat().st_size
for _ in range(10):
 time.sleep(.2);size=LOG.stat().st_size
 if size==last_size:break
 last_size=size
text=LOG.read_text();modules=list(dict.fromkeys(re.findall(r'(?:✔|ℹ|⚠) \[\d+/\d+\] Built ([A-Za-z0-9_.]+)',text)))
selected=json.loads(Path('/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json').read_text());records={};missing=[]
for mod in modules:
 if mod in selected['project_sources']:base=P;src=Path(selected['project_sources'][mod]['installed_path'])
 elif mod in selected['native_sources']:base=P/'.lake/packages/goldbach';src=Path(selected['native_sources'][mod]['installed_path'])
 else:continue
 rel=mod.replace('.','/');paths=[src,base/('.lake/build/lib/lean/'+rel+'.olean'),base/('.lake/build/lib/lean/'+rel+'.ilean'),base/('.lake/build/ir/'+rel+'.c'),base/('.lake/build/ir/'+rel+'.setup.json'),base/('.lake/build/lib/lean/'+rel+'.trace')]
 records[mod]={str(p):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in paths if p.exists()}
 if not paths[1].exists() or not paths[-1].exists():missing.append(mod)
assert not missing,missing
write(G/'COMPLETED_MODULES_BEFORE_TERMINATION.json',{'utc':now(),'completed_selected_modules':len(records),'source_plus_five_outputs':records,'reported_Built_modules':modules,'missing_last_success_olean_or_trace':missing})
# Recheck exact identities after snapshots; no active source process is ever signaled.
assert same(old)
latest=allproc();assert not active_source(latest)
# Include any additional old-tree wrappers queued while successful artifacts were being hashed.
latest_ids=descendants(OLD,latest)
for pid in sorted(latest_ids):
 x=latest[pid];a=x['argv']
 if len(a)>=2 and a[1] in allowed:
  if not any(w['pid']==pid for w in waiters):waiters.append(x)
 elif x['state']!='Z':raise AssertionError(('unexpected final old descendant',x))
write(G/'WAITING_WRAPPERS_FINAL_BEFORE_STOP.json',waiters)
os.kill(OLD,signal.SIGTERM);signals=[{'pid':OLD,'signal':'SIGTERM','role':'old Lake controller'}];time.sleep(.4)
for x in waiters:
 if same(x):os.kill(x['pid'],signal.SIGTERM);signals.append({'pid':x['pid'],'signal':'SIGTERM','role':'captured old-tree waiting wrapper','argv':x['argv']})
for _ in range(30):
 remaining=[x for x in [old]+waiters if same(x) and proc(x['pid'])['state']!='Z']
 if not remaining:break
 time.sleep(.1)
assert not remaining,remaining
ps_after=allproc();assert not active_source(ps_after)
for mod,paths in records.items():
 for name,expected in paths.items():
  p=Path(name);assert p.exists() and p.stat().st_size==expected['bytes'] and sha(p)==expected['sha256'],name
raw=LOG.read_bytes();(R/'old-root-tent-build.log').write_bytes(raw)
record={'status':'OLD_MEMBER_CONTROLLER_STOPPED_AT_VERIFIED_QUIESCENT_CHECKPOINT','completion_kind':'OWNER_AUTHORIZED_OPERATOR_STOP_FOR_VERIFIED_CACHE_REUSE','stopped_utc':now(),'old_lake_identity':old,'signals':signals,'running_source_Lean_signaled':False,'Prototype_tree_signaled':False,'exclusive_gate_still_held':True,'compiler_gate_evidence':str(G),'successful_selected_module_groups_preserved':len(records),'source_plus_five_output_hashes_unchanged_after_stop':True,'old_log_sha256':hashlib.sha256(raw).hexdigest(),'old_log_bytes':len(raw),'prior_module_failures_in_log':re.findall(r'✖ \[\d+/\d+\] Building ([A-Za-z0-9_.]+)',raw.decode()),'old_exec_final_exit_code':'root retains session35410 actual status; child cannot access cross-agent session','new_aggregate_started':False}
write(G/'OWNER_STOP_RECEIPT.json',record);write(G/'PROCESS_AFTER_TERMINATION.json',{'utc':now(),'remaining_old_identities':[proc(x['pid']) for x in [old]+waiters],'global_member_shadow_active_runtime':active_source(ps_after),'other_member_shadow_waiting_wrappers_preserved':[x for x in ps_after.values() if len(x['argv'])>=2 and x['argv'][1] in allowed]})
write(R/'OLD_CONTROLLER_COMPLETED.json',record)
write(R/'REUSE_WINDOW_OPEN.json',{'status':'COPY_WINDOW_OPEN_EXTERNAL_COMPILER_GATE_HELD_OLD_MEMBER_TREE_STOPPED','opened_utc':now(),'gate':str(G),'gate_pid':acquired['pid'],'source_Lean_running_in_Member_slot':False,'old_successes_preserved':True,'copy_only_until_stock_released':True,'stock_release_marker':str(R/'STOCK_RELEASED.json')})
print(json.dumps(record,indent=2),flush=True)
