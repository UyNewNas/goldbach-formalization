"""Root-authorized BEFORE only; preserve raw process logs and physical snapshots."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,subprocess,sys,traceback
S=Path(__file__).resolve().parent.parent;R=S.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'path':str(p),'sha256':sha(p)}
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(p,d):
 with p.open('x',encoding='utf-8') as f:f.write(json.dumps(d,indent=2)+'\n')
base=S/'rounds/20261022-native-pnt-before-v1'
terminal=Path(str(base)+'-process-terminal.json')
stdout=Path(str(base)+'.stdout.log');stderr=Path(str(base)+'.stderr.log')
run=S/'rounds/native-pnt-inputs-20261022-v1'
d={'status':'RUNNING_BEFORE_ONLY','started_utc':now(),'authorizing_actor':'root','operator_actor':'/root/principal_eu_admission_sol_medium_oct22','phase':'before','after_or_audit_or_compiler_authorized':False,'retry_count':0,'invocations':0}
rc=1
try:
 assert not terminal.exists() and not run.exists()
 assert not stdout.exists() and not stderr.exists()
 pins={'rounds/20261022-native-pnt-original-inputs-SOURCE-ONLY.py':'1728938a91a0a612bf849bbb77435b2da7bf878ac02d1fcb5d0409c8663e26a0','source-reviews/20261022-native-pnt-original-inputs-source-only-CP.json':'c3f0f4efa8875f1df8322c8bea700ed4f376b306a16a5278666329293fa098e6','source-reviews/20261022-native-pnt-original-inputs-independent-source-review-HOLD.json':'427bc66dd0cc65628fc0b8a01a1f0b560f6ed3cd60ea6b4e0fbc172aca6398f4','rounds/20261022-three-frontiers-common-v2-SOURCE-ONLY.py':'481d94a26e973a94f410bd7c8a0f320ad0babb7e66eaa11b1ab5e6dec2f763d4'}
 assert all(sha(S/p)==h for p,h in pins.items())
 d['bindings']=pins
 spec=importlib.util.spec_from_file_location('physical_idle_definitions_only',S/'rounds/20261022-three-frontiers-common-v2-SOURCE-ONLY.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
 idle=S/'rounds/20261022-native-pnt-before-v1-physical-idle-before.json';write(idle,c.physical_idle());d['idle_before']=ref(idle)
 argv=['/usr/bin/python3','-B',str(S/'rounds/20261022-native-pnt-original-inputs-SOURCE-ONLY.py'),'--phase','before','--directory','rounds/native-pnt-inputs-20261022-v1']
 d.update(argv=argv,cwd=str(R),operator_pid=os.getpid(),invocations=1)
 with stdout.open('xb') as out,stderr.open('xb') as err:
  process=subprocess.Popen(argv,cwd=R,stdout=out,stderr=err,start_new_session=True)
  d.update(pid=process.pid,process_group_id=os.getpgid(process.pid))
  write(Path(str(base)+'-process-started.json'),d)
  rc=process.wait()
 d.update(exit_code=rc,stdout=ref(stdout),stderr=ref(stderr))
 parsed=[]
 for line in stdout.read_text().splitlines():
  try:parsed.append(json.loads(line))
  except json.JSONDecodeError:pass
 d['actual_json_output']=parsed
 assert rc==0,'Original collector first process failure; raw logs preserved'
 assert len(parsed)==1 and parsed[0]['status']=='READONLY_INPUT_MAP_COMPLETE' and parsed[0]['phase']=='before'
 output=Path(parsed[0]['output']['path']);assert sha(output)==parsed[0]['output']['sha256']
 d['before_output']=ref(output)
 idle=S/'rounds/20261022-native-pnt-before-v1-physical-idle-after.json';write(idle,c.physical_idle());d['idle_after']=ref(idle)
 d['status']='BEFORE_ONLY_ORIGINAL_COLLECTOR_PASS_NO_AUDIT_AUTHORITY_HOLD'
except BaseException as error:
 d.update(status='FIRSTFAIL_BEFORE_PROCESS_HOLD_NO_RETRY',error=str(error),traceback=traceback.format_exc())
 rc=rc or 1
finally:
 d['finished_utc']=now()
 if not terminal.exists():write(terminal,d)
print(json.dumps({'terminal':ref(terminal),'status':d['status'],'actual_before':d.get('before_output'),'exit_code':rc}));sys.exit(rc)
