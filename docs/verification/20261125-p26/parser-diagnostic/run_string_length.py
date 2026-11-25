from pathlib import Path
import hashlib,json,os,subprocess,sys,time
ROOT=Path('/workspace/p26-parser-diagnostics-20261125')
TARGETS={'string_length00':'P2OriginalSaving19StringLength00Diagnostic'}
phase=sys.argv[1]
assert phase in TARGETS
name=TARGETS[phase]
source=ROOT/'ImbalancedChen'/(name+'.lean')
objects=ROOT/'objects'
(objects/'ImbalancedChen').mkdir(parents=True,exist_ok=True)
logs=ROOT/'logs';logs.mkdir(exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=str(objects)+os.pathsep+env.get('LEAN_PATH','')
argv=['lean','-DmaxHeartbeats=0','-DmaxRecDepth=1000000','-o',str(objects/'ImbalancedChen'/(name+'.olean')),str(source)]
meta={'phase':phase,'argv':argv,'cwd':str(ROOT),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'started_unix':time.time(),'lean_path':env['LEAN_PATH'],'normal_compile_only':True}
(logs/(phase+'-command.json')).write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta),flush=True)
start=time.monotonic()
with (logs/(phase+'-normal.log')).open('w') as f:
 result=subprocess.run(argv,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
meta.update({'exit_code':result.returncode,'elapsed_seconds':time.monotonic()-start})
(logs/(phase+'-result.json')).write_text(json.dumps(meta,indent=2)+'\n')
print((logs/(phase+'-normal.log')).read_text(),end='',flush=True)
print(json.dumps(meta),flush=True)
sys.exit(result.returncode)
