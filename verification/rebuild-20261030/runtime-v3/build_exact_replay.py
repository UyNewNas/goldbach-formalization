from pathlib import Path
import json,hashlib,time,subprocess,fcntl
from rss_supervisor import supervise
b=Path(__file__).parent;root=Path('/workspace/scratch/ec89760698e5/goldbach-formalization');out=b/'exact-build001';out.mkdir();start=time.monotonic();sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();lock=(b/'batch.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
r={'status':'RUNNING','sourceSha256':sha(b/'ExactReplay.lean'),'stages':[],'supervisorSha256':sha(b/'rss_supervisor.py')};(out/'receipt.json').write_text(json.dumps(r,indent=2))
commands=[['lake','env','lean','-R',str(b),'-o',str(b/'ExactReplay.olean'),'-c',str(b/'ExactReplay.c'),str(b/'ExactReplay.lean')],['lake','env','leanc','-O3','-o',str(b/'exact-replay'),str(b/'ExactReplay.c'),'-lLake']]
for i,cmd in enumerate(commands):
 with (out/f'{i}.log').open('w') as f:result=supervise(cmd,cwd=root,stdout=f,memory_bytes=6144*1024**2,timeout_seconds=1800,batch_deadline=start+16200,poll_seconds=.02)
 r['stages'].append({'command':cmd,'supervision':result,'logSha256':sha(out/f'{i}.log')});(out/'receipt.json').write_text(json.dumps(r,indent=2));print(i,result['exit_code'],flush=True)
 if result['exit_code'] or not result['termination_verified']:r['status']='FAILED';break
else:r['status']='BUILT_NOT_YET_REPLAY_TESTED';r['binarySha256']=sha(b/'exact-replay')
assert sha(b/'ExactReplay.lean')==r['sourceSha256'];(out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
