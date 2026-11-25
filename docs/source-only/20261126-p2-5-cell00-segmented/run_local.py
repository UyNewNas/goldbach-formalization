#!/usr/bin/env python3
"""Run one bounded local diagnostic; never submit a cloud job."""
from pathlib import Path
import argparse, hashlib, json, os, signal, subprocess, time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parents[2]
LAB = REPO/'.lake/p25-segmented-lab'
BIN = Path('/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('module'); modes=ap.add_mutually_exclusive_group(); modes.add_argument('--kernel',action='store_true'); modes.add_argument('--audit',action='store_true'); ap.add_argument('--label',default='attempt001'); args=ap.parse_args()
    rel=Path(*args.module.split('.')); source=ROOT/rel.with_suffix('.lean'); obj=LAB/'objects'/rel.with_suffix('.olean')
    mode='audit' if args.audit else ('kernel' if args.kernel else 'normal'); stem=args.module.replace('.','_')+'-'+args.label+'-'+mode
    log=LAB/'logs'/(stem+'.log'); receipt=LAB/'logs'/(stem+'.json')
    assert not log.exists() and not receipt.exists(), 'Use a fresh explicit label; records are never overwritten.'
    audit_data=None
    if args.audit:
        assert obj.exists()
        audit_data=(REPO/'verification/part2/winner9_private_audit_template.lean').read_text().replace('ImbalancedChen.P2Winner9FiniteMomentKernel',args.module)
        (LAB/'logs'/(stem+'.lean')).write_text(audit_data)
        command=[str(BIN/'lean'),'-t0','-j1','-M4096','-DwarningAsError=true','-DmaxRecDepth=50000','-DmaxHeartbeats=40000000','--stdin']
    elif args.kernel:
        assert obj.exists()
        command=[str(BIN/'leanchecker'),'--verbose',args.module]
    else:
        command=[str(BIN/'lean'),'-t0','-j1','-M4096','-DwarningAsError=true','-DmaxRecDepth=50000','-DmaxHeartbeats=40000000','--root='+str(ROOT),'-o',str(obj),str(source)]
    env=dict(os.environ); env.pop('LEAN_SRC_PATH',None); env['LEAN_SYSROOT']=str(BIN.parent); env['LEAN_PATH']=str(LAB/'objects')
    before={'source_sha256':sha(source),'object_sha256':sha(obj),'dependencies':{str(p.relative_to(LAB/'objects')):sha(p) for p in (LAB/'objects/ImbalancedChen').glob('*.olean')}}
    started=time.monotonic(); peak=0; reason=None
    with log.open('w') as out:
        proc=subprocess.Popen(command,cwd=REPO,env=env,stdin=subprocess.PIPE if audit_data is not None else None,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
        if audit_data is not None:
            proc.stdin.write(audit_data.encode()); proc.stdin.close()
        while proc.poll() is None:
            try:
                status=Path(f'/proc/{proc.pid}/status').read_text()
                rss=next(int(s.split()[1])*1024 for s in status.splitlines() if s.startswith('VmRSS:'))
                peak=max(peak,rss)
                if rss>4*1024**3: reason='external_4GiB_RSS_limit'
            except (FileNotFoundError,StopIteration): pass
            if time.monotonic()-started>180: reason='external_180s_limit'
            if reason:
                os.killpg(proc.pid,signal.SIGKILL); break
            time.sleep(.2)
        code=proc.wait()
    result={'scope':'BOUNDED_LOCAL_VERIFICATION','module':args.module,'mode':mode,'command':command,'exit_code':code,'termination_reason':reason,'seconds':round(time.monotonic()-started,3),'peak_sampled_rss_bytes':peak,'source_sha256':sha(source),'object_sha256':sha(obj),'log_sha256':sha(log),'before':before}
    if args.audit:
        lines=log.read_text().splitlines()
        inventories=[json.loads(s.removeprefix('P0_QUEUE_INVENTORY ')) for s in lines if s.startswith('P0_QUEUE_INVENTORY ')]
        decls=[json.loads(s.removeprefix('P0_QUEUE_DECL ')) for s in lines if s.startswith('P0_QUEUE_DECL ')]
        complete=len(inventories)==1 and sorted(inventories[0]['serialized'])==sorted(inventories[0]['environment'])==sorted(d['name'] for d in decls)
        safe=all(not d[k] for d in decls for k in ['unsafe','partial','axiom'])
        axioms=sorted(set(a for d in decls for a in d['axioms']))
        result.update({'audit_source_sha256':hashlib.sha256(audit_data.encode()).hexdigest(),'full_owned_count':len(decls),'inventory_complete':complete,'all_safe_total_nonaxiom':safe,'transitive_axioms':axioms,'audit_passed':code==0 and reason is None and complete and safe and set(axioms)<={'propext','Classical.choice','Quot.sound'}})
    receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='before'},indent=2),flush=True)
    print(log.read_text()[-5000:],flush=True)
    raise SystemExit(0 if code==0 and reason is None else 1)

if __name__=='__main__': main()
