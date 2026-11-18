#!/usr/bin/env python3
"""Linux CI stage supervisor. No proof-command or resource-guard substitution."""
import argparse, ctypes, datetime, json, os, pathlib, signal, subprocess, sys, time

def members(group):
    found=[]
    for p in pathlib.Path('/proc').iterdir():
        if p.name.isdigit():
            try:
                fields=(p/'stat').read_text().rsplit(')',1)[1].split()
                if int(fields[2])==group and fields[0]!='Z': found.append(int(p.name))
            except (FileNotFoundError, ProcessLookupError): pass
    return found

def reap():
    while True:
        try:
            pid,_=os.waitpid(-1,os.WNOHANG)
            if not pid: break
        except ChildProcessError: break

def stop_group(group, grace):
    evidence=[]
    for sig in (signal.SIGTERM,signal.SIGKILL):
        live=members(group);evidence.append({'signal':sig.name,'live_pids':live})
        if not live: break
        try: os.killpg(group,sig)
        except ProcessLookupError: pass
        end=time.monotonic()+grace
        while members(group) and time.monotonic()<end: time.sleep(.05)
    return evidence

def main():
    p=argparse.ArgumentParser();p.add_argument('--timeout',type=float,required=True);p.add_argument('--grace',type=float,default=5);p.add_argument('stage');p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
    if a.timeout<=0 or a.grace<=0 or not a.command or not all(c.isalnum() or c in '-_' for c in a.stage): p.error('invalid stage, command or deadline')
    # Become the reaper for orphaned grandchildren as well as the direct child.
    libc=ctypes.CDLL(None,use_errno=True)
    if libc.prctl(36,1,0,0,0)!=0: raise OSError(ctypes.get_errno(),'PR_SET_CHILD_SUBREAPER')
    folder=pathlib.Path(os.environ['RUNNER_TEMP'])/'lean-verification-logs';folder.mkdir(parents=True,exist_ok=True)
    logfile=folder/(a.stage+'.log');receipt=folder/(a.stage+'.supervisor.json');start=time.monotonic();started=datetime.datetime.now(datetime.timezone.utc).isoformat();caught=[]
    for sig in (signal.SIGTERM,signal.SIGINT): signal.signal(sig,lambda s,f:caught.append(s))
    result={'stage':a.stage,'command':a.command,'started_utc':started,'timeout_seconds':a.timeout,'status':'RUNNING'};child=None;code=125
    receipt.write_text(json.dumps(result,indent=2)+'\n')
    try:
        with logfile.open('wb',buffering=0) as output, logfile.open('rb') as reader:
            child=subprocess.Popen(a.command,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
            result['process_group']=child.pid
            while True:
                data=reader.read()
                if data: sys.stdout.buffer.write(data);sys.stdout.buffer.flush()
                rc=child.poll()
                if rc is not None:
                    code=rc if rc>=0 else 128-rc;result['reason']='exit';break
                if caught: code=128+caught[0];result['reason']='signal';break
                if time.monotonic()-start>=a.timeout: code=124;result['reason']='timeout';break
                time.sleep(.05)
            residual=members(child.pid)
            # Even a successful parent may not leave child work behind.
            if residual and result['reason']=='exit': code=code or 125;result['reason']='residual_processes'
            result['cleanup']=stop_group(child.pid,a.grace)
            child.wait(timeout=a.grace);reap()
            result['remaining_live_pids']=members(child.pid)
            if result['remaining_live_pids']: code=125
            data=reader.read()
            if data: sys.stdout.buffer.write(data);sys.stdout.buffer.flush()
    except Exception as error:
        code=125;result['reason']='supervisor_error';result['error']=repr(error)
    finally:
        if child is not None and members(child.pid):
            result['emergency_cleanup']=stop_group(child.pid,a.grace)
            try: child.wait(timeout=a.grace)
            except subprocess.TimeoutExpired: pass
            reap()
        result.update(exit_code=code,elapsed_seconds=round(time.monotonic()-start,3),status='PASS' if code==0 else 'FAILED',finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        receipt.write_text(json.dumps(result,indent=2)+'\n')
        for env,text in [('GITHUB_OUTPUT',f'elapsed-seconds={result["elapsed_seconds"]}\nexit-code={code}\n'),('GITHUB_STEP_SUMMARY',f'- {a.stage}: {result["elapsed_seconds"]} seconds; exit code {code}\n')]:
            if os.environ.get(env):
                with open(os.environ[env],'a') as f:f.write(text)
        (folder/(a.stage+'.timing.tsv')).write_text('stage\tstarted_utc\tfinished_utc\telapsed_seconds\texit_code\n'+f'{a.stage}\t{started}\t{result["finished_utc"]}\t{result["elapsed_seconds"]}\t{code}\n')
    return code
if __name__=='__main__':sys.exit(main())
