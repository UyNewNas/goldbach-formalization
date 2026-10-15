#!/usr/bin/env python3
"""P0-only bounded verification. No dependency installation, pin updates or full build.

The workflow restores the exact successful 59d338 cache. Unchanged imported
objects are recorded as reused coverage, not newly rebuilt/replayed dependencies.
New project prerequisites and targets are compiled serially under -j2/-M4096/-t0.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, sys, time
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT))
from verification.verify_variable_envelope_boxes import lean_code
BASE='59d338b93b2347021237eb51293bb934a316909d'

def sha(p):
    with p.open('rb') as f: return hashlib.file_digest(f,'sha256').hexdigest()
def dump(p,v):
    t=p.with_suffix(p.suffix+'.tmp'); t.write_text(json.dumps(v,indent=2)+'\n'); t.replace(p)
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def imports(p):
    return [m for line in lean_code(p.read_text()).splitlines()
      if re.match(r'^\s*(?:(?:public|private)\s+)?import\s+',line)
      for m in re.sub(r'^\s*(?:(?:public|private)\s+)?import\s+','',line).split()]
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('request'); args=ap.parse_args()
    req=json.loads(Path(args.request).read_text()); run_id=req['run_id']
    assert re.fullmatch(r'[A-Za-z0-9_-]+',run_id)
    out=ROOT/'.lake/p0-queue'/run_id; out.mkdir(parents=True,exist_ok=False)
    overlay=out/'objects'; overlay.mkdir(); report={'schema':'p0-finite-queue-v1','run_id':run_id,'source_commit':git('rev-parse','HEAD'),'status':'RUNNING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'strategy':'Exact baseline cache, serial bounded targets; no full build','unconditional_main':False,'stages':[],'reused_project_cache':{},'dependency_replay_claim':False}
    dump(out/'receipt.json',report)
    env=os.environ.copy(); env.pop('LEAN_PATH',None); env.pop('LEAN_SRC_PATH',None); env['LEAN_NUM_THREADS']='2'
    def run(cmd,label,timeout=600):
        log=out/(label+'.log'); start=time.monotonic()
        with log.open('wb') as f:
            proc=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            report['active_child']={'pid':proc.pid,'command':cmd,'label':label,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}; dump(out/'receipt.json',report)
            try: code=proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                # Terminate this run's group only; never kill another task.
                import signal
                os.killpg(proc.pid,signal.SIGTERM)
                try: code=proc.wait(timeout=10)
                except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); code=proc.wait()
                code=124
        report.pop('active_child',None)
        record={'label':label,'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(ROOT)),'log_sha256':sha(log)}
        report['stages'].append(record); dump(out/'receipt.json',report); print(json.dumps(record),flush=True)
        if code: raise RuntimeError(f'{label}: exit {code}; inspect {log}')
        return log.read_text(errors='replace')
    try:
        run([sys.executable,'verification/parts/p0/check_pins.py'],'pins',60)
        lean=Path(subprocess.check_output(['elan','which','lean'],text=True).strip())
        checker=Path(subprocess.check_output(['elan','which','leanchecker'],text=True).strip())
        sysroot=lean.parent.parent
        packages=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
        roots=[ROOT]+[ROOT/'.lake/packages'/p['name'] for p in packages]
        paths=[overlay,ROOT/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in roots[1:]]+[sysroot/'lib/lean']
        env['LEAN_PATH']=':'.join(map(str,paths))
        report['runtime_sha256']={str(p):sha(p) for p in [lean,checker]}
        report['pins_sha256']={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
        run([str(lean),'--version'],'lean-version',60)
        seen={}; objects={}; sources={}; active=set()
        def locate(module):
            rel=Path(module.replace('.','/'))
            for root in roots:
                p=root/rel.with_suffix('.lean')
                if p.is_file(): return root,p,root/'.lake/build/lib/lean'/rel.with_suffix('.olean')
            for root in [sysroot/'src/lean',sysroot/'src/lean/lake']:
                p=root/rel.with_suffix('.lean')
                if p.is_file(): return root,p,sysroot/'lib/lean'/rel.with_suffix('.olean')
            obj=sysroot/'lib/lean'/rel.with_suffix('.olean')
            if obj.is_file(): return None,None,obj
            raise RuntimeError('Missing pinned source/object provider: '+module)
        def parts(obj):
            if not obj.is_file(): raise RuntimeError('Missing cache object: '+str(obj))
            result={str(p):sha(p) for p in sorted(obj.parent.glob(obj.name+'*')) if p.is_file()}
            for ext in ['.ilean']:
                p=obj.with_suffix(ext)
                if p.is_file(): result[str(p)]=sha(p)
            return result
        def closure(module):
            if module in seen: return
            if module in active: raise RuntimeError('Import cycle: '+module)
            active.add(module); root,source,obj=locate(module)
            if source:
                sources[str(source)]=sha(source)
                for dep in imports(source): closure(dep)
            seen[module]=(root,source,obj); active.remove(module)
        for module in req['modules']: closure(module)
        # All original imported main/private/server files are bound, not only .olean.
        for module,(root,source,obj) in seen.items():
            if obj.exists(): objects.update(parts(obj))
        before={'sources':sources,'objects':objects}; dump(out/'inputs-before.json',before)
        compiled=set()
        def compile_one(module,force=False):
            if module in compiled:return
            root,source,obj=seen[module]
            if root!=ROOT:
                parts(obj);return
            deps=imports(source)
            for dep in deps:compile_one(dep)
            changed=git('diff',BASE,'HEAD','--',str(source.relative_to(ROOT)))!=''
            changed=changed or any(dep in compiled for dep in deps)
            if not force and not changed and obj.is_file():
                report['reused_project_cache'][module]={'baseline':BASE,'source_sha256':sha(source),'object_parts':parts(obj)};return
            dest=overlay/(module.replace('.','/')+'.olean'); dest.parent.mkdir(parents=True,exist_ok=True)
            run([str(lean),'-t0','-j2','-M4096','-DwarningAsError=true','-o',str(dest),str(source.relative_to(ROOT))],'compile-'+module,req.get('compile_timeout_seconds',900))
            compiled.add(module); report.setdefault('compiled_objects',{})[module]=parts(dest)
        for module in req['modules']:
            compile_one(module,force=True)
            run([str(checker),'--verbose',module],'replay-'+module,900)
        # A separate complete serialized defining-module inventory; no namespace filter.
        template=(ROOT/'verification/parts/p0/queue/AuditTemplate.lean').read_text()
        for module in req['modules']:
            audit_name='Audit_'+module.rsplit('.',1)[1]
            source=ROOT/'verification/parts/p0/queue'/(audit_name+'.lean')
            source.write_text(template.replace('TARGET_IMPORT',module).replace('TARGET_NAME',module))
            obj=overlay/'verification/parts/p0/queue'/(audit_name+'.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
            text=run([str(lean),'-t0','-j2','-M4096','-DwarningAsError=true','-o',str(obj),str(source.relative_to(ROOT))],'audit-'+module,900)
            decl=[json.loads(x.removeprefix('P0_QUEUE_DECL ')) for x in text.splitlines() if x.startswith('P0_QUEUE_DECL ')]
            inventory=[json.loads(x.removeprefix('P0_QUEUE_INVENTORY ')) for x in text.splitlines() if x.startswith('P0_QUEUE_INVENTORY ')]
            assert len(inventory)==1 and decl and len({d['name'] for d in decl})==len(decl)
            assert {d['name'] for d in decl}==set(inventory[0]['serialized'])==set(inventory[0]['environment'])
            assert all(d['module']==module and not d['unsafe'] and not d['partial'] and not d['axiom'] and set(d['axioms'])<={'propext','Classical.choice','Quot.sound'} and d['type'] and '⋯' not in d['type'] for d in decl)
            dump(out/('declarations-'+module+'.json'),decl)
            (out/(audit_name+'.lean')).write_text(source.read_text())
            report.setdefault('audit_objects',{})[module]=parts(obj)
            # Use the full module path inferred from its source; LEAN_PATH exposes output root.
            run([str(checker),'--verbose','verification.parts.p0.queue.'+audit_name],'audit-replay-'+module,900)
            report.setdefault('audited_declarations',{})[module]=len(decl)
        assert all(Path(p).is_file() and sha(Path(p))==h for p,h in {**sources,**objects}.items()),'Original source/import object changed'
        report['status']='PASS_SCOPED_LEAVES'; report['verification_level']='FULLY_AUDITED_LEAF_WITH_REUSED_DEPENDENCIES'
    except Exception as e:
        report['status']='FAILED';report['failure']=str(e);print(str(e),file=sys.stderr)
    finally:
        report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();dump(out/'receipt.json',report)
    return 0 if report['status']=='PASS_SCOPED_LEAVES' else 1
if __name__=='__main__':sys.exit(main())
