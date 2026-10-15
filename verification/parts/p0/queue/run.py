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
      if re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+',line)
      for m in re.sub(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?','',line).split()]
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('request'); args=ap.parse_args()
    req=json.loads(Path(args.request).read_text()); run_id=req['run_id']
    assert re.fullmatch(r'[A-Za-z0-9_-]+',run_id)
    out=ROOT/'.lake/p0-queue'/run_id; out.mkdir(parents=True,exist_ok=False)
    fresh=os.environ.get('P0_DEPENDENCY_MODE')=='FRESH_PINNED_TARGET_CLOSURE'
    overlay=ROOT/'.lake/p0-queue/fresh-objects' if fresh else out/'objects'; overlay.mkdir(parents=True,exist_ok=fresh); fresh_index_path=ROOT/'.lake/p0-queue/fresh-index.json'
    fresh_index=json.loads(fresh_index_path.read_text()) if fresh_index_path.is_file() else {}
    report={'schema':'p0-finite-queue-v1','run_id':run_id,'source_commit':git('rev-parse','HEAD'),'status':'RUNNING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'strategy':'Fresh pinned target closure' if fresh else 'Exact baseline cache, serial bounded targets; no full build','unconditional_main':False,'stages':[],'reused_project_cache':{},'dependency_replay_claim':False}
    dump(out/'receipt.json',report)
    import fcntl, signal
    lock_path=os.environ.get('CHEN_HEAVY_LOCK_PATH','/workspace/shared/chen-coordination/locks/heavy.lock')
    Path(lock_path).parent.mkdir(parents=True,exist_ok=True)
    lock_fd=os.open(lock_path,os.O_CREAT|os.O_APPEND|os.O_WRONLY,0o600)
    try: fcntl.flock(lock_fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:
        report.update(status='WAITING_FOR_RESOURCE',failure='Host heavy slot is held',finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        dump(out/'receipt.json',report);os.close(lock_fd);return 75
    report['lock']={'path':lock_path,'fd':lock_fd,'inherited_by_heavy_children':True}
    active_proc=None
    def stop(sig,frame):
        if active_proc is not None and active_proc.poll() is None:
            os.killpg(active_proc.pid,signal.SIGTERM)
            try: active_proc.wait(timeout=10)
            except subprocess.TimeoutExpired: os.killpg(active_proc.pid,signal.SIGKILL);active_proc.wait()
        raise RuntimeError('P0 run interrupted by signal '+str(sig))
    signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    env=os.environ.copy(); env.pop('LEAN_PATH',None); env.pop('LEAN_SRC_PATH',None); env['LEAN_NUM_THREADS']='2'
    def run(cmd,label,timeout=600,cwd=ROOT):
        nonlocal active_proc
        log=out/(label+'.log'); start=time.monotonic()
        with log.open('wb') as f:
            proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True,pass_fds=(lock_fd,))
            active_proc=proc
            report['active_child']={'pid':proc.pid,'command':cmd,'label':label,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}; dump(out/'receipt.json',report)
            try: code=proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                # Terminate this run's group only; never kill another task.
                import signal
                os.killpg(proc.pid,signal.SIGTERM)
                try: code=proc.wait(timeout=10)
                except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL); code=proc.wait()
                code=124
        active_proc=None
        report.pop('active_child',None)
        record={'label':label,'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(ROOT)),'log_sha256':sha(log),'checker_resource_policy':'native bundled checker; no supported -M option; single heavy process, LEAN_NUM_THREADS=2' if ('replay-' in label) else None}
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
        report['cache_provenance']={'base_commit':BASE,'success_run':'https://github.com/UyNewNas/goldbach-formalization/actions/runs/38349841383','cache_hit':os.environ.get('P0_CACHE_HIT'),'matched_key':os.environ.get('P0_CACHE_MATCHED_KEY')}
        if fresh:
            bootstrap=ROOT/'.lake/p0-queue/bootstrap/receipt.json'
            receipt=json.loads(bootstrap.read_text())
            assert receipt['status']=='PASS_OFFICIAL_CACHE_ONLY' and receipt['manifest_sha256']==sha(ROOT/'lake-manifest.json'),'Fresh bootstrap is not verified'
            report['cache_provenance']={'mode':'FRESH_PINNED_TARGET_CLOSURE','bootstrap_receipt_sha256':sha(bootstrap),'prior_baseline_receipt_reused':False}
        else:
            assert report['cache_provenance']['cache_hit']=='true','Cache was not an exact hit'
            assert report['cache_provenance']['matched_key'].endswith('-'+BASE),'Wrong cache key'
        report['runtime_sha256']={str(p):sha(p) for p in [lean,checker]}
        report['pins_sha256']={p:sha(ROOT/p) for p in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
        report['verifier_sha256']={p:sha(ROOT/p) for p in ['verification/parts/p0/queue/run.py','verification/parts/p0/queue/bootstrap.py','verification/parts/p0/queue/AuditTemplate.lean','verification/parts/p0/check_pins.py','verification/verify_variable_envelope_boxes.py','.github/workflows/p0-queue.yml','automation/dispatch.json']}
        report['request_sha256']=sha(Path(args.request))
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
        def resolved_object(module,expected):
            relative=Path(module.replace('.','/')+'.olean')
            found=next((p/relative for p in paths if (p/relative).is_file()),None)
            assert found is not None and found.resolve()==expected.resolve(),f'LEAN_PATH provider collision or missing object for {module}: {found} != {expected}'
            return found
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
                if root==ROOT:
                    relative=str(source.relative_to(ROOT))
                    assert git('hash-object',relative)==git('rev-parse','HEAD:'+relative),'Working source differs from published commit'
                sources[str(source)]=sha(source)
                for dep in imports(source): closure(dep)
            seen[module]=(root,source,obj); active.remove(module)
        for module in [*req['modules'],'Init','Lean.Util.CollectAxioms']: closure(module)
        # All original imported main/private/server files are bound, not only .olean.
        for module,(root,source,obj) in seen.items():
            if obj.exists(): objects.update(parts(obj))
            prior=overlay/(module.replace('.','/')+'.olean')
            if fresh and module in fresh_index and prior.exists():objects.update(parts(prior))
        before={'sources':sources,'objects':objects}; dump(out/'inputs-before.json',before)
        compiled=set(); prepared=set()
        def compile_one(module,force=False):
            if module in compiled or (module in prepared and not force):return
            root,source,obj=seen[module]
            is_fresh_source=fresh and (root==ROOT or root==ROOT/'.lake/packages/goldbach')
            if root!=ROOT and not is_fresh_source:
                parts(resolved_object(module,obj));prepared.add(module);return
            deps=imports(source)
            for dep in deps:compile_one(dep)
            dest=overlay/(module.replace('.','/')+'.olean')
            if fresh:
                dep_parts={d:parts(resolved_object(d,overlay/(d.replace('.','/')+'.olean') if (overlay/(d.replace('.','/')+'.olean')).exists() else seen[d][2])) for d in deps}
                signature={'source_sha256':sha(source),'dependency_objects':dep_parts,'pins':report['pins_sha256'],'lean_sha256':sha(lean),'command_policy':['-t0','-j2','-M4096']}
                cached=fresh_index.get(module)
                if not force and cached and cached['inputs']==signature and dest.exists() and parts(dest)==cached['objects']:
                    report.setdefault('reused_fresh_compilation',{})[module]=cached
                    prepared.add(module);return
            else:
                changed=git('diff',BASE,'HEAD','--',str(source.relative_to(ROOT)))!=''
                changed=changed or any(dep in compiled for dep in deps)
                if not force and not changed and obj.is_file():
                    report['reused_project_cache'][module]={'baseline':BASE,'source_sha256':sha(source),'object_parts':parts(resolved_object(module,obj))};prepared.add(module);return
            dest.parent.mkdir(parents=True,exist_ok=True)
            # Prerequisites use the baseline ordinary warning policy; targets are strict.
            command=[str(lean),'-t0','-j2','-M4096',*(['-DwarningAsError=true'] if force else []),'-o',str(dest),str(source.relative_to(root))]
            # run() receives an explicit provider cwd, never changes other workspaces.
            run(command,'compile-'+module,req.get('compile_timeout_seconds',900),cwd=root)
            compiled.add(module); prepared.add(module); report.setdefault('compiled_objects',{})[module]=parts(dest)
            if fresh:
                fresh_index[module]={'inputs':signature,'objects':parts(dest),'producer_run_id':run_id,'replayed':False}
                dump(fresh_index_path,fresh_index)
        for module in req['modules']:
            compile_one(module,force=True)
            run([str(checker),'--verbose',module],'replay-'+module,900)
        # A separate complete serialized defining-module inventory; no namespace filter.
        template=(ROOT/'verification/parts/p0/queue/AuditTemplate.lean').read_text()
        for module in req['modules']:
            audit_name='Audit_'+module.rsplit('.',1)[1]
            source=ROOT/'verification/parts/p0/queue'/(audit_name+'.lean')
            source.write_text(template.replace('TARGET_IMPORT',module).replace('TARGET_NAME',module))
            generated_sha=sha(source)
            obj=overlay/'verification/parts/p0/queue'/(audit_name+'.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
            text=run([str(lean),'-t0','-j2','-M4096','-DwarningAsError=true','-o',str(obj),str(source.relative_to(ROOT))],'audit-'+module,900)
            actual=[json.loads(x.removeprefix('P0_QUEUE_IMPORTS ')) for x in text.splitlines() if x.startswith('P0_QUEUE_IMPORTS ')]
            assert len(actual)==1 and actual[0] and all(m in seen for m in actual[0]),'Actual imported module missing from frozen source closure'
            actual_objects={}
            for m in actual[0]:
                candidate=overlay/(m.replace('.','/')+'.olean')
                actual_objects[m]=parts(resolved_object(m,candidate if candidate.exists() else seen[m][2]))
            report.setdefault('actual_imported_objects',{})[module]=actual_objects
            assert sha(source)==generated_sha,'Generated audit source changed'
            report.setdefault('generated_audit_sha256',{})[str(source.relative_to(ROOT))]=generated_sha
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
        assert all(sha(ROOT/p)==h for p,h in report['verifier_sha256'].items()),'Verifier source changed'
        assert all(sha(ROOT/p)==h for p,h in report['pins_sha256'].items()),'Pins changed'
        assert all(sha(Path(p))==h for p,h in report['runtime_sha256'].items()),'Runtime changed'
        assert all(sha(Path(p))==h for group in ['compiled_objects','audit_objects'] for bundle in report.get(group,{}).values() for p,h in bundle.items()),'New proof object changed'
        assert all(sha(ROOT/p)==h for p,h in report.get('generated_audit_sha256',{}).items()),'Audit source changed'
        assert sha(Path(args.request))==report['request_sha256'],'Request changed'
        report['status']='PASS_SCOPED_LEAVES'; report['verification_level']='FULLY_AUDITED_LEAF_ONLY';report['dependency_acceptance']='Fresh source prerequisites are COMPILED but not separately inventoried/replayed; target actual transitive axiom whitelist and target defining-module census are checked. Official Mathlib and toolchain cached dependencies remain trusted.' if fresh else 'Reused exact baseline dependencies, not newly rebuilt/replayed.'
    except BaseException as e:
        report['status']='FAILED';report['failure']=str(e);print(str(e),file=sys.stderr)
    finally:
        report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();dump(out/'receipt.json',report)
    return 0 if report['status']=='PASS_SCOPED_LEAVES' else 1
if __name__=='__main__':sys.exit(main())
