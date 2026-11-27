"""Local sequential invocation of stock Lean and the existing project inventory audit."""
import datetime
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import time

root = pathlib.Path(__file__).resolve().parent
repo = root.parent / 'goldbach-formalization'
package = repo / 'docs/source-only/20261127-p2-5-cell01-decoder'
work = root / 'cell01'
objects = work / 'objects'
strict = ['-t0', '-j1', '-M11264', '-DwarningAsError=true', '-DmaxRecDepth=1000000', '-DmaxHeartbeats=80000000']
template = (repo / 'docs/source-only/20261126-p2-5-cell00-decoded/TYPED_PAYLOAD_AUDIT.lean').read_text()
scalar = json.loads((package/'SCALAR_MANIFEST.json').read_bytes())
fields = json.loads((package/'FIELD_MANIFEST.json').read_bytes())
hashes = {pathlib.Path(p).stem:row['sha256'] for p,row in scalar['files'].items()}
hashes.update({row['module'].split('.')[-1]:row['sha256'] for row in fields['outputs']})
aggregate = 'P2Saving16Cell01ScalarDecode'
support = 'P2Saving16Cell01FieldSimp'
typed = 'P2Saving16Cell01TypedPayload'
typed_pkg = repo/'docs/source-only/20261126-p2-5-cell01-parser-typed'
typed_manifest = json.loads((typed_pkg/'TYPED_PAYLOAD_MANIFEST.json').read_bytes())
hashes[typed] = typed_manifest['source_sha256']
nodes = [*scalar['proof_modules'],aggregate,support,'P2OriginalSaving16DecoderRecordCompose','P2Saving16Cell01FieldBase',*[f'P2Saving16Cell01Simplex{i:02}Decode' for i in range(81)],'P2Saving16Cell01FieldDecode']
assert len(nodes)==len(set(nodes))==98

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def markers(path):
    records={}
    for line in path.read_text().splitlines():
        if line.startswith(('P0_QUEUE_', 'P25_PRIVATE_SCOPED_SIMP_INTERFACE ')):
            name,body=line.split(' ',1)
            records.setdefault(name, []).append(json.loads(body))
    return records

def audit_results(name,src,stage):
    if sha(src)!=hashes[name]:
        raise ValueError(f'Source changed: {name}')
    module='ImbalancedChen.'+name
    obj=objects/'ImbalancedChen'/(name+'.olean')
    data=markers(stage/'AUDIT.log')
    inventory,=data['P0_QUEUE_INVENTORY']
    imports,=data['P0_QUEUE_IMPORTS']
    records=data.get('P0_QUEUE_DECL', [])
    names=sorted(r['name'] for r in records)
    assert inventory['module']==module and names==sorted(inventory['serialized'])==sorted(inventory['environment'])
    assert len(names)==len(set(names)) and len(imports)==len(set(imports))
    assert (name==aggregate)==(not names)
    for declaration in records:
        assert declaration['module']==module and not any(declaration[k] for k in ['unsafe','partial','axiom'])
        assert set(declaration['axioms']) <= {'propext','Classical.choice','Quot.sound'}
    direct=re.findall(r'^import (\S+)', src.read_text(),re.M)
    assert set(direct).issubset(imports)
    if name==aggregate:
        assert direct==['ImbalancedChen.'+s for s in scalar['proof_modules']]
    if name==typed:
        missing=set(module+'.'+n for n in typed_manifest['candidate_declarations'])-set(names)
        assert not missing,missing
    if name==support:
        scope,=data['P25_PRIVATE_SCOPED_SIMP_INTERFACE']
        assert scope['required_count']==scope['matched_count']==scalar['field_simp_private_theorems']
    return {'module':module,'source_sha256':sha(src),'object_sha256':sha(obj),'object_bytes':obj.stat().st_size,'normal_log_sha256':sha(stage/'NORMAL.log'),'stock_replay_log_sha256':sha(stage/'REPLAY.log'),'complete_owned_audit_log_sha256':sha(stage/'AUDIT.log'),'audit_sha256':sha(work/'audits'/(name+'.lean')),'owned_count':len(names),'imports_count':len(imports),'project_imports':[n for n in imports if n.startswith('ImbalancedChen.')],'transitive_axioms':sorted({a for r in records for a in r['axioms']}),'mathematical_endpoint_claimed':False}

def run_owner(name, stage_limit=600, snapshot=None):
    module='ImbalancedChen.'+name
    src=package/'ImbalancedChen'/(name+'.lean');assert sha(src)==hashes[name]
    stage=work/'evidence'/name
    stage.mkdir()
    audit=work/'audits'/(name+'.lean')
    content=template.replace('P2Saving16Cell00TypedPayload',name)
    if name==aggregate:
        content=content.replace('names.size > 0','names.size == 0')
    if name==support:
        appendix=(repo/'docs/source-only/20261126-p2-5-cell00-field-split/PRIVATE_SCOPED_SIMP_AUDIT_APPENDIX.lean').read_text().replace('Cell00','Cell01')
        declared=re.findall(r'^private theorem (\w+)',src.read_text(),re.M)
        assert len(declared)==scalar['field_simp_private_theorems']
        expect=',\n    '.join(json.dumps('ImbalancedChen.P2Saving16Cell01FieldDecode.'+x) for x in declared)
        appendix=re.sub(r'(let expected : Array String := #\[).*?(\]\n  let simpTheorems)',lambda m:m[1]+expect+m[2],appendix,count=1,flags=re.S)
        content+='\n'+appendix
    audit.write_text(content)
    obj=objects/'ImbalancedChen'/(name+'.olean')
    assert not obj.exists()
    commands=[('NORMAL',['lean',*strict,'--root='+str(package),'-o',str(obj),str(src)]),('REPLAY',['leanchecker','-v',module]),('AUDIT',['lean',*strict,'--root='+str(audit.parent),str(audit)])]
    times=[]
    for label,command in commands:
        started=datetime.datetime.now(datetime.timezone.utc).isoformat()
        if snapshot: snapshot(name,label,"before",stage)
        begin=time.monotonic()
        with (stage/(label+'.log')).open('w') as log:
            with subprocess.Popen(['timeout',str(stage_limit)+'s',*command],stdout=log,stderr=subprocess.STDOUT) as child:
                _,wait_status,usage=os.wait4(child.pid,0)
                child.returncode=os.waitstatus_to_exitcode(wait_status)
                status=child.returncode
        times.append({'stage':label,'argv':command,'started_utc':started,'elapsed_seconds':round(time.monotonic()-begin,3),'exit_code':status,'wait4_max_rss_kib':usage.ru_maxrss})
        (stage/'STAGES.json').write_text(json.dumps(times,indent=2)+'\n')
        if snapshot: snapshot(name,label,"after",stage)
        if status: raise RuntimeError(f'{name}: {label} exit {status}; {stage}')
    result=audit_results(name,src,stage)
    (stage/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f"{name}  {result['owned_count']} owned  {round(sum(t['elapsed_seconds'] for t in times),1)}s",flush=True)

if __name__=='__main__':
    stage=work/'evidence'/typed
    assert (stage/'AUDIT_OK').exists()
    typed_row=audit_results(typed,typed_pkg/'ImbalancedChen'/(typed+'.lean'),stage)
    (stage/'RESULT.json').write_text(json.dumps(typed_row,indent=2)+'\n')
    print(typed,typed_row['owned_count'],flush=True)
    for n in nodes:
        run_owner(n)
