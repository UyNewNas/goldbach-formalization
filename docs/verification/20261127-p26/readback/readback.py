"""Independent byte-level readback. Never extracts archive members or imports archived code."""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import tarfile

BASE = Path(__file__).resolve().parents[2]
WORK = BASE / 'materials/p26-work'
REF = BASE / 'materials/recovery-20261127/remaining9-v2-exact/stage'
TOOLS = 'tools/p26/cell05-'
PROTO = TOOLS + 'runtime-recovery-20261127'
TOOL = TOOLS + 'shape-completion-20261127'
OLD_TOOL = TOOLS + 'remaining9-run-20261126'
ANCHORS = json.loads((WORK / PROTO / 'ANCHORS.json').read_bytes())
REC = '/workspace/p26-cell05-runtime-recovery-20261127-v2'
OLD = ANCHORS['remaining9']['stage']
SHAPE = '/workspace/p26-cell05-shape-completion-20261127-v1'
BOUNDARY = json.loads((REF / OLD_TOOL / 'BOUNDARY.json').read_bytes())
SHORT = 'P2OriginalSaving19Geometry05ScalableShape'
MODULE = 'ImbalancedChen.' + SHORT
REL = 'ImbalancedChen/' + SHORT
MODES = ('normal', 'kernel', 'owned')
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
SHAPE_DRIVER_SHA = 'dc75e4c6d56df8673a6551420f74015b0b75d1fec3fe62b544ef63bcc596a133'


def need(test, message):
    if not test:
        raise ValueError(message)


def same(a, b, why):
    if a != b:
        raise ValueError(why)


def decode(b):
    def unique(items):
        d = dict(items)
        need(len(d) == len(items), 'duplicate JSON field')
        return d
    return json.loads(b, object_pairs_hook=unique)


def pin(b):
    return {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def ident(b, path):
    return dict(pin(b), path=path)


def safe(s):
    p = PurePosixPath(s)
    need(s and s not in ('.', '..') and not p.is_absolute() and p.as_posix() == s and '..' not in p.parts and '\\' not in s and '\0' not in s, 'invalid archive/member path')
    return s


def archive(path, size, digest):
    data = path.read_bytes()
    same(pin(data), {'bytes': size, 'sha256': digest}, 'independent exterior pin mismatch')
    out = {}
    expanded = 0
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:xz') as tf:
        for m in tf:
            safe(m.name)
            expanded += m.size
            need(m.type in (tarfile.REGTYPE, tarfile.AREGTYPE) and not m.linkname and not m.sparse and m.size >= 0 and expanded < 256*1024**2 and len(out) < 512, 'invalid or oversized tar member')
            need(m.name not in out, 'duplicate tar member')
            out[m.name] = tf.extractfile(m).read()
            same(len(out[m.name]), m.size, 'truncated tar member')
    manifest = decode(out['EXPORT_MANIFEST.json'])
    rows = manifest['members']
    same(len(rows), len({r['member'] for r in rows}), 'duplicate manifest members')
    same(set(out), {'EXPORT_MANIFEST.json'} | {r['member'] for r in rows}, 'manifest/file set')
    for r in rows:
        same(pin(out[r['member']]), {k:r[k] for k in ('bytes','sha256')}, 'member pin '+r['member'])
    return out, manifest


def frozen_protocol(workflow_sha):
    mb = (WORK / PROTO / 'WORKFLOW_MANIFEST.json').read_bytes()
    same(pin(mb)['sha256'], workflow_sha, 'independently reviewed v2 protocol manifest')
    same(ANCHORS['recovery_stage'],REC,'v2 recovery roots')
    files = {'WORKFLOW_MANIFEST.json': mb}
    for row in decode(mb)['files']:
        n = safe(row['relative_path'])
        files[n] = (WORK / PROTO / n).read_bytes()
        same(pin(files[n]), {k:row[k] for k in ('bytes','sha256')}, 'reviewed protocol '+n)
    return files


def original(path):
    sub = path.removeprefix(OLD+'/')
    need(sub != path, 'outside historical remaining9')
    return (REF / safe(sub)).read_bytes()


def validate_history(h, view):
    fs = h['families']
    same(set(fs), {'prefix13','shape1','remaining8'}, 'history families')
    old_run = decode((REF/'verification/remaining9-complete-v1/RUN.json').read_bytes())['context']
    stop = decode((REF/'verification/remaining9-complete-v1/STOPPED.json').read_bytes())
    prior_archives={}
    for key,name in [('prefix13','cell05-connections13-prefix'),('shape1','cell05-shape-repair')]:
        a=BOUNDARY['origins'][key]['source_archive_pin']
        prior_archives[key],_=archive(Path(__file__).with_name(name+'.tar.xz'),a['bytes'],a['sha256'])
    index13=decode(prior_archives['prefix13']['PARTIAL_INDEX.json'])
    same(index13['original_context'],fs['prefix13']['original_context'],'immutable original fourteen-owner RUN')
    same(index13['failed_fourteenth_owner'],fs['prefix13']['state']['failure'],'exact published first failed normal')
    same(index13['original_records'],fs['prefix13']['state']['records'],'exact published first 39 records')
    by_member={r['original']['path']:r['archive_member'] for r in index13['original_to_archive_map']}
    for k in ('command','result','log','source'):
        r=index13['failed_fourteenth_owner'][k]
        same(ident(prior_archives['prefix13'][by_member[r['path']]],r['path']),r,'first failed '+k)
    previous_success=BOUNDARY['origins']['shape1']['success']
    earlier=prior_archives['shape1'][str(PurePosixPath(previous_success['path']).relative_to(BOUNDARY['origins']['shape1']['stage']))]
    same(ident(earlier,previous_success['path']),previous_success,'separate successful repaired ShapeArrays')
    same(decode(earlier)['records'],fs['shape1']['state']['records'],'public ShapeArrays three checks')
    p8 = fs['remaining8']
    same(old_run, p8['original_context'], 'preserved original context')
    same(view['original'], old_run, 'consumer original')
    same(view['prefix8'], p8['state'], 'consumer state')
    same(view['dependencies'], p8['suppliers'], 'consumer dependencies')
    same(view['target'], old_run['targets'][-1], 'consumer target')
    same(view['target'], p8['target'], 'history target')
    by_path = {r['path']:r for r in h['frozen_inputs']}
    same(len(by_path), len(h['frozen_inputs']), 'historical frozen uniqueness')
    for file in (REF/'verification').rglob('*'):
        if file.is_file():
            p = OLD+'/'+file.relative_to(REF).as_posix()
            same(by_path[p], ident(file.read_bytes(), p), 'historical raw '+p)
    need(len([p for p in by_path if p.startswith(OLD+'/verification/')]) == 113, '113 raw')
    old_records = p8['state']['records']
    same(old_records, stop['records'], 'original24')
    for family, n, count in [('prefix13',13,112),('shape1',1,28),('remaining8',8,116)]:
        fam=fs[family]; state=fam['state']; ctx=fam['original_context']
        same((state['accepted_targets'],state['accepted_steps'],fam['owned_declaration_count']), (n,n*3,count), family+' counts')
        same([(r['module'],r['mode']) for r in state['records']],[(r['module'],m) for r in ctx['targets'][:n] for m in MODES], family+' ordering')
        same(ctx['runtime_guard'], ANCHORS['original_guard'], 'unchanged historical guard')
        if family in ('prefix13','shape1'):
            bound=BOUNDARY['origins'][family]
            same(bound['records'], state['records'], 'frozen original records '+family)
            for a in bound['anchors']:
                same(by_path[a['path']],a,'frozen historical anchor')
        if family != 'shape1':
            failure=state['failure']; same((failure['module'],failure['mode'],failure['status'],failure['exit_code'],failure['accepted'],failure['object']), (ctx['targets'][-1]['module'],'normal','failed',1,False,None), family+' failed normal')
            for k in ('command','result','log','source'):
                item=failure[k]; same(by_path[item['path']],item,family+' failed '+k)
    total_owned=0
    for row in old_records:
        seal=decode(original(row['accepted']['path']))
        same(ident(original(row['accepted']['path']),row['accepted']['path']),row['accepted'],'original seal pin')
        cmd=decode(original(seal['command']['path']));res=decode(original(seal['result']['path']))
        same(res['command'], seal['command'],'historic command/result')
        same((res['status'],res['exit_code'],res['object'],res['run']),( 'succeeded',0,seal['object'],seal['run']),'historic accepted disposition')
        same(res['log'],ident(original(res['log']['path']),res['log']['path']),'historic log')
        if row['mode']=='normal': need('--trust=0' not in cmd['argv'],'historic normal argv')
        if row['mode']=='owned': total_owned+=res['owned_declaration_count']
    same(total_owned,116,'raw owned count')
    bad=decode(original(stop['failed_result']['path']))
    same((bad['status'],bad['exit_code'],bad['object']),('failed',1,None),'original final failure')
    d=p8['state']['failure']
    same({k:d[k] for k in ('source','command','log')},{k:bad[k] for k in ('source','command','log')},'original failed links')
    same(d['result'],stop['failed_result'],'old failed result')
    same(len(bad['dependency_objects']),125,'failed closure')
    return old_run


def recovery(out, manifest, cert_sha, workflow_sha):
    same(manifest['schema'],'p26_explicit_runtime_recovery_export_v1','wrong recovery export')
    protocol=frozen_protocol(workflow_sha)
    names=['CERTIFICATE.json','CURRENT_RUNTIME_GUARD.json','HISTORICAL_VALIDATION.json','CAPTURE_OUTPUT.json','CAPTURE.stderr','CAPTURE_PROCESS.json']
    spec={**{'protocol/'+n:REC+'/'+PROTO+'/'+n for n in protocol}, **{'capture/'+n:REC+'/'+n for n in names}, 'original/ORIGINAL_RUNTIME_GUARD.json':ANCHORS['original_guard']['path'], 'original/ORIGINAL_RUNTIME_SNAPSHOT.json':ANCHORS['original_snapshot']['path']}
    same({r['member']:r['path'] for r in manifest['members']},spec,'exact recovery member mapping')
    for n,b in protocol.items(): same(out['protocol/'+n],b,'archived protocol')
    ids={n:ident(out[n],p) for n,p in spec.items()}
    for n,k in [('ORIGINAL_RUNTIME_GUARD','original_guard'),('ORIGINAL_RUNTIME_SNAPSHOT','original_snapshot')]: same(ids['original/'+n+'.json'],ANCHORS[k],'original '+k)
    c,g,h,v,proc=[decode(out['capture/'+n]) for n in [names[0],names[1],names[2],names[3],names[5]]]
    same(out['capture/CAPTURE.stderr'],b'','capture diagnostics')
    same(proc['exit_code'],0,'capture process')
    same(proc['argv'][1:],['-I','-S','-B',REC+'/'+PROTO+'/recovery.py','capture'],'only capture argv')
    same(proc['stdout'],ids['capture/CAPTURE_OUTPUT.json'],'capture stdout')
    same(proc['stderr'],ids['capture/CAPTURE.stderr'],'capture stderr')
    same(ids['capture/CERTIFICATE.json']['sha256'], cert_sha, 'independently retained certificate')
    for k, n in [('certificate','capture/CERTIFICATE.json'),('history','capture/HISTORICAL_VALIDATION.json'),('current_runtime_guard','capture/CURRENT_RUNTIME_GUARD.json'),('protocol_manifest','protocol/WORKFLOW_MANIFEST.json'),('original_runtime_guard','original/ORIGINAL_RUNTIME_GUARD.json'),('original_snapshot','original/ORIGINAL_RUNTIME_SNAPSHOT.json')]:
        same(v[k],ids[n],'view '+k)
        if k!='certificate':same(c[k],ids[n],'certificate '+k)
    same(manifest['certificate'],v['certificate'],'export certificate')
    same((c['stage'],c['schema'],v['schema'],h['schema']), (REC,'p26_runtime_recovery_certificate_v1','p26_runtime_recovery_verified_v1','p26_runtime_recovery_history_v1'),'recovery schemas')
    same(c['historical_counts'],{'prefix13':[13,39,112],'shape1':[1,3,28],'remaining8':[8,24,116]},'certificate history counts')
    same((c['supplier_count'],c['owned_project_closure_count'],c['historical_loaded_runtime_inventory_claimed']), (125,126,False),'certificate scope')
    linked={r['path']:r for r in h['frozen_inputs']}
    for n in ('certificate','current_runtime_guard','history'):
        row=v[n]; linked[row['path']]=row
    same(v['frozen_inputs'],[linked[k] for k in sorted(linked)],'consumer full history frozen input bindings')
    same(proc['workflow_manifest'],v['protocol_manifest'],'capture workflow')
    same(c['protocol_files'],[ids['protocol/'+n] for n in sorted(protocol)],'certificate source manifest')
    same(c['protocol_files'],h['protocol_files'],'history source manifest')
    for doc in (v,c,h):
        same((doc['original_live_guard_validator_passed'],doc['old_Lean_commands'],doc['P2_6_complete'],doc['original_evidence_rewritten']),(False,0,False,False),'historical boundary')
    same((v['status'],c['status']),('PASS_EXPLICIT_RUNTIME_RECOVERY',)*2,'capture disposition')
    oldrun=validate_history(h,v)
    snap=decode(out['original/ORIGINAL_RUNTIME_SNAPSHOT.json'])
    og=decode(out['original/ORIGINAL_RUNTIME_GUARD.json'])
    roots=snap['roots']; same(len(roots),10,'ten roots')
    summary=[{k:v for k,v in row.items() if k!='files'} for row in roots]
    logical=[{k:v for k,v in row.items() if k!='physical_root'} for row in summary]
    runtime=h['runtime_capture']
    same(runtime['roots'],summary,'capture/full snapshot roots')
    same((runtime['original_guard'],runtime['original_snapshot'],runtime['Lean_commands'],runtime['status']),(ANCHORS['original_guard'],ANCHORS['original_snapshot'],0,'COMPLETE_TEN_ROOT_CONTENT_EQUALITY'),'full ten-root recovery capture')
    summary_on_disk=decode((REF/OLD_TOOL/'original103/runtime-evidence/runtime-P2-SUMMARY.json').read_bytes())
    same(summary_on_disk['roots'],summary,'independently archived ten-root summary')
    same(runtime['original_guard_current_lstat_passed'],False,'old live guard must remain failed')
    need(runtime['original_guard_failure']['message'],'recorded historical failure')
    present=set()
    for row in roots:
        files=row['files']; ns=[safe(e['relative_path']) for e in files]
        same(ns,sorted(set(ns)),'sorted unique root inventory')
        same((len(files),sum(e['bytes'] for e in files),pin(json.dumps(files,sort_keys=True,separators=(',',':')).encode())['sha256']),(row['file_count'], row['total_bytes'],row['logical_inventory_sha256']),'root logical hash')
        present.update(row['physical_root']+'/'+n for n in ns)
    for guard in (og,g):
        same(guard['logical_roots'],logical,'guard logical roots')
        same(guard['snapshot'],ANCHORS['original_snapshot'],'guard snapshot')
        allpaths={e['path']:e['lstat'] for e in guard['entries']}
        need(len(allpaths)==len(guard['entries']) and present <= allpaths.keys(),'guard coverage')
        for row in roots:
            for f in row['files']:
                key=row['physical_root']+'/'+f['relative_path']; info=allpaths[key]
                if 'link_target' in f:
                    need(stat.S_ISLNK(info[2]),'guard symlink metadata')
                    info=allpaths[row['physical_root']+'/'+f['link_target']]
                need(len(info)==6 and stat.S_ISREG(info[2]) and info[3]==f['bytes'],'guard file metadata '+key)
        same((guard['all_selected_bytes_rehashed_before_guard'],guard['historical_loaded_inventory_retroactively_claimed'],guard['kernel_compatibility_replays_required'],guard['normal_replays_permitted']),(True,False,0,False),'guard scope')
    need(og['entries']!=g['entries'],'recorded distinct physical state')
    same(snap['runtime'],oldrun['runtime'],'original runtime binary identity')
    same(c['runtime_identity'],snap['runtime'],'certificate binary identity')
    same(runtime['runtime'],snap['runtime'],'capture binary identity')
    return v, {'ten_root_files':sum(x['file_count'] for x in roots),'ten_root_bytes':sum(x['total_bytes'] for x in roots),'old_guard_failure':runtime['original_guard_failure'],'old_failures':{k:h['families'][k]['state']['failure'] for k in ('prefix13','remaining8')}, 'source_manifest':v['protocol_manifest'],'certificate':v['certificate']}


def audit(log, target, declared):
    marks={'IMPORTS':[],'INVENTORY':[],'DECL':[],'COMPLETE':[]}
    for line in log.splitlines():
        if not line.strip():
            continue
        label,body=line.split(' ',1)
        need(label.startswith('P26_GEOMETRY01_AUDIT_'),'unexpected owned log')
        marks[label.removeprefix('P26_GEOMETRY01_AUDIT_')].append(decode(body))
    imports,=marks['IMPORTS']; inv,=marks['INVENTORY'];done,=marks['COMPLETE']; decls=marks['DECL']
    same(len(imports),len(set(imports)),'unique imported modules')
    project={n for n in imports if n=='ImbalancedChen' or n.startswith('ImbalancedChen.')}
    same(project,{MODULE}|set(target['transitive_dependencies']),'actual project closure')
    same(len(project),126,'exact project module count')
    names=[d['name'] for d in decls]
    same(sorted(set(names)), sorted(names),'unique declarations')
    same(sorted(inv['serialized']),sorted(names),'serialized names completeness')
    same(sorted(inv['environment']),sorted(names),'environment ownership completeness')
    same((inv['module'],done['module'],done['count']),(MODULE,MODULE,len(names)),'complete declaring module')
    need(len(names)>0,'empty named declarations')
    axioms=set()
    for d in decls:
        need(d['module']==MODULE and d['name'] and d['type'].strip() and '⋯' not in d['type'],'invalid full type/owner')
        need(all(d[k] is False for k in ('unsafe','partial','axiom')),'unsafe or axiom owner')
        need(isinstance(d['axioms'],list) and set(d['axioms'])<=AXIOMS,'forbidden owned axiom')
        axioms.update(d['axioms'])
    expected={'module':MODULE,'owned_declaration_count':len(names),'axioms_union':sorted(axioms),'inventory':inv,'declarations':decls,'complete':done}
    same(declared,expected,'parsed audit and raw owned log')
    return len(names), sorted(axioms),len(project)


def shape(out,manifest,rec_out,view,binding_sha,workflow_sha):
    same(manifest['schema'],'cell05_single_shape_recovered_export_v1','shape export schema')
    pr=lambda n: ident(out[n],SHAPE+'/'+n)
    doc=lambda n:decode(out[n])
    protocol=frozen_protocol(workflow_sha)
    capture_names=['CERTIFICATE.json','CURRENT_RUNTIME_GUARD.json','HISTORICAL_VALIDATION.json']
    rv='verification/'
    source='project/'+REL+'.lean';obj='objects/'+REL+'.olean';aud=TOOL+'/owned-audits/'+SHORT+'.lean'
    binding=TOOL+'/RECOVERY_BINDING.json'; run_file=rv+'RUN.json'
    paths={'PREFIX8_VALIDATED.json','COMBINED_INDEX.json',source,obj,aud,TOOL+'/complete_shape.py',TOOL+'/PINS.json',binding,run_file,rv+'SUCCESS.json',rv+'owned-declarations.json'}
    for mode in MODES:
        paths.add('launch-witnesses/'+mode+'.json')
        paths.update(rv+mode+s for s in ('-command.json','.log','-result.json','-accepted.json'))
    expected_artifacts={}
    for n in protocol:
        dst='recovery/'+PROTO+'/'+n
        same(out[dst],rec_out['protocol/'+n],'same published protocol')
        expected_artifacts[REC+'/'+PROTO+'/'+n]=ident(out[dst],REC+'/'+PROTO+'/'+n)
        paths.add(dst)
    for n in capture_names:
        dst='recovery/'+n
        same(out[dst],rec_out['capture/'+n],'same published recovery '+n)
        expected_artifacts[REC+'/'+n]=ident(out[dst],REC+'/'+n)
        paths.add(dst)
    same(set(out),paths|{'EXPORT_MANIFEST.json'},'exact shape archive members')
    for a,b in [(aud,WORK/TOOL/'owned-audits'/(SHORT+'.lean')),(TOOL+'/complete_shape.py',WORK/TOOL/'complete_shape.py'),(TOOL+'/PINS.json',WORK/TOOL/'PINS.json'),(source,WORK/(REL+'.lean'))]:
        same(out[a],b.read_bytes(),'frozen shape file '+a)
    same(pr(TOOL+'/complete_shape.py')['sha256'],SHAPE_DRIVER_SHA,'reviewed Shape driver')
    same(pr(binding)['sha256'],binding_sha,'independently retained binding')
    r=doc(run_file); bb=doc(binding)
    same(bb,{'schema':'cell05_shape_recovery_binding_v1',**{k:view[k] for k in ('certificate','history','current_runtime_guard','protocol_manifest')}},'operator binding')
    for k,j in [('certificate','recovery_certificate'),('history','recovery_history'),('current_runtime_guard','runtime_guard'),('original_runtime_guard','original_runtime_guard'),('original_snapshot','recovery_original_snapshot'),('frozen_inputs','recovery_frozen_inputs'),('protocol_manifest','recovery_protocol_manifest')]:same(r[j],view[k],'RUN recovery '+k)
    same(r['schema'],'cell05_single_shape_recovered_run_v1','recovery RUN schema')
    same(r['recovery_artifacts'],[expected_artifacts[p] for p in [REC+'/'+PROTO+'/WORKFLOW_MANIFEST.json']+[REC+'/'+PROTO+'/'+x['relative_path'] for x in decode(protocol['WORKFLOW_MANIFEST.json'])['files']]+[REC+'/'+n for n in capture_names]],'RUN archive inputs')
    same((r['stage'],r['cwd'],r['original_stage'],r['original_live_guard_validator_passed'],r['old_proof_commands'],r['P2_6_complete']), (SHAPE,SHAPE+'/project',OLD,False,0,False),'RUN boundary')
    same(r['recovery_binding'],pr(binding),'RUN binding')
    old=view['original']; same(r['runtime'],old['runtime'],'stock binary pins')
    env=dict(old['environment']);parts=env['LEAN_PATH'].split(':')
    same(parts[0],OLD+'/objects','old object root')
    env['LEAN_PATH']=':'.join([SHAPE+'/objects',*parts[1:]])
    same(r['environment'],env,'replacement object root only')
    failed=decode(original(view['prefix8']['failure']['command']['path']))
    deps=r['dependencies'];same(len(deps),125,'125 suppliers')
    same(set(deps),set(failed['dependency_objects']),'same dependency names as original failed command')
    for row in view['dependencies']:
        m=row['module'];d=deps[m]
        same(d['object'],failed['dependency_objects'][m],'original object '+m)
        for k,prefix,ext in [('source','project','.lean'),('object','objects','.olean')]:
            pp='/'+prefix+'/'+m.replace('.','/')+ext
            attr={a:row[k][a] for a in ('bytes','sha256')}
            same(d[k],dict(attr,path=OLD+pp),'original '+k)
            same(d['installed_'+k],dict(attr,path=SHAPE+pp),'installed '+k)
    target,=r['targets']; same(target,{'module':MODULE,'source':pr(source),'audit':pr(aud),'project_imports':view['target']['project_imports'],'transitive_dependencies':sorted(deps)},'only target')
    prior=None; recs=[]; metrics={}
    common=[r['runtime']['lean_binary']['path'],'--trust=0','-DwarningAsError=true','-j1','-M12288','-DmaxRecDepth=1000000','-DmaxHeartbeats=0']
    for m in MODES:
        command,log,result,seal=[rv+m+s for s in ('-command.json','.log','-result.json','-accepted.json')]
        witness='launch-witnesses/'+m+'.json';c=doc(command);z=doc(result);a=doc(seal)
        argv={'normal':common+['-o',SHAPE+'/'+obj,REL+'.lean'],'kernel':[r['runtime']['leanchecker_binary']['path'],'--verbose',MODULE],'owned':common+[SHAPE+'/'+aud]}[m]
        fields={'run':pr(run_file),'module':MODULE,'mode':m,'source':pr(source),'audit_source':pr(aud),'dependencies':deps}
        expected=dict(fields,schema='cell05_single_shape_command_v1',previous_accepted=prior,argv=argv,cwd=r['cwd'],environment=env,object_before=pr(obj) if prior else None)
        same({k:v for k,v in c.items() if k!='started_unix'},expected,'command '+m)
        same(doc(witness),dict(schema='cell05_single_shape_launch_v1',module=MODULE,mode=m,run=pr(run_file),command=pr(command)),'witness '+m)
        for k,v in dict(fields,schema='cell05_single_shape_result_v1',command=pr(command),log=pr(log),object=pr(obj),launch_witness=pr(witness),started_unix=c['started_unix'],status='succeeded',exit_code=0,termination_reason=None).items():same(z[k],v,m+' '+k)
        need(z['finished_unix']>=z['started_unix']>0 and 0<z['elapsed_seconds']<=900 and 0<=z['peak_rss_bytes']<=12*1024**3 and len(out[obj])>0,'resource/object boundary')
        metrics[m]={k:z[k] for k in ('elapsed_seconds','peak_rss_bytes','exit_code')}
        same(a,{'schema':'cell05_single_shape_accepted_v1','status':'accepted','module':MODULE,'mode':m,'run':pr(run_file),'launch_witness':pr(witness),'command':pr(command),'result':pr(result),'object':pr(obj)},'seal '+m)
        text=out[log].decode()
        need(not re.search(r'(?:^|:\s*|\s)(?:warning|error|fatal error):',text,re.I|re.M),'diagnostics '+m)
        if m=='kernel':same(text.strip(),'replaying '+MODULE,'actual checker log')
        if m=='normal':
            names=[MODULE+'.'+n for n in re.findall(r'^#print axioms (\w+)$',out[source].decode(),re.M)]
            lines=list(re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])\s*",text))
            same(''.join(e[0] for e in lines),text,'only axiom output')
            same([e[1] for e in lines],names,'exact declared #prints')
            ax={n.strip() for e in lines for n in (e[2] or '').split(',') if n.strip()};need(ax<=AXIOMS,'forbidden normal axiom')
            same(z['printed_axioms'],sorted(ax),'normal axiom union');same(z['printed_declarations'],names,'normal printed names')
        if m=='owned':
            owned=rv+'owned-declarations.json'
            same(z['owned_declarations'],pr(owned),'archived owned inventory')
            cnt,axs,nimport=audit(text,target,doc(owned));same(z['owned_declaration_count'],cnt,'owned count')
        prior=pr(seal);recs.append({'module':MODULE,'mode':m,'accepted':prior})
    pfx='PREFIX8_VALIDATED.json'
    px=doc(pfx);same(r['prefix8'],pr(pfx),'prefix link')
    for k in ('records','accepted_steps','accepted_targets'):same(px[k],view['prefix8'][k],'historical prefix '+k)
    for k in ('command','result','log','source','exit_code','object'):same(px['failed_normal'][k],view['prefix8']['failure'][k],'genuine failure '+k)
    suc=rv+'SUCCESS.json';sd=doc(suc);same(sd['records'],recs,'three seals')
    same((sd['run'],sd['object'],sd['accepted_targets'],sd['accepted_steps'],sd['P2_6_complete'],sd['old_proof_commands']),(pr(run_file),pr(obj),1,3,False,0),'single owner success')
    ind=doc('COMBINED_INDEX.json')
    same((ind['prefix8'],ind['shape_success'],ind['prefix8_accepted_steps'],ind['shape_accepted_steps'],ind['distinct_step_acceptances'],ind['P2_6_complete']),(pr(pfx),pr(suc),24,3,27,False),'separate contexts')
    same(manifest['recovery_certificate'],view['certificate'],'Shape archive certificate')
    return {'source':pr(source),'object':pr(obj),'kernel_binary':r['runtime']['leanchecker_binary'],'metrics':metrics,'owned_declarations':cnt,'owned_axioms':axs,'actual_project_imports':nimport,'old_checks':24,'new_checks':3,'P2_6_complete':False}


def cli():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('recovery','shape'):
        required=name=='recovery'
        p.add_argument('--'+name,type=Path,required=required)
        p.add_argument('--'+name+'-sha',required=required)
        p.add_argument('--'+name+'-size',type=int,required=required)
    p.add_argument('--capture-external-observation',type=Path,required=True)
    p.add_argument('--certificate-sha',required=True)
    p.add_argument('--workflow-sha',required=True)
    p.add_argument('--binding-sha')
    args=p.parse_args()
    ro,rm=archive(args.recovery,args.recovery_size,args.recovery_sha)
    v,rs=recovery(ro,rm,args.certificate_sha,args.workflow_sha)
    ext=decode(args.capture_external_observation.read_bytes())
    same(ext['export']['archive'],{'path':REC+'/RECOVERY_EXPORT.tar.xz','bytes':args.recovery_size,'sha256':args.recovery_sha},'external archive observation')
    same(ext['export']['manifest'],ident(ro['EXPORT_MANIFEST.json'],REC+'/RECOVERY_EXPORT_MANIFEST.json'),'external member manifest identity')
    same(ext['export']['members'],len(ro),'external archive member count')
    for k in ('certificate','history','current_runtime_guard'):same(ext['certified'][k],v[k],'out-of-band '+k)
    same((ext['certified']['prefix8_steps'],ext['certified']['suppliers'],ext['certified']['old_Lean_commands'],ext['certified']['P2_6_complete']),(24,125,0,False),'capture report scope')
    rs.update(manifest=ext['export']['manifest'],history=v['history'],current_runtime_guard=v['current_runtime_guard'],original_runtime_guard=v['original_runtime_guard'],original_snapshot=v['original_snapshot'],archive_members=len(ro),historical_checks={'prefix13':39,'shape1':3,'remaining8':24},old_Lean_commands=0,selected_suppliers=125)
    report={'status':'OFFLINE_RECOVERY_ARCHIVE_VERIFIED','archive':{'bytes':args.recovery_size,'sha256':args.recovery_sha},'recovery':rs,'Lean_commands_executed_by_readback':0,'P2_6_complete':False}
    if args.shape:
        need(all([args.shape_sha,args.shape_size,args.binding_sha]),'independent Shape archive pin and binding required')
        so,sm=archive(args.shape,args.shape_size,args.shape_sha)
        report.update(status='OFFLINE_SHAPE_ARCHIVE_VERIFIED',shape_archive={'bytes':args.shape_size,'sha256':args.shape_sha},shape=shape(so,sm,ro,v,args.binding_sha,args.workflow_sha))
    print(json.dumps(report,sort_keys=True,indent=2))


if __name__=='__main__':
    cli()
