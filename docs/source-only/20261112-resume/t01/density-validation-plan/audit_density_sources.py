"""Read-only static dependency selection audit. No installation/proof execution."""
from pathlib import Path
import hashlib, json, os, re, subprocess

BASE=Path('E:/timot/Documents/FilesForGPT/Myath')
REPO=BASE/'goldbach-proof-continuation'
HERE=BASE/'output/resume-20261112/t01/density-validation-plan'
MIRROR=BASE/'goldbach-proof-github-sync-20261110.git'
PUBLISHER=BASE/'output/t-batch-20261110/publish.git'
ENV={**os.environ,'GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0','GIT_ALLOW_PROTOCOL':''}
BASEPLAN=REPO/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3'
ROOT='a41918dfc6a8b8a7da6ef6df9841632a79f4da6d'
P4='eea9486f7b101d484e2938e97499c1d77cc1a67a'
TARGET='ImbalancedChen.P4AOriginalFiniteAll22FineDensity'

def sha(b): return hashlib.sha256(b).hexdigest()
def blob(b): return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def git(*args):return subprocess.check_output(['git','-c','remote.origin.promisor=false','-c','protocol.allow=never','--git-dir='+str(MIRROR),*args],env=ENV)
def dump(name,value):
    (HERE/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def tree(commit):
    r={}
    for line in git('ls-tree','-r',commit).decode().splitlines():
        a,p=line.split('\t',1)
        if a.split()[1]=='blob':r[p]=a.split()[2]
    return r

TREES={ROOT:tree(ROOT),P4:tree(P4)}
batches=[subprocess.Popen(['git','-c','remote.origin.promisor=false','-c','protocol.allow=never','--git-dir='+str(repo),'cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,env=ENV)
         for repo in [MIRROR,PUBLISHER]]
cache={}
def obj(oid):
    if oid not in cache:
        for batch in batches:
            batch.stdin.write((oid+'\n').encode());batch.stdin.flush()
            header=batch.stdout.readline().decode().strip().split()
            if len(header)!=3 or header[1]!='blob':continue
            b=batch.stdout.read(int(header[2]));assert batch.stdout.read(1)==b'\n'
            assert blob(b)==oid
            cache[oid]=b
            break
        else:raise ValueError('Unavailable exact source object in local mirror/publisher '+oid)
    return cache[oid]
def origin_payload(r):
    origin=r['origin']
    local=REPO/origin.get('path','__no_local_source__')
    if r.get('transform'):
        pre=r['pre_input']
        b=local.read_bytes() if local.is_file() else b''
        if sha(b)!=pre['sha256']:b=obj(pre['git_blob_sha1'])
        assert sha(b)==pre['sha256'] and len(b)==pre['bytes']
        for e in r['transform']:
            a,c=e['old'].encode(),e['new'].encode()
            assert b.count(a)==e['count']
            b=b.replace(a,c)
        assert sha(b)==r['sha256'] and len(b)==r['bytes'] and blob(b)==r['git_blob_sha1'],r['module']
        return b
    if local.is_file():
        b=local.read_bytes()
        if sha(b)==r['sha256']:return b
    try:
        b=obj(r['git_blob_sha1'])
        if sha(b)==r['sha256']:return b
    except ValueError:pass
    if origin['kind']=='git':
        b=git('show',origin['commit']+':'+origin['path'])
    elif origin['kind']=='checkout':b=(REPO/origin['path']).read_bytes()
    else:raise ValueError('Mathematical source has non-source origin '+repr(origin))
    if r.get('transform'):
        for e in r['transform']:
            a,c=e['old'].encode(),e['new'].encode()
            assert b.count(a)==e['count']
            b=b.replace(a,c)
    assert sha(b)==r['sha256'] and len(b)==r['bytes'] and blob(b)==r['git_blob_sha1'],r['module']
    return b

def imports(b):
    # Only source-text command census, not an actual compiler import/read map.
    s=b.decode('utf-8-sig');out=[]
    # Ignore nested block and line comments while preserving newlines.
    i=0;depth=0;clean=[]
    while i<len(s):
        if s[i:i+2]=='/-':depth+=1;i+=2;continue
        if depth:
            if s[i:i+2]=='-/':depth-=1;i+=2
            else:
                if s[i]=='\n':clean.append('\n')
                i+=1
        elif s[i:i+2]=='--':
            j=s.find('\n',i)
            if j<0:break
            clean.append('\n');i=j+1
        else:clean.append(s[i]);i+=1
    for line in ''.join(clean).splitlines():
        m=re.match(r'^\s*(?:public\s+)?import\s+(.+)$',line)
        if m:
            for name in m.group(1).split():
                if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",name):out.append(name)
    return out

base=json.loads((BASEPLAN/'EXACT_INSTALL_MANIFEST.json').read_text(encoding='utf-8'))
basefiles={r['module']:r for r in base['files']}
candidates={}
for commit,t in TREES.items():
    for p,oid in t.items():
        if p.endswith('.lean') and (p.startswith('ImbalancedChen/') or p.startswith('docs/source-only/')):
            name=p[:-5].replace('/','.') if p.startswith('ImbalancedChen/') else 'ImbalancedChen.'+Path(p).stem
            candidates.setdefault(name,[]).append({'origin':{'kind':'git','commit':commit,'path':p},'git_blob_sha1':oid})

overrides={
 'ImbalancedChen.P4AOriginalEarlyTupleCarriers':{'commit':ROOT,'path':'docs/source-only/20261112-resume/install-overlays/ImbalancedChen/P4AOriginalEarlyTupleCarriers.lean'},
 'ImbalancedChen.P4AOriginalEarlyTupleComparison':{'commit':ROOT,'path':'docs/source-only/20261112-resume/install-overlays/ImbalancedChen/P4AOriginalEarlyTupleComparison.lean'},
 'ImbalancedChen.P4AOriginalFiniteAll22FineDensity':{'commit':ROOT,'path':'docs/source-only/20261112-resume/t01/P4AOriginalFiniteAll22FineDensity.lean'},
 'ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient':{'commit':ROOT,'path':'docs/source-only/20261112-resume/t01/P4AOriginalFiniteAll22FineCofinalCoefficient.lean'},
 'ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient':{'commit':ROOT,'path':'docs/source-only/20261112-resume/t01/P4AOriginalFiniteAll22CofinalCoefficient.lean'},
 'ImbalancedChen.P4AOriginalFiniteFallbackFinePPSchedule':{'commit':ROOT,'path':'docs/source-only/20261112-resume/t02/P4AOriginalFiniteFallbackFinePPSchedule.lean'},
 'ImbalancedChen.P4AOriginalSavedSixthWordAccess':{'commit':ROOT,'path':'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/successor_G4_API/P4AOriginalSavedSixthWordAccess.lean'},
 'ImbalancedChen.P2OriginalLaterSixthSourceIntegral':{'commit':ROOT,'path':'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/successor_sixth_history/stage_repairs/P2OriginalLaterSixthSourceIntegral.lean'},
}
p2manifest_path=BASE/'output/resume-20261112/p2-validation/P2_VALIDATION_MANIFEST.json'
p2manifest=json.loads(p2manifest_path.read_text(encoding='utf-8'))
for row in p2manifest['repaired_baseline_changes']:
    if row['in_abi_closure']:
        overrides[row['path'][:-5].replace('/','.')]=dict(commit=p2manifest['repaired_baseline'],path=row['path'])
if p2manifest['repaired_baseline'] not in TREES:
    TREES[p2manifest['repaired_baseline']]=tree(p2manifest['repaired_baseline'])
selected={};payloads={};unresolved={};visiting=set();ordered=[];edges=[];external=set();cycles=[]
def choose(name):
    if name in overrides:
        o=overrides[name];b=obj(TREES[o['commit']][o['path']])
        return {'module':name,'origin':{'kind':'git',**o},'selection':'EXPLICIT_PUBLISHED_REVIEWED_OVERLAY_OR_NEW_ENDPOINT'},b
    if name in basefiles:
        return {**basefiles[name],'selection':'INHERITED_FULL87_V3_EXACT_SELECTION'},origin_payload(basefiles[name])
    cs=candidates.get(name,[])
    production=[r for r in cs if r['origin']['commit']==P4 and r['origin']['path'].startswith('ImbalancedChen/')]
    if production:
        assert len(production)==1
        r=production[0]
        return {'module':name,**r,'selection':'PINNED_P4_PRODUCTION_NEW_TO_BASE'},obj(r['git_blob_sha1'])
    groups={}
    for r in cs:groups.setdefault(r['git_blob_sha1'],[]).append(r)
    if len(groups)==1:
        rs=next(iter(groups.values()))
        # Prefer the current root archive over a topic duplicate of exact bytes.
        r=min(rs,key=lambda r:(r['origin']['commit']!=ROOT,len(r['origin']['path']),r['origin']['path']))
        return {'module':name,**r,'selection':'UNIQUE_PUBLIC_SOURCE_BYTES_NEW_TO_BASE'},obj(r['git_blob_sha1'])
    unresolved[name]={'status':'MISSING' if not groups else 'AMBIGUOUS_SOURCE_VARIANTS',
                      'candidates':[{'git_blob_sha1':oid,'origins':[r['origin'] for r in rs]} for oid,rs in groups.items()]}
    return None,None
def visit(name):
    if not name.startswith('ImbalancedChen.'):
        external.add(name);return
    if name in visiting:cycles.append(name);return
    if name in selected or name in unresolved:return
    try:r,b=choose(name)
    except (ValueError,subprocess.CalledProcessError) as error:
        unresolved[name]={'status':'UNAVAILABLE_EXACT_SOURCE_BYTES','error':str(error)}
        return
    if r is None:return
    selected[name]=r;payloads[name]=b;visiting.add(name)
    ims=imports(b)
    r.update({'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b),
              'install_path':name.replace('.','/')+'.lean','imports':ims})
    if name not in basefiles:
        r['quoted_data_path_mentions']=[{'line':i,'text':s.strip()}
            for i,s in enumerate(b.decode('utf-8-sig').splitlines(),1)
            if re.search(r'"[^"\n]+\.(?:json|npy|npz|bin)"',s)]
        r['input_read_syntax_mentions']=[{'line':i,'text':s.strip()}
            for i,s in enumerate(b.decode('utf-8-sig').splitlines(),1)
            if re.search(r'\b(?:include_str|includeBin|include_bytes|readFile|readBinFile|IO\.FS\.)',s)]
    if name in basefiles:
        assert ims==basefiles[name]['imports'],('INHERITED_IMPORT_CENSUS_DIFFERENCE',name,ims,basefiles[name]['imports'])
    for im in ims:edges.append({'from':name,'to':im});visit(im)
    visiting.remove(name);ordered.append(name)
visit(TARGET)

new=[selected[n] for n in ordered if n not in basefiles]
same=[n for n in ordered if n in basefiles and selected[n]['sha256']==basefiles[n]['sha256']]
replaced=[{'module':n,'before':basefiles[n],'after':selected[n]} for n in ordered if n in basefiles and selected[n]['sha256']!=basefiles[n]['sha256']]
p4diff=[]
for n in same:
    p=n.replace('.','/')+'.lean'
    oid=TREES[P4].get(p)
    if oid and oid!=selected[n]['git_blob_sha1']:
        p4diff.append({'module':n,'selected_sha256':selected[n]['sha256'],'selected_git_blob_sha1':selected[n]['git_blob_sha1'],
                      'p4_production_git_blob_sha1':oid,'policy':'Keep reviewed full87 selection; API/semantic incompatibility remains a remote elaboration obligation, do not silently replace.'})

dump('STATIC_DEPENDENCIES.json',{'schema':'T01_DIRECT_DENSITY_STATIC_SOURCE_CENSUS_V1','target':TARGET,
 'source_snapshots':{'published_root':ROOT,'P4':P4},'base_manifest_path':str(BASEPLAN/'EXACT_INSTALL_MANIFEST.json'),
 'base_manifest_sha256':sha((BASEPLAN/'EXACT_INSTALL_MANIFEST.json').read_bytes()),
 'modules':[selected[n] for n in ordered], 'edges':edges,'external_imports':sorted(external),
 'missing_or_ambiguous':unresolved,'cycles':cycles,'module_count_so_far':len(ordered),
 'new_to_full87_count_so_far':len(new),'inherited_exact_count_so_far':len(same),
 'changed_existing_count_so_far':len(replaced),'closure_complete':not unresolved and not cycles,
 'not_compiled':True,'not_actual_setup_import_receipts':True,'installer_or_guard_executed':False})
dump('SELECTOR_DELTA.json',{'schema':'T01_DIRECT_DENSITY_SOURCE_SELECTOR_DELTA_V1','target':TARGET,
 'new_to_full87':new,'same_names_changed_from_full87':replaced,'explicit_selection_overrides':overrides,
 'P4_production_different_bytes_at_inherited_selected_names':p4diff,
 'remove_from_active_scope':sorted(set(basefiles)-set(selected)),
 'accepted_cached_objects':[],'potential729_is_not_accepted_cache':True})
dump('NEW_SOURCE_DATA_MENTIONS.json',{'schema':'T01_FINE_DENSITY_NEW_SOURCE_INPUT_TEXT_CENSUS_V1',
 'scope':'New-to-full87 sources only; source-text mentions require input mapping review, not actual compiler read receipts.',
 'modules':[{'module':r['module'],'origin':r['origin'],'quoted_data_path_mentions':r['quoted_data_path_mentions'],
             'input_read_syntax_mentions':r['input_read_syntax_mentions']} for r in new
            if r['quoted_data_path_mentions'] or r['input_read_syntax_mentions']]})
p2overlap=[]
for r in p2manifest['modules']:
    if r['module'] in selected:
        current=selected[r['module']]
        p2overlap.append({'module':r['module'],'p2_sha256':r['sha256'],'density_sha256':current['sha256'],
                          'same_source_bytes':r['sha256']==current['sha256']})
dump('P2_SHARED_SOURCE_CENSUS.json',{'schema':'T01_FINE_DENSITY_P2_SHARED_SOURCE_CENSUS_V1',
 'P2_manifest':str(p2manifest_path),'P2_manifest_sha256':sha(p2manifest_path.read_bytes()),
 'P2_source_commit':p2manifest['source_commit'],'P2_repaired_baseline':p2manifest['repaired_baseline'],
 'overlap':p2overlap,'selected_existing_P2_repairs':[r for r in replaced if r['after']['origin'].get('commit')==p2manifest['repaired_baseline']],
 'P2_target_and_diagnostic_not_force_added':True,'compiled_object_reuse_accepted':False,
 'strict_census_diagnostic_only_no_ABI_promotion':True})
for batch in batches:
    batch.stdin.close();batch.wait()
print(json.dumps({'modules_so_far':len(ordered),'new_to_full87':len(new),'same_exact':len(same),'replacements':len(replaced),
 'external_imports':len(external),'unresolved':{k:v['status'] for k,v in unresolved.items()},'cycles':cycles,
 'P4_differing_inherited_names':len(p4diff)},indent=2))
