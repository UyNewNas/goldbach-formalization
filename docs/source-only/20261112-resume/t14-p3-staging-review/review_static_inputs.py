"""Static byte joins. Reads only pinned source, archival files, named frozen packets.
No Lean tooling, installation, build, producer, or Git writes.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = ROOT / 'output/resume-20261112'
GIT = ROOT / 'goldbach-proof-github-sync-20261110.git'
HEAD = '365409fed5d1a485d82cd2b6849b202492dad401'
PAPER = '9731290e8f53cffda44129906cde6a965eaa869b'
E4C = 'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
T01 = BASE / 't01/new-target-validation-plan'
T13 = BASE / 't13-p3-staging'
DR = ROOT / 'goldbach-proof-continuation/.lake/proof-continuation/source-reviews/drafts'
MATHLIB = ROOT / 'goldbach-variable-envelope/.lake/ntfs-source-backups/mathlib'

def sha(b): return hashlib.sha256(b).hexdigest()
def oid(b): return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
def ids(b): return dict(bytes=len(b), sha256=sha(b), git_blob_sha1=oid(b))
def j(p): return json.loads(p.read_bytes())
def rp(p): return p.relative_to(ROOT).as_posix()
def gitb(q): return subprocess.check_output(['git','--git-dir='+str(GIT),'show',HEAD+':'+q])
def save(name,data):
    (HERE/name).write_bytes((json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode())
def gitp(q):
    b = gitb(q)
    return dict(commit=HEAD,path=q,**ids(b))
def read(p):
    if p.drive and len(str(p.resolve()))>=250:
        return Path('\\\\?\\'+str(p.absolute())).read_bytes()
    return p.read_bytes()
def file(p): return dict(path=rp(p), **ids(read(p)))
def packet(path, expected):
    d=T13/path; r=d/'REGISTRY.json'; assert sha(r.read_bytes())==expected
    rows=j(r)['files']; names={row['relative_path'] for row in rows}
    assert len(names)==len(rows)
    assert {p.relative_to(d).as_posix() for p in d.rglob('*') if p.is_file()}==names|{'REGISTRY.json'}
    for row in rows:
        b=(d/row['relative_path']).read_bytes(); assert all(row[k]==v for k,v in ids(b).items())
    return dict(registry=file(r), exact_named_nonregistry_files_checked=len(rows), extra_files=0)

ext=ROOT / 'goldbach-proof-continuation/docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/repairs/PINNED_EXTERNAL_TREES.json'
assert sha(ext.read_bytes())=='ba0b6a320dbc17cc36d671dbc12af22fb587fa2ef3527f2411a542e3c44e5cae'
pkgs={r['package']:r for r in j(ext)}; assert pkgs['mathlib']['sha']==E4C
tree={r['path']:r for r in pkgs['mathlib']['files']}
refs={
    'MeasureTheory/Integral/Prod':[246,250,335,342,467],
    'Analysis/Fourier/AddCircle':[75,85,101,117,123,160,298,347],
    'MeasureTheory/Integral/IntervalIntegral/Periodic':[190,257],
    'MeasureTheory/MeasurableSpace/Constructions':[422],
    'MeasureTheory/Function/LpSpace/Basic':[178],
    'MeasureTheory/Function/L2Space':[45,137],
    'Analysis/Calculus/ContDiff/FTaylorSeries':[120],
    'Topology/Defs/Filter':[134],
    'Analysis/SpecialFunctions/SmoothTransition':[206],
    'Analysis/Calculus/ContDiff/Defs':[1160],
    'Analysis/Normed/Operator/Bilinear':[431,432],
    'Analysis/InnerProductSpace/Basic':[210],
    'Data/Complex/Basic':[665],
    'MeasureTheory/Integral/Bochner/ContinuousLinearMap':[158],
}
evidence=[]
for q,ns in refs.items():
    q='Mathlib/'+q+'.lean'; p=MATHLIB/q; b=p.read_bytes()
    assert tree[q]['bytes']==len(b) and tree[q]['git_blob_sha1']==oid(b)
    lines=b.decode().splitlines();evidence.append(dict(package='mathlib',commit=E4C,git_path=q,**file(p),lines={n:lines[n-1] for n in ns}))
holds=j(T01/'T04_INHERITED_HOLDS.json')['rows']
basename=lambda x:x.rsplit('.',1)[1]
slice_dir=T13/'slice-api-v1'; ds=[]
for index,(key,n,ident) in enumerate([('hiM',174,'f76ab9242486c54235bcef64ff2b371840332ec0ed602ba31c7b133cb310e7d8'),('hsquare',79,'575f7eac12f40bbb11f41b6af97b7f1022599b29cfc2ccab299330102f44b6a9')]):
    row=holds[index]; module=row['module']; name=basename(module); qp='docs/source-only/20261026b-code-only/dots-pending-attachments/'+name+'.lean.txt'
    a=gitb(qp);p=slice_dir/'selection/ImbalancedChen'/(name+'.lean'); b=p.read_bytes(); before=(key+'.prod_right_ae').encode();after=(key+'.prod_left_ae').encode()
    assert a==read(Path(row['source_path'])) and sha(a)==row['sha256']
    assert a.count(before)==1 and b==a.replace(before,after) and sha(b)==ident
    assert before in a.splitlines()[n-1]
    names=re.findall(r'(?m)^(?:private )?(?:def|theorem) (\w+)',a.decode()); assert len(names)==[17,5][index]
    ds.append(dict(module=module,preimage=gitp(qp),postimage=file(p),changed_line=n,old=before.decode(),new=after.decode(),only_change_in_entire_byte_stream=True,unchanged_declaration_headers_count=len(names),all_names=names))
im=holds[2]; a=gitb('ImbalancedChen/'+basename(im['module'])+'.lean'); p=Path(im['candidate_path']); b=read(p)
old=b'Real.smoothTransition.contDiff.differentiable (by norm_num : (1 : '+chr(0x2115).encode()+chr(0x221e).encode()+b') '+chr(0x2264).encode()+b' 1)'; new=b'(Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)'
assert a==read(Path(im['original_path'])) and a.count(old)==1 and b==a.replace(old,new) and sha(a)==im['original_sha256'] and sha(b)==im['candidate_sha256']
ir=Path(im['registry']); imj=j(ir); assert imj['ready_to_install']==False
guards=[]
for g in imj['dependency_guards']:
    row=gitp(g['target_relative_path']); assert row['sha256']==g['sha256']; guards.append(row)
evr=DR/'20261026b-ZeroModeHardy/phase16-spectral-kernel/integration-registry.json'; ev=j(evr)['entries'][0]; ep=Path(ev['candidate_path']); assert read(ep)==read(Path(holds[3]['source_path'])) and sha(read(ep))==ev['candidate_sha256']
pred=[]
for g in ev['import_preimage_guards']:
    p=Path(g['dependency_candidate_path']); assert sha(read(p))==g['expected_sha256']; pred.append(dict(module=g['module_name'],**file(p),historical_ready=g['dependency_ready_to_install']))
paper=[]
for g in j(BASE/'t04/spectral-next/REGISTRY.json')['primary_manuscript_sources']:
    p=ROOT/g['path']; q=p.relative_to(ROOT/'chen-imbalanced-semiprimes').as_posix();b=subprocess.check_output(['git','-C',str(ROOT/'chen-imbalanced-semiprimes'),'show',PAPER+':'+q]); assert b==p.read_bytes() and sha(b)==g['sha256']; paper.append(dict(commit=PAPER,git_path=q,**file(p),anchors=g['anchors']))
save('STATIC_EVIDENCE.json',dict(schema='T14_INDEPENDENT_SOURCE_READBACK_V1',source_head=HEAD,immutable_external_tree=file(ext),lean_ref=pkgs['Lean']['ref'],lean_commit=pkgs['Lean']['sha'],mathlib_commit=E4C,mathlib=evidence,slice_v1_packet=packet('slice-api-v1','3368b7f30f5e8486b80023c1fe574bc8de2f12e3d4cedffb09210bfd5c87e642'),original_slice_v1_pairs=ds,imaginary=dict(original=gitp('ImbalancedChen/'+basename(im['module'])+'.lean'),candidate=file(Path(im['candidate_path'])),only_proof_line_changed=57,registry=file(ir),status=imj['status'],ready_to_install=imj['ready_to_install'],canonical_guard_matches=guards),eigen=dict(leaf=file(ep),registry=file(evr),direct_guards=pred),other_current_head_sources=[gitp('ImbalancedChen/'+name+'.lean') for name in ['Part3ActualQuotientInfinityCylinderFourier','Part3ActualInfinityFourierHeightL2','Part3SmoothZeroHeightSeedProfiles']],original_paper=paper))

def headers(b):
    # Explicit source headers (not synthesized declarations). Ignore default/named
    # arguments inside binders; support structures and `def … where` as well.
    s=b.decode(); out={}
    for m in re.finditer(r'(?m)^(?:(?:private|protected|noncomputable) )?(?:def|theorem|lemma|abbrev|structure) ([\w.]+)',s):
        depth=0; start=m.start(); k=m.end()
        while k<len(s):
            c=s[k]; depth+=(c in '([{')-(c in ')]}'); assert depth>=0,(m.group(1),k)
            if depth==0 and (s[k:k+2]==':=' or s[k:k+6]==' where' and s[k+6:k+7] in ('\n','\r')):break
            k+=1
        assert k<len(s) and m.group(1) not in out; out[m.group(1)]=s[start:k].strip()
    return out

IP=packet('imaginary-existing-selection-v1','2af6dab0920770903d8c6bf30874e5807bf0f3f1a3ba16816cfd581915bb05d9')
AP=packet('slice-api-v2','eb2dc8a27a27f9f09b1dcc93f9ab95e41850832761f8aa712d086c2a6cccfd1b')
ih=headers(gitb('ImbalancedChen/'+basename(im['module'])+'.lean')); assert len(ih)==11 and ih==headers(read(Path(im['candidate_path'])))
AP['pairs']=[]
for i,(name,count) in enumerate([('Part3ActualCompletedHorocycleMeanDerivative',0),('Part3NormalizedCuspCylinderFourier',3),('Part3ActualQuotientInfinityCylinderFourier',2),('Part3ActualInfinityFourierHeightL2',0)]):
    q=ds[i]['preimage']['path'] if i<2 else 'ImbalancedChen/'+name+'.lean'; a=gitb(q); p=T13/'slice-api-v2/selection/ImbalancedChen'/(name+'.lean'); b=p.read_bytes(); expected=a
    if i<3:
        assert expected.count(b'prod_right_ae')==1
        expected=expected.replace(b'prod_right_ae',b'prod_left_ae')
    else: assert b'prod_right_ae' not in a
    if i==0:
        assert expected.count(b'open scoped Topology UpperHalfPlane')==1
        expected=expected.replace(b'open scoped Topology UpperHalfPlane',b'open scoped Topology UpperHalfPlane ContDiff')
    else:
        expected=re.sub(rb'AddCircle\.(fourier(?:Coeff(?:_congr_ae)?)?)\b',rb'_root_.\1',expected)
    assert b==expected; A,B=headers(a),headers(b); assert set(A)==set(B)
    changed=[k for k in A if A[k]!=B[k]]; assert len(changed)==count
    for k in changed: assert B[k]==A[k].replace('AddCircle.fourier','_root_.fourier')
    AP['pairs'].append(dict(module='ImbalancedChen.'+name,preimage=gitp(q),postimage=file(p),only_reviewed_substitutions=True,source_header_count=len(A),changed_source_headers=changed,canonical_fourier_occurrences=len(re.findall(rb'_root_\.fourier(?:Coeff(?:_congr_ae)?)?\b',b)),haar_qualification_preserved=(b.count(b'AddCircle.haarAddCircle')==a.count(b'AddCircle.haarAddCircle'))))
save('SLICE_V2_AND_IMAGINARY_JOINS.json',dict(slice_v2=AP,imaginary=IP,imaginary_declaration_headers=len(ih),imaginary_headers_changed=0,installed=False,kernel_verified=False))

EIG=packet('eigen-local-api-and-holds-v1','0be75bb5439e085757c33c27fd11898946182be9728b61d9931beb25c9d85277'); EIG['pairs']=[]
for name,orig,order in [(basename(ev['module_name']),ep,'Topology ContDiff'),(basename(pred[1]['module']),ROOT/pred[1]['path'],'ContDiff')]:
    a=read(orig); p=T13/'eigen-local-api-and-holds-v1/selection/ImbalancedChen'/(name+'.lean'); b=read(p)
    assert a.count(b'open scoped MatrixGroups UpperHalfPlane')==1
    expected=a.replace(b'open scoped MatrixGroups UpperHalfPlane',('open scoped MatrixGroups UpperHalfPlane '+order).encode())
    if orig==ep:
        o=b'simp_rw [inner_self_eq_norm_sq_to_K] at h'; assert expected.count(o)==1
        expected=expected.replace(o,'simp_rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] at h'.encode())
    assert b==expected and headers(a)==headers(b)
    EIG['pairs'].append(dict(module='ImbalancedChen.'+name,preimage=file(orig),postimage=file(p),source_header_count=len(headers(a)),changed_source_headers=[],only_reviewed_substitutions=True))
assert sum(r['source_header_count'] for r in EIG['pairs'])==11
save('EIGEN_JOINS.json',EIG)
upq='ImbalancedChen/Part3ActualPoincareSpectralCoefficient.lean'; upstream=gitp(upq); pb=gitb(upq); assert upstream['sha256']=='335c593ece0ccc557585b58513b90e31767616141e97f8f038df38314f873a05'; assert [n for n,l in enumerate(pb.splitlines(),1) if b'AddCircle.fourier' in l]==[157,162,169,200,249]; sg=next(r for r in j(T01/'STATIC_SOURCE_SELECTION.json')['modules'] if r['module']=='ImbalancedChen.Part3ActualPoincareSpectralCoefficient'); assert sg['sha256']==upstream['sha256'] and sg['git_blob_sha1']==upstream['git_blob_sha1']; upstream['also_T01_origin']=sg['origin']; upstream['lines_with_stale_Fourier_names']=[157,162,169,200,249]
seed=gitp('ImbalancedChen/Part3SmoothZeroHeightSeedProfiles.lean'); assert seed['sha256'].startswith('92aa836b'); seed['scope_seam_lines']=[19,27,43]
DIRECT=packet('direct-predecessor-api-v1','74676059b08e6ecb51bab4c277ac9dbc015fce4dace87a9963b851ddfecd6868'); DIRECT['pairs']=[]
for ob,sections in [(seed,16),(upstream,22)]:
    name=Path(ob['path']).stem; p=T13/'direct-predecessor-api-v1/selection'/ob['path']; a=gitb(ob['path']); b=read(p); A,B=headers(a),headers(b)
    assert len(A)==sections and set(A)==set(B); changed=[n for n in A if A[n]!=B[n]]
    if ob==seed:
        assert a.count(b'open scoped UpperHalfPlane')==1 and b==a.replace(b'open scoped UpperHalfPlane',b'open scoped UpperHalfPlane ContDiff') and not changed
        assert 'SmoothHeightSeed' in A and 'SmoothHeightSeed.maass' in A and 'profileTensor' in A and b'cinfty : ContDiff' in b
    else:
        assert b==re.sub(rb'AddCircle\.(fourier(?:_neg)?)\b',rb'_root_.\1',a) and changed==['actualTestFourier_eq_interval','actualTestFourier_positive_height']
        assert all(B[n]==A[n].replace('AddCircle.fourier','_root_.fourier') for n in changed)
    DIRECT['pairs'].append(dict(module='ImbalancedChen.'+name,preimage=ob,postimage=file(p),source_header_count=len(A),changed_source_headers=changed,only_reviewed_substitutions=True))
DIRECT['frozen_prose_erratum']='ActualPoincareSpectralCoefficient changes two theorem headers, not one. See the two named headers and original raw/computed bytes.'
remaining='ImbalancedChen/Part3SmoothIntegerUnitPartition.lean'; sr=gitp(remaining); source=gitb(remaining).decode(); assert sr['sha256']=='3eb60ea1153e4138bb21f6ca54d240f6d02bbb88639d38da69bbbc9e11b3620d'; assert source.splitlines()[21]=='open Set Filter' and 'ContDiff ℝ ∞' in source.splitlines()[81] and 'ContDiff ℝ ∞' in source.splitlines()[105] and 'open scoped ContDiff' not in source; sr['open_scope_observation']='original at named HEAD uses ContDiff smoothness infinity on lines 82/106, only explicit open at 22 is Set Filter. This is a separate predecessor outside this bounded review.'
save('DIRECT_JOINS.json',DIRECT)
allow=[]
for row in AP['pairs']+DIRECT['pairs']+EIG['pairs']:
    allow.append(dict(module=row['module'],future_install_path=row['module'].replace('.','/')+'.lean',preimage=row['preimage'],exact_future_selection=row['postimage'],disposition='ALLOW_LOCAL_API_POSTIMAGE_KEEP_EIGEN_DEPENDENCY_HOLD' if row in EIG['pairs'] else 'ALLOW_LOCAL_API_POSTIMAGE_AS_SOURCE_PLAN_ONLY',source_header_count=row['source_header_count'],headers_changed=row['changed_source_headers'],ready_to_install=False,kernel_accepted=False))
allow.append(dict(module=im['module'],future_install_path=imj['target_relative_path'],preimage=gitp(imj['target_relative_path']),exact_future_selection=file(Path(im['candidate_path'])),disposition='REUSE_EXISTING_CANDIDATE_IDENTITY_ONLY_DOTS_OWNER_EXISTING_TARGET_HOLD',original_owner_registry=file(ir),source_header_count=len(ih),headers_changed=[],ready_to_install=False,kernel_accepted=False))
assert len(allow)==9 and sum(r['source_header_count'] for r in allow)==100 and sum(len(r['headers_changed']) for r in allow)==7
agg=T13/'REGISTRY.json'; ag=j(agg); assert sha(read(agg))=='0905ad5e9297acaa884c7fce527c8b4415c9a6610f26f7d8aaabf59ac34954eb'; assert len(ag['packets'])==5 and len(ag['files'])==11 and ag['ready_to_install'] is False
for g in ag['files']+[r['registry'] for r in ag['packets']]:
    b=read(T13/g['relative_path']); assert all(g[k]==v for k,v in ids(b).items())
inplan={r['module']:r for r in j(T13/'INSTALL_SELECTIONS.json')['rows']}; assert set(inplan)=={r['module'] for r in allow}
for r in allow:
    s=inplan[r['module']]; assert (s['install_path'],s['preimage_sha256'],s['selected_sha256'],s['selected_git_blob_sha1'],s['selected_bytes'],s['ready_to_install'])==(r['future_install_path'],r['preimage']['sha256'],r['exact_future_selection']['sha256'],r['exact_future_selection']['git_blob_sha1'],r['exact_future_selection']['bytes'],False)
save('ALLOWLIST.json',dict(schema='T14_P3_INDEPENDENT_SOURCE_SELECTION_ALLOWLIST_V1',status='ACCEPT_BOUNDED_STATIC_SOURCE_CHOICES_ONLY_RETAIN_ALL_RUNTIME_AND_TRANSITIVE_HOLDS',source_head=HEAD,toolchain='v4.33.0-rc1',mathlib=E4C,full_type_identity_verified=False,source_closure_complete=False,ready_to_install=False,kernel_verified=False,new_formal_credit=0,parent_status_changes=[],author_package_registries={'slice_v2':AP['registry'],'direct_predecessors':DIRECT['registry'],'eigen_v1':EIG['registry'],'imaginary_reuse':IP['registry']},superseded_reference_only=j(HERE/'STATIC_EVIDENCE.json')['slice_v1_packet']['registry'],reviewed_api_postimage_count=8,existing_source_mapping_count=1,new_math_declarations=0,source_choices=allow,other_observed_predecessors=[sr],erratum=DIRECT['frozen_prose_erratum'],evidence=[file(HERE/f) for f in ['REVIEW.md','STATIC_EVIDENCE.json','SLICE_V2_AND_IMAGINARY_JOINS.json','EIGEN_JOINS.json','DIRECT_JOINS.json','review_static_inputs.py']]))
x=j(HERE/'ALLOWLIST.json'); x['author_aggregate_registry']=file(agg); x['all_9_aggregate_choices_matched']=True; x['author_aggregate_erratum']=file(T13/'METADATA_NOTES.json'); save('ALLOWLIST.json',x)
