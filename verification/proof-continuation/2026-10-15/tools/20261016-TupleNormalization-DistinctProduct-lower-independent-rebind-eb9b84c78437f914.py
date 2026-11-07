import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json,re,base64,hashlib,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
out=root/'.lake/proof-continuation/source-reviews'
snapshot=out/'drafts/20261016-TupleNormalization-DistinctProduct-original-pre-repair.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(snapshot)=='b5eb15ed360a41c1bf4d8ad137e2988e057ffa6cf67b2cd9e84833cf61d0e1d3'
old_snap={x['path']:x for x in json.loads(snapshot.read_text())}
def uncomment(s):
    chars=list(s);i=0;depth=0;string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i):chars[i]=chars[i+1]=' ';depth+=1;i+=2
            elif s.startswith('-/',i):chars[i]=chars[i+1]=' ';depth-=1;i+=2
            else:
                if chars[i]!='\n':chars[i]=' '
                i+=1
        elif string:
            if s[i]=='\\':i+=2
            elif s[i]=='"':string=False;i+=1
            else:i+=1
        elif s.startswith('/-',i):chars[i]=chars[i+1]=' ';depth=1;i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i)
            if j<0:j=len(s)
            chars[i:j]=[' ']*(j-i);i=j
        elif s[i]=='"':string=True;i+=1
        else:i+=1
    assert depth==0
    return ''.join(chars)
def imports(s):return re.findall(r'(?m)^\s*(?:public\s+)?import\s+(\S+)',uncomment(s))
def assignment_at_top(segment):
    depth=0;i=0
    while i<len(segment)-1:
        c=segment[i]
        if c in '([{':depth+=1
        elif c in ')]}':depth-=1
        if depth==0 and segment.startswith(':=',i):return i
        i+=1
    raise AssertionError('no top level definition assignment')
def declarations(raw):
    clean=uncomment(raw)
    matches=list(re.finditer(r'(?m)^(private\s+)?(def|theorem|lemma|abbrev|axiom|opaque)\s+([^\s({:]+)',clean));ds=[]
    for i,m in enumerate(matches):
        end=matches[i+1].start() if i+1<len(matches) else len(clean)
        seg=clean[m.start():end]
        if m[2] in ['theorem','lemma']:
            proof=re.search(r':=\s*by\b',seg);assert proof is not None
            offset=proof.start();body_start=proof.end()
        else:offset=assignment_at_top(seg);body_start=offset+2
        body=re.split(r'(?m)^end(?:\s.*)?$',seg[body_start:],maxsplit=1)[0].strip()
        d={'name':m[3],'kind':m[2],'private':bool(m[1]),'start_line':clean[:m.start()].count('\n')+1,'complete_source_header':seg[:offset].strip()}
        if m[2]=='def':d['complete_definition']=seg[:offset+2]+'\n'+body
        else:d['complete_proof_body_after_by']=body
        ds.append(d)
    return ds
mathlib=Path('/home/slava/codex-lean-ve/native-packages/mathlib')
core=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux/src/lean')
api_specs=[
 (mathlib/'Mathlib/Data/Finset/Card.lean',184,211,'List.toFinset_card_le has the explicit section variable (l : List alpha); exact argument is ps.permutations'),
 (mathlib/'Mathlib/Data/List/Permutation.lean',284,289,'List.length_permutations gives factorial of the actual list length, even with repeated values'),
 (mathlib/'Mathlib/Data/List/Permutation.lean',311,316,'List.mem_permutations iff List.Perm'),
 (mathlib/'Mathlib/Data/Nat/Factors.lean',166,181,'Nat.primeFactorsList_unique handles arbitrary prime lists, retaining multiplicities'),
 (core/'Init/Data/List/Lemmas.lean',350,359,'Pinned List.mem_cons expands all cons cells; not_mem_nil and or_false remove the exact leftover nil membership'),
 (core/'Init/Data/List/Perm.lean',526,550,'List.Perm.eq_of_pairwise: canonical order plus same prime multiset gives exact ordered list equality')]
apis=[{'path':str(p),'file_sha256':sha(p),'lines':[lo,hi],'role':role,'literal_fixed_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])} for p,lo,hi,role in api_specs]
pins={x:sha(root/x) for x in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for name,hash_value in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/name)==hash_value
manifest=json.loads((root/'lake-manifest.json').read_text())
provider_checks=[]
for name in ['goldbach','mathlib']:
    p=Path('/home/slava/codex-lean-ve/native-packages')/name
    actual=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
    expected=next(x['rev'] for x in manifest['packages'] if x['name']==name)
    diff=subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
    assert expected==actual and diff.returncode==0
    provider_checks.append({'name':name,'actual_head':actual,'manifest_pin':expected,'git_diff_HEAD_tracked_exit_code':diff.returncode})
configs=[
 {'module':'ActualPrimeTupleNormalization','old':'ee2f0f12ef232b770dcc7136d8ce74f27fc830cad73ab78641fe18f1cabc5db0','new':'c5c280a89f5bb833bbfc68ffbe07fea70f43330bf2c35ab81568274dd3de2ee7','owner':'20261016-ActualPrimeTupleNormalization-first-diagnostic-root-owner-rebind.json','owner_sha':'50ba0949c81a5da884e2434a522d9dc13fcc3e494cd34e68c5401ef96d855e3a','run':'20261015T215319804371Z-ImbalancedChen.ActualPrimeTupleNormalization','count':7,'defs':2,'patch_counts':[1]},
 {'module':'ActualExtendedThirdDistinctProductHarmonic','old':'75f52840ccf119eafa31e6ba1376c4fcf1946bef0c814ef23bbe41aad6aa6064','new':'9fd24ba39eaae25f0ac8b3bfececf8644330ec1cac64ddd9bd70e04e4ce3d94c','owner':'20261016-ActualExtendedThirdDistinctProductHarmonic-first-diagnostic-root-owner-rebind.json','owner_sha':'e5cba609b9aec13bc0835b1e94a4fc83b7295fdda2c7477ef78a116ebec46548','run':'20261015T215738762823Z-ImbalancedChen.ActualExtendedThirdDistinctProductHarmonic','count':15,'defs':5,'patch_counts':[2,1]}]
reviews={
 'ActualPrimeTupleNormalization':[
 'The literal coefficient counts product fibres of the actual finite ordered-list carrier T. All lists are assumed to have m slots and prime entries; disjoint prime intervals and squarefree products are not required.',
 'For a nonempty fibre pick its actual representative ps. Prime factor uniqueness proves every qs in the same fibre is a permutation of that same prime multiset, retaining repetitions. This gives subset of ps.permutations.toFinset. The cardinal is bounded by the actual LIST length, which equals m! even if repeated values cause duplicate permutation lists. Empty fibres cost zero.',
 'The only API repair applies List.toFinset_card_le to the explicit actual list ps.permutations. The old diagnostic states precisely that this list argument was missing. There is no change to the finite inequality or coefficient domain.',
 'm! is positive for every natural m, including m=0. Thus the real normalized coefficient is in [0,1] on every n, including repeated-prime products and n outside support; abs<=1 follows from nonnegativity.',
 'Multiplying once by m! restores the actual coefficient exactly. The three-group scalar identity moves exactly the three group factorials into c, while retaining any repeated-label symmetry factor already in c. It does not assert any original policy assignment is a Cartesian box, nor supply a distribution or arithmetic mean.'
 ],
 'ActualExtendedThirdDistinctProductHarmonic':[
 'The actual selector is the original target-prime-deleted box filtered by the precise owned distinct-cell prime region. The parent proves actual strict natural order p2<p1<p0 from the two strict log-order gates; no arithmetic wall mass is discarded by a measure-zero claim.',
 'Each actual tuple has prime coordinates. On prime lists equal products imply equality of prime multisets; their canonical decreasing order makes the ordered lists equal and hence the Fin3 tuples equal. Product injectivity is proved on the actual selector, with no caller injection premise or factorial multiplicity inserted.',
 'The two revised List.mem_cons simp lines now simplify the exact residual a in [] seen in the actual failure log, by fixed List.not_mem_nil and or_false, to a=p0 or a=p1 or a=p2. They do not change primality assumptions or ordering.',
 'The representative is selected only from the actual product image; its membership and exact product are proved by choose_spec. On the image, selector injectivity recovers the uniquely original tuple. The fallback zero tuple is outside the support and is never substituted for a selected term.',
 'Strict distinct prime coordinates make their totient product exactly the actual reciprocal prime weight. The sum_image transport preserves an arbitrary signed test G of the whole original tuple, not merely a product-only test or a supremum.',
 'The explicit rewrite test is exactly G(p)=actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j) (actualPrimeTupleLog N p), with the SAME original e,h,m,j. This is beta-equivalent to the test already present on every product representative. It repairs higher-order rewrite inference only.',
 'The product harmonic sum and its prime-tuple version are equal for N>1 by actual image Fubini and the precise selector indicator. Eventual N>1 transports the already proved parent cell/compact harmonic limits. The same original retained integral and nonlinear ideal functional remain; h,e and the owned finite grid m are chosen before N.',
 'This is a finite arithmetic dictionary and harmonic limit only. It does not identify the full signed first-exit sieve coefficient, pay physical counting error, or prove full hUpper/hLower/current adopted constants.'
 ]}
result=[]
for c in configs:
    path='ImbalancedChen/'+c['module']+'.lean';p=root/path
    old=base64.b64decode(old_snap[path]['bytes_base64']);new=p.read_bytes()
    assert hashlib.sha256(old).hexdigest()==c['old'] and sha(p)==c['new']
    owner_path=out/c['owner'];assert sha(owner_path)==c['owner_sha'];owner=json.loads(owner_path.read_text())
    receipt_path=root/'.lake/proof-continuation/runs'/c['run']/'receipt.json'
    log_path=receipt_path.with_name('stdout.log');receipt=json.loads(receipt_path.read_text())
    assert receipt['status']=='FAILED' and receipt['binding']['source_sha256']==c['old'] and receipt['binding_after']['source_sha256']==c['old']
    assert sha(log_path)==owner['actual_diagnostic']['sha256']
    assert pins==receipt['binding']['pins']==receipt['binding_after']['pins']
    patched=old;patch_evidence=[]
    for patch,count in zip(owner['literal_byte_patches'],c['patch_counts']):
        a=patch['old'].encode();b=patch['new'].encode();assert patched.count(a)==count
        patched=patched.replace(a,b)
        patch_evidence.append({'old':patch['old'],'new':patch['new'],'occurrences':count})
    assert patched==new
    inverse=new
    for patch,count in reversed(list(zip(owner['literal_byte_patches'],c['patch_counts']))):
        a=patch['old'].encode();b=patch['new'].encode();assert inverse.count(b)==count
        inverse=inverse.replace(b,a)
    assert inverse==old
    old_ds=declarations(old.decode());new_ds=declarations(new.decode())
    assert len(old_ds)==len(new_ds)==c['count'] and sum(x['kind']=='def' for x in new_ds)==c['defs']
    for a,b in zip(old_ds,new_ds):
        assert (a['name'],a['kind'],a['private'],a['complete_source_header'])==(b['name'],b['kind'],b['private'],b['complete_source_header'])
        if a['kind']=='def':assert a['complete_definition']==b['complete_definition']
    assert imports(old.decode())==imports(new.decode()) and len(imports(new.decode()))==1
    parents=[]
    for imp in imports(new.decode()):
        q=root/(imp.replace('.','/')+'.lean');assert sha(q)==receipt['binding']['direct_source_sha256'][imp]
        parents.append({'module':imp,'path':str(q.relative_to(root)),'current_source_sha256':sha(q),'old_failed_receipt_direct_source_sha256':receipt['binding']['direct_source_sha256'][imp],'unchanged_parent_source':True})
    assert [(x['name'],x['complete_source_header']) for x in new_ds]==[(x['name'],x['complete_source_header']) for x in owner['all_complete_unchanged_types_and_definitions']]
    clean=uncomment(new.decode());forbidden=[]
    for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
        forbidden.extend(m.group(0) for m in re.finditer(pat,clean))
    assert not forbidden
    data={
      'schema':'independent-actual-diagnostic-proof-only-rebind-v1',
      'status':'SOURCE_ONLY_NONAUTHOR_EXACT_REBIND_NO_CONFIRMED_REMAINING_MATH_OR_FIXED_API_FINDING',
      'reviewer':'/root/lower_resume (independent of repair author /root)',
      'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
      'project_head_at_review':sys.argv[1],
      'candidate':path,'old_actual_failed_sha256':c['old'],'current_sha256':sha(p),
      'old_source_snapshot':{'path':str(snapshot.relative_to(root)),'sha256':sha(snapshot),'method':'Independent pre-repair exact bytes captured only while current old source hash matched; report uses the base64 bytes, not a Git text conversion.'},
      'actual_failure_evidence':{'receipt_path':str(receipt_path.relative_to(root)),'receipt_sha256':sha(receipt_path),'status':receipt['status'],'old_source_binding_before_after_matches':True,'stdout_path':str(log_path.relative_to(root)),'stdout_sha256':sha(log_path),'complete_stdout_read':log_path.read_text(),'old_failures_preserved':True},
      'author_rebind_evidence':{'path':str(owner_path.relative_to(root)),'sha256':sha(owner_path)},
      'literal_byte_patches_independently_checked':patch_evidence,
      'forward_old_to_current_exact_bytes':patched==new,'inverse_current_to_old_exact_bytes':inverse==old,
      'complete_types_and_definition_comparison':{'method':'Theorems use actual := by marker, not first :=; definitions use top-level assignment outside brackets. Every complete header and full definition compared old/new and with root owner report.','declaration_count':len(new_ds),'definition_count':c['defs'],'all_complete_headers_and_full_definitions_identical':True,'all_complete_current_declarations_and_proofs':new_ds},
      'direct_imports_before_after':imports(new.decode()),'direct_parents_current_binding':parents,
      'fixed_API_source_evidence':apis,
      'mathematical_review':reviews[c['module']],
      'proper_source_DAG_rebind_boundary':{'imports_identical':True,'relative_local_delta':0,'relative_foreign_delta':0,'existing_graph_shape_unchanged':True,'new_foreign_modules':[],'full_foreign_closure_walk_rerun':False,'note':'Exact proof-only changes leave all complete types, definitions, imports, constants and thresholds identical. Parent current hashes also equal the actual failed receipt. Existing proper source graph shape is unchanged; no old object is rebound by this review.'},
      'pins_fresh_and_identical_to_failed_receipt':pins,'providers_fresh_HEAD_and_tracked_source_clean':provider_checks,
      'source_forbidden_token_or_option_hits':forbidden,'findings':[],
      'acceptance_boundary':{'source_only':True,'lean_or_lake_invoked':False,'source_modified_by_reviewer':False,'objects_installed_or_rebound':False,'foreign_bootstrap':False,'pins_limits_linter_changed':False,'new_candidate_strict_pass_claimed':False,'owned_or_cache_acceptance_claimed':False,'transitive_axioms_replayed':False,'note':'Root has authorized only original 6144/j2/6656 fair retries after both author and independent reports. This review supplies exact source rebind evidence, not an elaboration or acceptance result.'}}
    dest=out/f'20261016-{c["module"]}-first-diagnostic-lower-independent-rebind.json'
    with dest.open('x',encoding='utf8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
    assert sha(p)==c['new']
    result.append({'module':c['module'],'source_sha256':sha(p),'report':str(dest.relative_to(root)),'report_sha256':sha(dest),'declarations':len(new_ds),'definitions':c['defs']})
print(json.dumps(result,indent=2))