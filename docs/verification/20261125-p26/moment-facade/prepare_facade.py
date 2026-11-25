#!/usr/bin/env python3
"""Read pinned Git sources; emit one isolated facade candidate and its evidence."""
from pathlib import Path
from functools import lru_cache
import argparse, difflib, hashlib, json, re, subprocess
from declaration_tools import declarations, header, proof_body, with_body, mask_comments, normalize

HERE=Path(__file__).resolve().parent
NS='ImbalancedChen.P2OriginalSaving19HigherMoments'
REL='ImbalancedChen/P2OriginalSaving19HigherMoments.lean'
ORIG_REL='docs/source-only/20261102-resume-30m/saving19_higher_moments/P2OriginalSaving19HigherMoments.lean'
BASE='0fa84a8bf7c3a794d29279f381c8b5b18a8d3b2d'
OLD='59ccbb110e9aceac63a5bb7030b49e0f1103993bc6b2f6fb2b49a80391b2d41e'
SPLIT='910de365b810a41d17f7781856e384512cb0080d5051c6be7045643f0004b3b1'
CORE_NAMES=['duplicateH','baryCoefficient','bumped','integratedPower','completeH','completeH_cons_succ']
GUARDS=['integratedPower_newton_guard','duplicateH_author_guard']
PREEXISTING_PROOF_CHANGES=['rationalMoment_cast','integerNewtonNumerator_spec']
SYNTAX=['integratedPower_newton_guard','binomial_normalization','integral_bary_interpolate_power','integral_interpolate_mul_power']
FROZEN={
NS+'Core':'3738b75a69892c1f9ab68a395b6394817e24a94083ca5254b38c32d73a859832',
NS+'GuardLowBoundary':'3fa7f12eb715a9aabac0c431533fbb515ad3d2512aadd8eec677c5b098486604',
'ImbalancedChen.P2OriginalSaving19MomentFiniteReindex':'ef69493b03eea3c013fe645f20f5a70b4348e64ec3c59aef1a0e325afa42e902',
NS+'Symmetry':'5425985922dae867d1a1be2903c2def751187894373d700ca3a8a62b3346e16d',
NS+'SymmetryPilot':'8cd95f3227fcbdd2172eb19df40f2553e53c34b375d45c80e20d444a131d3902',
'ImbalancedChen.P2OriginalSaving19MomentAntidiagonalSplit':'8fdac0d48e8d85b33ddc2e7c203e6275729243a76dfa67d962a25e811f806529',
NS+'NewtonStructure':'8fe12eb1fea30bf171ad999e4aebb76b25130332c8ae8937620ec5a3fd1a967e',
NS+'MomentStructure':'4c8250f09dfbd120c6e30bbbde047d5a31589b6e89713c2e2abe12a70dd6e885'}
ACCEPTED_RESULTS={
'ImbalancedChen.P2OriginalSaving19MomentAntidiagonalSplit':'a56bc9cd495ff62b894719b3e00cda16701b83092d6ce9cf142c187cd0b26eef',
NS+'NewtonStructure':'ed385164a68c18f7cee72b7a37e7c74359dd07b655e24fdefde1bb8bdba5d2c5',
NS+'MomentStructure':'364c15439312a4d6b477a1914d3ff0646502810ec46f39563d12342b6e04b3c3'}
ap=argparse.ArgumentParser()
ap.add_argument('--source-root',type=Path,default=Path('/workspace/p26-source-closure'))
ap.add_argument('--check',action='store_true')
args=ap.parse_args()
root=args.source_root.resolve()
def sha(b):return hashlib.sha256(b).hexdigest()
def path(m):return m.replace('.','/')+'.lean'
@lru_cache(None)
def git(p):return subprocess.check_output(['git','show',BASE+':'+p],cwd=root)
def emit(p,b):
    p=HERE/p
    if args.check: assert p.read_bytes()==b, str(p)
    else:
        p.parent.mkdir(parents=True,exist_ok=True)
        if not p.exists() or p.read_bytes()!=b:p.write_bytes(b)
def json_emit(p,v):emit(p,(json.dumps(v,indent=2)+'\n').encode())
def fixed(s):return s.replace('9.factorial','Nat.factorial 9')
original,baseline,core=git(ORIG_REL),git(REL),git(path(NS+'Core'))
assert sha(original)==OLD and sha(baseline)==SPLIT and sha(core)==FROZEN[NS+'Core']
od,bd,cd=map(declarations,[original.decode(),baseline.decode(),core.decode()])
assert len(od)==36 and len(bd)==30 and set(od)==set(bd)|set(CORE_NAMES)
imports=['ImbalancedChen.P2OriginalSaving19MomentFloorConsumer',NS+'MomentStructure']
prefix=''.join('import '+m+'\n' for m in imports)
candidate=re.sub(r'\A(?:import [^\n]+\n)+',prefix,baseline.decode(),count=1)
for name in GUARDS:
    old=bd[name]['text']
    assert candidate.count(old)==1
    candidate=candidate.replace(old,with_body(bd[name],' by\n  exact ProofPieces.'+name+'_structural y i k hk'),1)
assert candidate.count('9.factorial')==4
assert all(header(bd[n]).count('9.factorial')==1 for n in SYNTAX)
candidate=fixed(candidate)
new=candidate.encode();newsha=sha(new);nd=declarations(candidate)
assert set(nd)==set(bd)
rest=candidate
for name in GUARDS:rest=rest.replace(nd[name]['text'],fixed(bd[name]['text']),1)
assert rest==fixed(re.sub(r'\A(?:import [^\n]+\n)+',prefix,baseline.decode(),count=1))
assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^axiom\s',mask_comments(candidate),re.M)
assert 'set_option' not in mask_comments(candidate)
emit(REL,new)
snapshots={
'provenance/P2OriginalSaving19HigherMoments.original.lean':original,
'provenance/P2OriginalSaving19HigherMoments.base_0fa.lean':baseline,
'provenance/P2OriginalSaving19HigherMomentsCore.base_0fa.lean':core}
for p,b in snapshots.items():emit(p,b)

newall={**{n:cd[n] for n in CORE_NAMES},**nd}
baseall={**{n:cd[n] for n in CORE_NAMES},**bd}
rows=[]
for name,before in od.items():
    middle,after=baseall[name],newall[name]
    assert before['kind']==middle['kind']==after['kind'] and not before['private']
    h0,h1,h2=map(header,[before,middle,after])
    assert h0==h1
    assert fixed(h0)==h2
    if name not in SYNTAX:assert h0==h2
    else:assert h0!=h2
    if name not in GUARDS:
        if before['kind']=='theorem':
            assert proof_body(middle['text'])==proof_body(after['text'])
            if name not in PREEXISTING_PROOF_CHANGES:assert proof_body(before['text'])==proof_body(after['text'])
            else:assert proof_body(before['text'])!=proof_body(middle['text'])
        else:assert before['text']==middle['text']==after['text']
    if name not in set(GUARDS)|set(SYNTAX):
        assert middle['text']==after['text']
        if name not in PREEXISTING_PROOF_CHANGES:assert before['text']==after['text']
    row={'name':name,'kind':before['kind'],'original_git_path':ORIG_REL,'original_source_sha256':OLD,
         'current_owner':NS+'Core' if name in CORE_NAMES else NS,
         'original_statement':h0,'base_statement':h1,'candidate_statement':h2,
         'original_declaration_sha256':sha(before['text'].encode()),
         'base_declaration_sha256':sha(middle['text'].encode()),
         'candidate_declaration_sha256':sha(after['text'].encode()),
         'header_byte_equal':h0==h2,'header_equal_after_documented_syntax_repair':True,
         'declaration_byte_equal_to_original':before['text']==after['text'],
         'declaration_byte_equal_to_base':middle['text']==after['text'],
         'preexisting_original_to_base_proof_change':name in PREEXISTING_PROOF_CHANGES,
         'syntax_repair':name in SYNTAX,'proof_rewired':name in GUARDS}
    if before['kind']=='theorem':
        row.update({'original_proof_sha256':sha(proof_body(before['text']).encode()),
                    'base_proof_sha256':sha(proof_body(middle['text']).encode()),
                    'candidate_proof_sha256':sha(proof_body(after['text']).encode()),
                    'proof_byte_equal_to_original':proof_body(before['text'])==proof_body(after['text']),
                    'proof_byte_equal_to_base':proof_body(middle['text'])==proof_body(after['text'])})
    rows.append(row)
comparison={'schema':'p26_facade_original_36_contracts_v1',
 'status':'STATIC_SOURCE_COMPARISON_NOT_KERNEL_DEFINITIONAL_EQUALITY_TEST',
 'original_source_sha256':OLD,'baseline_facade_sha256':SPLIT,'candidate_facade_sha256':newsha,'baseline_commit':BASE,
 'public_contract_count':36,'facade_declarations':30,'unchanged_core_declarations':6,
 'definitions':sum(x['kind']=='def' for x in rows),'structures':sum(x['kind']=='structure' for x in rows),
 'theorems':sum(x['kind']=='theorem' for x in rows),'byte_equal_headers':sum(x['header_byte_equal'] for x in rows),
 'byte_equal_declarations_to_base':sum(x['declaration_byte_equal_to_base'] for x in rows),
 'byte_equal_theorem_proofs_to_base':sum(x.get('proof_byte_equal_to_base',False) for x in rows),
 'byte_equal_declarations_to_original':sum(x['declaration_byte_equal_to_original'] for x in rows),
 'byte_equal_theorem_proofs_to_original':sum(x.get('proof_byte_equal_to_original',False) for x in rows),
 'header_repairs':SYNTAX,'proof_rewirings':GUARDS,'preexisting_original_to_base_proof_changes':PREEXISTING_PROOF_CHANGES,'declarations':rows,
 'source_origin_paths':{'original_59cc_archive_git_path':ORIG_REL,'published_910de_facade_git_path':REL,'snapshot_commit':BASE},
 'semantic_limit':'Four original numeral-dot headers were malformed under Lean4.33. They are explicitly repaired to Nat.factorial 9. All other tokens, binders and assumptions are unchanged; no old parsed-type equality is claimed.',
 'reused_parser_source_sha256':'ddd9477c561b11743ceb441e4b79ca8a62d1198c7eceb99d425fc4f71c767ad6',
 'reused_parser_slice_sha256':'f352c104fe5fd6479f531ea354b7f81b68ec52e6bc54dee2d4e6c72e764b1893'}
assert (comparison['definitions'],comparison['structures'],comparison['theorems'])==(12,1,23)
assert (comparison['byte_equal_headers'],comparison['byte_equal_declarations_to_base'],comparison['byte_equal_theorem_proofs_to_base'])==(32,31,21)
assert (comparison['byte_equal_declarations_to_original'],comparison['byte_equal_theorem_proofs_to_original'])==(29,19)
json_emit('PUBLIC_DECLARATION_COMPARISON.json',comparison)
emit('FACADE_DIFF.patch',''.join(difflib.unified_diff(baseline.decode().splitlines(True),candidate.splitlines(True),fromfile='0fa/'+REL,tofile='candidate/'+REL)).encode())

def closure(owned):
    sources,graph,active={},{},[]
    def visit(m):
        assert m not in active,m
        if m in sources:return
        p=path(m);own=m==NS;b=owned if own else git(p)
        if not own:assert (root/p).read_bytes()==b,'Dependency differs from 0fa: '+m
        imps=[m for line in re.findall(r'^import (.+)$',mask_comments(b.decode()),re.M) for m in line.split()]
        sources[m]={'path':p,'sha256':sha(b),'bytes':len(b),'imports':imps,
                    'local_source_path':str(HERE/p if own else root/p),
                    'origin_kind':'CHANGED_FACADE_OWNER' if own else 'UNCHANGED_PUBLISHED_BASE',
                    'observed_base_commit':None if own else BASE}
        graph[m]=[x for x in imps if x.startswith('ImbalancedChen.')]
        active.append(m)
        for x in graph[m]:visit(x)
        active.pop()
    visit(NS)
    return sources,graph
sources,graph=closure(new)
old_sources,_=closure(baseline)
assert not any(re.search(r'HigherMoments(?:GuardK[0-6]I|AuthorK[0-6])',m) for m in sources)
frozen={}
for m,s in FROZEN.items():
    b=git(path(m));assert sha(b)==s and (root/path(m)).read_bytes()==b
    frozen[m]={'path':path(m),'sha256':s,'bytes':len(b),'in_candidate_closure':m in sources,
               'acceptance_basis':'Parent-reported acceptance; source bytes verified here.'}
    if m in ACCEPTED_RESULTS:
        frozen[m].update({'parent_reported_job_id':'job_1b0e5c52fcfe440b9bd27179ed7fdf14',
          'parent_reported_status':'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS',
          'parent_reported_result_sha256':ACCEPTED_RESULTS[m]})
input_doc={'schema':'p26_facade_source_inputs_v1','status':'STATIC_SOURCE_BINDING_ONLY',
 'observed_base_source_commit':BASE,'project_sources':sources,'project_import_graph':graph,
 'source_closures':{NS:sorted(sources)},'baseline_closure_count':len(old_sources),
 'candidate_closure_count':len(sources),'removed_from_closure':sorted(set(old_sources)-set(sources)),
 'added_to_closure':sorted(set(sources)-set(old_sources)),'all_unchanged_sources_match_published_base':True}
json_emit('SOURCE_INPUTS.json',input_doc)
owner={k:sources[NS][k] for k in ['path','sha256','bytes','imports','local_source_path']}
owner['status']='SOURCE_CANDIDATE_PENDING_P1_NORMAL_KERNEL_FULL_OWNED'
manifest={'schema':'p26_facade_single_owner_source_manifest_v1',
 'status':'READY_FOR_PARENT_SOURCE_PUBLICATION_NOT_FACADE_ACCEPTED',
 'baseline_sha256':SPLIT,'baseline_facade_sha256':SPLIT,'original_monolithic_sha256':OLD,
 'observed_base_source_commit':BASE,'owner_count':1,'recommended_first_order':[NS],'modules':{NS:owner},
 'source_closure_counts':{NS:len(sources)},'baseline_source_closure_counts':{NS:len(old_sources)},
 'source_inputs':{'path':str(HERE/'SOURCE_INPUTS.json'),'sha256':sha((HERE/'SOURCE_INPUTS.json').read_bytes())},
 'public_declaration_comparison':{'path':str(HERE/'PUBLIC_DECLARATION_COMPARISON.json'),'sha256':sha((HERE/'PUBLIC_DECLARATION_COMPARISON.json').read_bytes())},
 'retained_accepted_source_bindings':frozen,
 'known_preimages':{
 OLD:{'kind':'parent-reported current remote monolithic preimage','snapshot_path':str(HERE/'provenance/P2OriginalSaving19HigherMoments.original.lean'),'snapshot_bytes':len(original),'archive_git_path':ORIG_REL,'archive_git_commit':BASE,'remote_source_commit_not_claimed':True},
 SPLIT:{'kind':'published local0fa facade preimage','snapshot_path':str(HERE/'provenance/P2OriginalSaving19HigherMoments.base_0fa.lean'),'snapshot_bytes':len(baseline),'git_path':REL,'git_commit':BASE}},
 'replacement_policy':{'allowed_existing_source_sha256':[OLD,SPLIT,newsha],
   'backup_required_for_preimages':[OLD,SPLIT],
   'separate_backup_record_fields':['actual_preimage_sha256','backup_path','backup_sha256','replacement_source_sha256'],
   'new_source_allowed_idempotently':True,'unknown_preimage_action':'stop without overwriting',
   'actual_remote_replacement_performed':False,'snapshots_are_not_claimed_as_remote_installation_backups':True},
 'source_configuration':{p:{'sha256':sha(git(p)),'bytes':len(git(p))} for p in ['lean-toolchain','lake-manifest.json','lakefile.toml']},
 'change_scope':{'imports':imports,'proof_rewirings':GUARDS,'header_syntax_repairs':SYNTAX,
   'all_other_bytes_preserved':True,'all_definitions_and_structure_bytes_preserved':True,
   'strict_api_policy_changed':False},
 'actual_facade_compiled_by_this_agent':False,'frozen_suppliers_recompiled_by_this_agent':False,
 'p1_job_started_by_this_agent':False,'production_checkout_modified_by_this_agent':False,
 'parent_runner_requirement':'Single changed facade owner; preserve normal/kernel/full-owned/types/axioms validation. Back up each actual allowed preimage separately and bind source closure to new published commit.'}
json_emit('SOURCE_MANIFEST.json',manifest)
print(json.dumps({'source_sha256':newsha,'source_bytes':len(new),'manifest_path':str(HERE/'SOURCE_MANIFEST.json'),
 'manifest_sha256':sha((HERE/'SOURCE_MANIFEST.json').read_bytes()),
 'comparison_sha256':sha((HERE/'PUBLIC_DECLARATION_COMPARISON.json').read_bytes()),
 'baseline_closure':len(old_sources),'candidate_closure':len(sources),
 'public_contracts':36,'byte_equal_headers':32,'byte_equal_declarations':31,'byte_equal_proofs':21,
 'mode':'check' if args.check else 'generated_candidate_only'},indent=2))
