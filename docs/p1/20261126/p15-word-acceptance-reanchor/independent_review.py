#!/usr/bin/env python3
"""Independent local U delta checks. Does not run the builder, Git, Lean, or cloud."""
from pathlib import Path
from types import ModuleType, SimpleNamespace
from unittest.mock import patch
import argparse, ast, copy, hashlib, json, sys
sys.dont_write_bytecode = True
BASE = Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
OUT = Path('/tmp/p15-entrypoint-u')
S = '18e41c4a1c01ca22e5537acb934e04891279b616'
R = '0935516b9bd978a61248c81b59776d1eb47f6044'
FAMILY = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
WORD = 'ImbalancedChen.P5IndependentPrimeSourceWordDictionary'
checks = []

def fp(raw):
    return {'bytes':len(raw), 'sha256':hashlib.sha256(raw).hexdigest()}

def check(name, value):
    if not value: raise AssertionError(name)
    checks.append(name)

def reject(name, fn):
    try: fn()
    except (ValueError, RuntimeError, KeyError, AssertionError): checks.append(name)
    else: raise AssertionError('accepted negative: ' + name)

def load(raw, name, path):
    m = ModuleType(name); m.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), m.__dict__)
    return m

def functions(raw):
    text = raw.decode()
    return {n.name:ast.get_source_segment(text,n) for n in ast.parse(text).body if isinstance(n,ast.FunctionDef)}

def closure(graph, roots):
    result, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m not in result:
            result.add(m); todo.extend(graph[m])
    return result

def canonical(value):
    return (json.dumps(value,ensure_ascii=False,sort_keys=True,indent=2)+'\n').encode()

def main(anchor):
    sp = BASE/'entrypoint-s/run_selected.py'; up = BASE/'entrypoint-u/run_selected.py'
    sr, ur = sp.read_bytes(), up.read_bytes()
    sm = json.loads(Path('/tmp/p15-entrypoint-s/SOURCE_MANIFEST.json').read_text())
    mr = (OUT/'SOURCE_MANIFEST.json').read_bytes(); manifest = json.loads(mr)
    public_raw = Path('/tmp/p15-t-publication/FAMILY_S_PUBLIC_ACCEPTANCE.json').read_bytes()
    public = json.loads(public_raw)
    check('exact_S_base', fp(sr)=={'bytes':130643,'sha256':'fdd3218c5e5d3169bd42ca8ba1953c8378f9b2c436107ed165a13068a48d2c55'})
    check('actual_flat_pin', fp(public_raw)=={'bytes':13244,'sha256':'12f18cc8e6160e645c17a7b7f5ae94f616d7c940a97289080698aaaee973fcfa'})
    s = load(sr,'old_S',sp); u = load(ur,'new_U',up)
    sf, uf = functions(sr), functions(ur)
    check('only_three_added_functions', set(uf)-set(sf)=={'family_s_prior_source_binding','require_family_s_prior_scope','retained_family_s_prior_target'})
    changed = {n for n in sf if sf[n]!=uf[n]}
    check('44_of_46_old_functions_byte_identical', len(sf)==46 and changed=={'source_manifest','preflight'})
    source_body = uf['source_manifest'].replace(' | set(FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS)','')
    source_body = source_body.replace("        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:\n            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n                    'Family@S prior classification differs: ' + module)\n            family_s_prior_source_binding(s, graph, sources, module, prior)\n            continue\n",'')
    preflight_body = uf['preflight'].replace("        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:\n            retained_family_s_prior_target(s, spec, module)\n        elif module in Q_PREVIOUSLY_ACCEPTED_TARGETS:", "        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:")
    check('two_dispatch_functions_restore_exact_S', source_body==sf['source_manifest'] and preflight_body==sf['preflight'])
    check('fixed_T_anchor_and_manifest_pin', u.SOURCE_ANCHOR==manifest['source_anchor_commit']==anchor and u.MANIFEST_SHA==fp(mr)['sha256'])
    check('all_359_other_sources_and_all_imports_unchanged',
        {k:v for k,v in manifest['project_sources'].items() if k!=WORD}=={k:v for k,v in sm['project_sources'].items() if k!=WORD} and
        all(v['all_imports']==sm['project_sources'][k]['all_imports'] and v['imports']==sm['project_sources'][k]['imports'] for k,v in manifest['project_sources'].items()))
    check('seven_old_prior_identities_byte_equivalent',
        {k:v for k,v in manifest['previously_accepted_targets'].items() if k!=FAMILY}==sm['previously_accepted_targets'] and
        {k:v for k,v in u.PREVIOUSLY_ACCEPTED_TARGETS.items() if k!=FAMILY}==s.PREVIOUSLY_ACCEPTED_TARGETS)
    check('303_policy_19_P3_17_suppliers_unchanged', all(manifest[k]==sm[k] for k in
        ('fixed_dependencies','unaccepted_p3_dependencies','unaccepted_p3_policy','accepted_supplier_groups','accepted_suppliers')) and
        len(manifest['fixed_dependencies'])==303 and len(manifest['unaccepted_p3_dependencies'])==19)
    graph = {k:v['imports'] for k,v in manifest['project_sources'].items()}; sources = {k:v['sha256'] for k,v in manifest['project_sources'].items()}
    guide = manifest['selection_guidance']; later = guide['subsequent_10_targets']
    check('first77_76_later157_147_watch160', (len(closure(graph,[WORD])),len(closure(graph,[WORD])-{WORD}),
        len(closure(graph,later)),len(closure(graph,later)-set(later)),len(closure(graph,later)|set(u.TARGETS)))==(77,76,157,147,160))
    check('exact_remaining10', later==[m for m in sm['selection_guidance']['subsequent_11_targets'] if m!=FAMILY] and len(later)==10)
    check('original_21_root_whitelist_unchanged', u.TARGETS==s.TARGETS==manifest['targets'])
    for module in u.PREVIOUSLY_ACCEPTED_TARGETS:
        reject('prior_cannot_be_selected:'+module, lambda m=module:u.selection([m]))
    check('Word_selection_allowed',u.selection([WORD])==[WORD])
    word = (BASE/'P5IndependentPrimeSourceWordDictionary.lean').read_bytes()
    repair = json.loads(Path('/tmp/p15-s-actual/WORD_REPAIR_CANDIDATE.json').read_text())
    check('Word_candidate_and_T_provenance', fp(word)==repair['after']=={k:manifest['project_sources'][WORD][k] for k in ('bytes','sha256')} and
        manifest['target_source_origins'][WORD]['canonical_source']['commit']==anchor and
        manifest['target_source_origins'][WORD]['source_reviews'][-1]['commit']==anchor)
    prior = manifest['previously_accepted_targets'][FAMILY]
    check('Family_public_bound_to_T_owner_bound_to_S',prior['source_commit']==S and prior['historical_group']['public_evidence']==
        {'commit':anchor,'path':'docs/p1/20261125/p15-current-public-acceptance/FAMILY_S_PUBLIC_ACCEPTANCE.json',**fp(public_raw)})
    captures=[]
    for name in ('FamilyCapturedResult.json','Later11CapturedResult.json'):
        x=json.loads((Path('/tmp/p15-s-actual')/name).read_text());captures.append({k:v for k,v in x.items() if k not in ('batch6','path')})
    workers=[{k:v for k,v in x.items() if k not in ('worker_exit_code','all_selected_owners_accepted','dispatch_error')} for x in captures]
    u.require_family_s_prior_scope(FAMILY,prior,public,captures[0],workers[0]); checks.append('actual_family_public_and_first_scope_accepted')
    for key,value in [('source_commit',anchor),('current_read_live_source_count',157),('current_read_preserved_dependency_count',147),
                      ('selected_owners_revalidated',[WORD]),('original_group_all_selected_owners_accepted',False)]:
        bad=copy.deepcopy(public);bad[key]=value
        reject('public_scope_negative:'+key,lambda b=bad:u.require_family_s_prior_scope(FAMILY,prior,b,captures[0],workers[0]))
    for key,value in [('source_commit',anchor),('owned_count',28),('receipt_rebound_to_current_commit',True),
                      ('later_same_S_reuse_run',None)]:
        bad=copy.deepcopy(public);bad['owners'][FAMILY][key]=value
        reject('owner_identity_negative:'+key,lambda b=bad:u.require_family_s_prior_scope(FAMILY,prior,b,captures[0],workers[0]))
    bad=copy.deepcopy(public);bad['owners'][FAMILY]['receipt_bindings']['normal']['path']='unexpected'
    reject('receipt_fingerprint_must_be_flat',lambda:u.require_family_s_prior_scope(FAMILY,prior,bad,captures[0],workers[0]))
    helpers=SimpleNamespace(h=SimpleNamespace(closure=closure))
    u.family_s_prior_source_binding(helpers,graph,sources,FAMILY,prior);checks.append('Family_exact_source_and_closure75')
    bad_sources={**sources,FAMILY:'0'*64}
    reject('wrong_Family_source',lambda:u.family_s_prior_source_binding(helpers,graph,bad_sources,FAMILY,prior))
    bad_graph={**graph,FAMILY:[*graph[FAMILY],WORD]}
    reject('changed_Family_closure',lambda:u.family_s_prior_source_binding(helpers,bad_graph,sources,FAMILY,prior))

    # Only new orchestration is isolated below; unchanged retained_read/audit APIs are not rerun.
    base=u.ROOT/S; first=base/'runs/attempt-00000'; second=base/'runs/attempt-00001'
    records={str(first/'RESULT.json'):canonical(captures[0]),str(first/'WORKER_RESULT.json'):canonical(workers[0]),
        str(second/'RESULT.json'):canonical(captures[1]),str(second/'WORKER_RESULT.json'):canonical(workers[1])}
    expected={str(first/'RESULT.json'):public['original_result'],str(first/'WORKER_RESULT.json'):public['original_worker_result']}
    expected.update({str(second/k):v for k,v in u.FAMILY_S_LATER_PINS.items()})
    for stem,pair in public['original_context_pairs'].items():
        for side in ('before','after'):
            path=str(first/(stem+'_'+side.upper()+'.json'));expected[path]=pair[side];records[path]=b'isolated-equal-context'
    for stem in ('CONTEXT','GIT'):
        for side in ('BEFORE','AFTER'):records[str(second/(stem+'_'+side+'.json'))]=b'isolated-equal-context'
    stock=public['original_final_stock_readiness']
    expected[stock['command']['path']]={k:stock['command'][k] for k in ('bytes','sha256')}
    expected[stock['log']['path']]={k:stock['log'][k] for k in ('bytes','sha256')}
    records[stock['command']['path']]=canonical(captures[0]['final_stock_readiness']);records[stock['log']['path']]=b'isolated-stock-log'
    # Command/context/log bytes are isolation stand-ins; only these four raw JSON
    # captures have independently established original serialization and SHA.
    for path in (str(first/'RESULT.json'),str(first/'WORKER_RESULT.json'),str(second/'RESULT.json'),str(second/'WORKER_RESULT.json')):
        check('actual_original_pin:'+path.rsplit('/',2)[-2]+'/'+Path(path).name,fp(records[path])==expected[path])
    binding=captures[0]['acceptance_bindings'][FAMILY]
    def exercise(fault=None):
        spec=SimpleNamespace(manifest=manifest,active=closure(graph,[WORD]),selected={WORD},graph=graph,sources=sources,
            supplier_evidence={},dependency_pins={},retained_inputs={})
        state={'audited':False}; files=copy.deepcopy(records)
        if fault=='later_binding':
            x=copy.deepcopy(captures[1]);x['acceptance_bindings'][FAMILY]['module']=WORD;files[str(second/'RESULT.json')]=canonical(x)
        if fault=='later_promoted':
            x=copy.deepcopy(captures[1]);x['all_selected_owners_accepted']=True;files[str(second/'RESULT.json')]=canonical(x)
        def read(_s,_spec,path,wanted=None):
            assert wanted==expected[str(path)],'unexpected original path/pin'
            _spec.retained_inputs[str(path)]=wanted
            return files[str(path)]
        def artifacts(_s,module):
            assert module==FAMILY
            result=copy.deepcopy(binding['all_observed_target_artifacts'])
            if fault=='full21' or (fault=='post_audit' and state['audited']):result[next(iter(result))]={'bytes':1,'sha256':'0'*64}
            return result
        def original_snapshot(project,module):
            assert project==u.PROJECT and module==FAMILY
            return {} if fault=='source_plus_five' else binding['source_plus_five_outputs']
        def generic(_s,shadow,module,validate_live=False):
            assert validate_live is True and shadow.manifest['accepted_suppliers'][module]['source_commit']==S
            assert shadow.manifest['accepted_supplier_groups']['family_s']==prior['historical_group']
            state['audited']=True
            shadow.supplier_evidence[module]={'source_commit':S,'selected_supplier_live_closure_count':75,
                'original_group_worker_exit_code':0,'owned_count':27,'public_count':27,
                'audit_plan':{'path':public['owners'][FAMILY]['receipt_paths']['audit_plan']}}
            return {'isolated_original_audit':True}
        hh=SimpleNamespace(closure=closure,guard=lambda lane,args:captures[0]['final_stock_readiness']['argv'][:4]+args)
        helper=SimpleNamespace(h=hh,d=SimpleNamespace(snapshot=original_snapshot))
        with patch.object(u,'published_binding',return_value=public_raw),patch.object(u,'retained_read',read),\
             patch.object(u,'module_artifacts',artifacts),patch.object(u,'retained_owner',generic):
            value=u.retained_family_s_prior_target(helper,spec,FAMILY)
        assert spec.dependency_pins[FAMILY]==binding['all_observed_target_artifacts'] and state['audited']
        return value
    check('retained_Family_orchestration_positive',exercise()=={'isolated_original_audit':True})
    for fault in ('later_binding','later_promoted','full21','source_plus_five','post_audit'):
        reject('retained_Family_negative:'+fault,lambda f=fault:exercise(f))
    check('production_candidates_unchanged_during_review',up.read_bytes()==ur and (OUT/'SOURCE_MANIFEST.json').read_bytes()==mr)
    return dict(schema='p15_U_independent_delta_review_v1',source_anchor=anchor,runner=fp(ur),manifest=fp(mr),
        status='PASS_TARGETED_LOCAL_REVIEW',check_count=len(checks),checks=checks,
        old_89_or_116_suites_rerun=False,new_lean_acceptance=False,whole_P1_5_complete=False,
        limitation='New adapter isolated orchestration uses stand-ins for unchanged retained_read/full-audit helpers; no cloud acceptance is claimed.')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--source-anchor',required=True);args=parser.parse_args()
    report=main(args.source_anchor)
    (OUT/'INDEPENDENT_REVIEW.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='checks'},ensure_ascii=False))
