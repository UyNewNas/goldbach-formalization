#!/usr/bin/env python3
"""Small local U collector contract checks; later-run fixtures are synthetic."""
from pathlib import Path
from types import ModuleType
from unittest.mock import patch
import ast, copy, json, sys, unittest
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
RAW=(HERE/'collect_u_acceptance.py').read_bytes()
c=ModuleType('u_collector');c.__file__=str(HERE/'collect_u_acceptance.py')
exec(compile(RAW,c.__file__,'exec'),c.__dict__)
x=json.loads(Path('/tmp/p15-u-actual/WordCapturedResult.json').read_text())
FIRST={k:v for k,v in x.items() if k not in ('batch6','path')}
NEXT='ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy'
FAILED='ImbalancedChen.P1OriginalSingletonSmoothLicence'

def worker(result):
    return {k:v for k,v in result.items() if k not in ('worker_exit_code','all_selected_owners_accepted','dispatch_error')}

def scope(result):
    result={k:copy.deepcopy(result[k]) for k in ('targets','accepted_owners','failures','reused_complete_selected_owners',
        'selected_live_source_count','direct_import_readiness')}
    result['direct_import_readiness']=list(result['direct_import_readiness'])
    return result

def synthetic_later(complete):
    r=copy.deepcopy(FIRST)
    r.update(targets=[c.WORD,NEXT,FAILED],accepted_owners=[c.WORD,NEXT,FAILED] if complete else [c.WORD,NEXT],
        failures={} if complete else {FAILED:'synthetic failure'},reused_complete_selected_owners=[c.WORD],
        selected_live_source_count=157,worker_exit_code=0 if complete else 1,all_selected_owners_accepted=complete)
    r['acceptance_bindings'].update({m:{'module':m} for m in r['accepted_owners'] if m!=c.WORD})
    r['direct_import_readiness']={NEXT:{},FAILED:{}}
    if not complete:
        r.pop('final_stock_readiness');r['dispatch_error']='serialized worker exited 1'
    return r

class Contracts(unittest.TestCase):
    def test_unbound_holds_before_any_subprocess(self):
        with patch.object(c,'PINNED',None), patch.object(c.subprocess,'check_output',side_effect=AssertionError('must not read environment')) as proc:
            with self.assertRaisesRegex(RuntimeError,'not yet frozen'):c.collect()
            proc.assert_not_called()
    def test_actual_first_scope(self):
        self.assertTrue(c.validate_scope(FIRST,worker(FIRST),scope(FIRST)))
        self.assertEqual(FIRST['source_commit'],c.U)
        self.assertEqual(FIRST['accepted_owners'],[c.WORD])
    def test_later_both_success_and_partial(self):
        for complete in (True,False):
            r=synthetic_later(complete)
            self.assertIs(c.validate_scope(r,worker(r),scope(r)),complete)
            origins=c.accepting_runs([(FIRST,{},{}),(r,{},{})])
            self.assertEqual(origins[c.WORD],0)
            self.assertEqual(origins[NEXT],1)
            self.assertEqual(set(origins),set(r['accepted_owners']))
    def test_failure_cannot_be_promoted_or_skip_owner(self):
        r=synthetic_later(False);r['all_selected_owners_accepted']=True
        with self.assertRaises(RuntimeError):c.validate_scope(r,worker(r),scope(r))
        r=synthetic_later(False);r['accepted_owners']=[c.WORD,FAILED]
        with self.assertRaises(RuntimeError):c.validate_scope(r,worker(r),scope(r))
        r=synthetic_later(False);r['final_stock_readiness']={}
        with self.assertRaises(RuntimeError):c.validate_scope(r,worker(r),scope(r))
    def test_same_U_reuse_cannot_rebind_Word(self):
        r=synthetic_later(False);r['acceptance_bindings'][c.WORD]['module']=NEXT
        with self.assertRaises(RuntimeError):c.accepting_runs([(FIRST,{},{}),(r,{},{})])
        r=synthetic_later(False);r['reused_complete_selected_owners']=[]
        with self.assertRaises(RuntimeError):c.accepting_runs([(FIRST,{},{}),(r,{},{})])
    def test_flat_keeps_first_and_later_group_separate(self):
        runs=[]
        for i,r in enumerate((FIRST,synthetic_later(False))):
            public={k:r[k] for k in ('targets','accepted_owners','reused_complete_selected_owners','worker_exit_code',
                'all_selected_owners_accepted')}
            public.update(compiler_job='synthetic-'+str(i),original_requested_targets=r['targets'],
                failed_modules=list(r['failures']),not_accepted_modules=r['targets'][len(r['accepted_owners']):],
                not_started_modules=[],dispatch_error=r.get('dispatch_error'),original_live_source_count=r['selected_live_source_count'],
                original_final_stock_readiness={'recorded':i==0},evidence_bindings={k:{'bytes':1,'sha256':'0'*64} for k in
                    ('RESULT.json','WORKER_RESULT.json','CONTEXT_BEFORE.json','CONTEXT_AFTER.json','GIT_BEFORE.json','GIT_AFTER.json')})
            runs.append((r,{},public))
        common={'selected_owners_revalidated':[c.WORD,NEXT],'current_read_live_source_count':123,'current_read_preserved_dependency_count':121}
        a=c.flat_summary(runs,0,c.WORD,{'owner_live_source_closure_count':77,'later_same_U_reuse_run':'synthetic-run1'},common)
        b=c.flat_summary(runs,1,NEXT,{'owner_live_source_closure_count':78,'later_same_U_reuse_run':None},common)
        self.assertEqual((a['original_run'],b['original_run']),('runs/attempt-00000','runs/attempt-00001'))
        self.assertTrue(a['original_group_all_selected_owners_accepted']);self.assertFalse(b['original_group_all_selected_owners_accepted'])
        self.assertTrue(a['original_final_stock_readiness']['recorded']);self.assertFalse(b['original_final_stock_readiness']['recorded'])
        self.assertEqual(b['original_group_failed_modules'],[FAILED]);self.assertIsNone(b['later_same_source_reuse'])
        self.assertEqual(a['selected_owners_revalidated'],b['selected_owners_revalidated'])
        self.assertEqual(a['later_same_source_reuse'],runs[1][2])
    def test_no_build_or_write_operations(self):
        calls=[n for n in ast.walk(ast.parse(RAW)) if isinstance(n,ast.Call)]
        attrs={n.func.attr for n in calls if isinstance(n.func,ast.Attribute)}
        self.assertFalse(attrs & {'write_text','write_bytes','save','write_frozen','mkdir','unlink','rename','Popen','run','system','check_call'})
        commands=[n for n in calls if isinstance(n.func,ast.Attribute) and n.func.attr=='check_output']
        self.assertEqual(len(commands),1)
        self.assertEqual([ast.literal_eval(v) for v in commands[0].args[0].elts[:2]],['git','show'])
        self.assertTrue({'preflight','require_completed_existing_owner','acceptance_binding'}<=attrs)
    def test_frozen_actual_runs_and_owner_origins(self):
        meta=json.loads(Path('/tmp/p15-u-actual/ACTUAL_U_METADATA.json').read_text())
        records=[]
        for index in (0,1):
            raw=Path('/tmp/p15-u-actual/attempt-%05d-RESULT.json'%index).read_bytes()
            result=json.loads(raw);w=worker(result)
            wr=(json.dumps(w,ensure_ascii=False,sort_keys=True,indent=2)+'\n').encode()
            frozen=c.PINNED['runs'][index]
            self.assertEqual(c.raw_fp(raw),frozen['pins']['RESULT.json'])
            self.assertEqual(c.raw_fp(wr),frozen['pins']['WORKER_RESULT.json'])
            self.assertEqual(frozen['pins'],{k:c.pin(v) for k,v in meta['runs']['attempt-%05d'%index].items()})
            self.assertIs(c.validate_scope(result,w,frozen['scope']),index==0)
            records.append((result,{},{}))
        self.assertEqual(c.accepting_runs(records),{c.WORD:0,NEXT:1})
        self.assertEqual(c.PINNED['current_read_live_source_count'],139)
        self.assertEqual(c.PINNED['current_read_preserved_dependency_count'],137)
        for module,row in c.PINNED['owners'].items():
            original=meta['accepted_owners'][module]
            self.assertEqual((row['owned_count'],row['public_count']),(15,15))
            self.assertEqual(row['source'],c.pin(original['source']))
            self.assertEqual(row['audit_result'],c.pin(original['audit_result']))
            self.assertEqual(row['audit_id'],Path(original['audit_plan']['path']).parent.name)
            binding=records[row['accepting_run_index']][0]['acceptance_bindings'][module]
            self.assertEqual(binding['normal_receipt'],original['normal'])
            self.assertEqual(binding['audits'],[{'plan':original['audit_plan'],'result':original['audit_result']}])
    def test_failed_source_setup_and_missing_slots_fixed(self):
        meta=json.loads(Path('/tmp/p15-u-actual/ACTUAL_U_METADATA.json').read_text())
        failure=meta['failures'][FAILED]
        observed={str(Path(k).relative_to(c.PROJECT)):c.pin(v) if v else None for k,v in failure['artifact_slots'].items()}
        self.assertEqual(c.PINNED['failed_artifact_observations'],{FAILED:observed})
        self.assertEqual((len(observed),sum(v is not None for v in observed.values())),(21,1))
        for key in ('source','normal_metadata'):
            self.assertEqual(c.PINNED['extra_pins'][failure[key]['path']],c.pin(failure[key]))
        for path,value in failure['artifact_slots'].items():
            if value:self.assertEqual(c.PINNED['extra_pins'][path],c.pin(value))
        self.assertEqual(c.PINNED['extra_pins'][meta['word_install']['path']],c.pin(meta['word_install']))
    def test_changed_original_pin_rejected_before_json_read(self):
        for index in (0,1):
            fixed=c.PINNED['runs'][index]
            def wrong(path):
                expected=c.DRIVER_FP if path.name=='executed-driver.py' else fixed['pins'][path.name]
                return {'path':str(path),**expected,**({'sha256':'0'*64} if path.name=='RESULT.json' else {})}
            with patch.object(c,'bind',wrong):
                with self.assertRaisesRegex(RuntimeError,'original U run pins differ'):
                    c.read_run(None,None,None,index,fixed)

if __name__=='__main__':unittest.main(verbosity=2)
