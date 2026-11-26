from pathlib import Path
from types import ModuleType, SimpleNamespace as NS
import ast, copy, hashlib, json, tempfile, unittest

LOCAL=Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
BASE=Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')
COLLECTOR=LOCAL/'collect_q_acceptance.py'

def load(path,name):
    m=ModuleType(name);m.__file__=str(path)
    exec(compile(path.read_bytes(),str(path),'exec'),m.__dict__)
    return m

m=load(COLLECTOR,'collector_under_test')
driver=load(LOCAL/'entrypoint/run_selected.py','actual_Q_driver')
manifest=json.loads((LOCAL/'entrypoint/SOURCE_MANIFEST.json').read_bytes())
graph={k:r['imports'] for k,r in manifest['project_sources'].items()}
api=load(BASE/'docs/p1/20261125/batch13-repairs/run_repairs.py','pinned_api')
h=load(BASE/api.HELPER,'pinned_h')
d=load(BASE/api.PRIMITIVES,'pinned_d')
assert m.raw_fp((LOCAL/'entrypoint/run_selected.py').read_bytes())==m.DRIVER_FP
assert m.raw_fp((LOCAL/'entrypoint/SOURCE_MANIFEST.json').read_bytes())==m.MANIFEST_FP
assert hashlib.sha256((BASE/'docs/p1/20261125/batch13-repairs/run_repairs.py').read_bytes()).hexdigest()==driver.API_SHA
for p in (api.HELPER,api.PRIMITIVES):assert hashlib.sha256((BASE/p).read_bytes()).hexdigest()==api.PINS[p]
s=NS(api=api,h=h,d=d)
ACTUAL_RUN_PINS=copy.deepcopy(m.RUN_PINS)

def records(index):
    targets,accepted,reused=([m.ALLK],[m.ALLK],[]) if index==0 else (m.REMAINING,m.ACCEPTED,[m.ALLK])
    worker={'source_commit':m.Q,'targets':targets,'accepted_owners':accepted,
            'failures':{} if index==0 else {m.FAMILY:'normal failed/scope differs: '+m.FAMILY},
            'acceptance_bindings':{x:{'fixture_owner':x} for x in accepted},
            'reused_complete_selected_owners':reused,'direct_import_readiness':
            {x:{} for x in ([m.ALLK] if index==0 else [m.ADMISSIBLE,m.FAMILY])},
            'published_source_count':360,'selected_live_source_count':73 if index==0 else 157}
    for k in ('whole_P1_complete','whole_P1_5_complete','accepted_supplier_recompile_requested',
              'dependency_rebuild_requested','old_receipts_rebound','old_P3_REUSE_changed'):worker[k]=False
    if index==0:worker['final_stock_readiness']={}
    result=copy.deepcopy(worker);result['worker_exit_code']=index;result['all_selected_owners_accepted']=index==0
    if index==1:result['dispatch_error']='serialized worker exited 1'
    return result,worker

class Tests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='q-collector-',dir='/tmp');self.addCleanup(self.tmp.cleanup)
        self.oldroot=m.ROOT;m.ROOT=Path(self.tmp.name);self.addCleanup(setattr,m,'ROOT',self.oldroot)
        self.oldpins=copy.deepcopy(m.RUN_PINS);self.addCleanup(setattr,m,'RUN_PINS',self.oldpins)
    def freeze(self,index,requested=None):
        run=m.ROOT/m.Q/'runs'/('attempt-%05d'%index);run.mkdir(parents=True)
        result,worker=records(index)
        requested=requested if requested is not None else ([m.ALLK] if index==0 else manifest['selection_guidance']['subsequent_13_targets'])
        context={'committed_inputs':{'source_commit':m.Q,'source_anchor_commit':m.P,'selected_targets':requested}}
        if index==0:
            log=run/'final-stock-readiness.log';log.write_bytes(b'isolated successful readiness fixture\n')
            stock={'exit_code':0,'actual_built_modules':[],'actual_failed_modules':[],'cwd':str(m.PROJECT),
                   'argv':h.guard(0,['lake','--no-build','build','+'+m.ALLK+':olean']),
                   'log':str(log),'log_bytes':m.file_fp(log)['bytes'],'log_sha256':m.file_fp(log)['sha256']}
            worker['final_stock_readiness']=stock;result['final_stock_readiness']=stock
            (run/'final-stock-readiness-command.json').write_text(json.dumps(stock))
        (run/'executed-driver.py').write_bytes((LOCAL/'entrypoint/run_selected.py').read_bytes())
        files={'RESULT.json':result,'WORKER_RESULT.json':worker,'CONTEXT_BEFORE.json':context,'CONTEXT_AFTER.json':context,
               'GIT_BEFORE.json':{'head':'isolated','status_hex':''},'GIT_AFTER.json':{'head':'isolated','status_hex':''}}
        for name,data in files.items():(run/name).write_text(json.dumps(data))
        m.RUN_PINS[index]={name:m.file_fp(run/name) for name in ('RESULT.json','WORKER_RESULT.json')}
        return run
    def test_two_real_shapes_and_ten_not_started(self):
        for index in (0,1):
            self.freeze(index)
            before=m.tree_inventory(m.ROOT/m.Q)
            result,context,public=m.read_run(driver,s,graph,index)
            self.assertEqual(m.tree_inventory(m.ROOT/m.Q),before)
            self.assertEqual(public['worker_exit_code'],index)
            self.assertEqual(public['not_started_modules'],[] if index==0 else m.REMAINING[3:])
            self.assertEqual(len(public['not_started_modules']),0 if index==0 else 10)
    def test_request_order_is_distinct_and_original_compile_order_used(self):
        req=manifest['selection_guidance']['subsequent_13_targets']
        self.assertNotEqual(req,m.REMAINING)
        self.assertEqual(d.compile_order([],req,graph),m.REMAINING)
        self.freeze(1,req)
        _,_,public=m.read_run(driver,s,graph,1)
        self.assertEqual(public['original_requested_targets'],req)
        self.assertEqual(public['targets'],m.REMAINING)
    def test_duplicate_request_rejected(self):
        self.freeze(1,m.REMAINING+[m.ALLK])
        with self.assertRaises((RuntimeError,ValueError)):m.read_run(driver,s,graph,1)
    def test_partial_cannot_be_relabelled_success(self):
        r,w=records(1);r['all_selected_owners_accepted']=True
        with self.assertRaises(RuntimeError):m.validate_scope(r,w,1)
    def test_prefix_extension_rejected(self):
        r,w=records(1)
        for record in (r,w):record['accepted_owners']=[*m.ACCEPTED,m.FAMILY]
        with self.assertRaises(RuntimeError):m.validate_scope(r,w,1)
    def test_wrong_target_order_rejected(self):
        r,w=records(1)
        for record in (r,w):record['targets']=[m.ADMISSIBLE,m.ALLK,*m.REMAINING[2:]]
        with self.assertRaises(RuntimeError):m.validate_scope(r,w,1)
    def test_missing_AllK_reuse_rejected(self):
        r,w=records(1)
        for record in (r,w):record['reused_complete_selected_owners']=[]
        with self.assertRaises(RuntimeError):m.validate_scope(r,w,1)
    def test_partial_final_stock_invention_rejected(self):
        r,w=records(1)
        for record in (r,w):record['final_stock_readiness']={}
        with self.assertRaises(RuntimeError):m.validate_scope(r,w,1)
    def test_worker_disagreement_rejected(self):
        r,w=records(1);w['arbitrary_extra_field']='different'
        with self.assertRaises(RuntimeError):m.validate_scope(r,w,1)
    def test_context_change_rejected(self):
        run=self.freeze(1);(run/'GIT_AFTER.json').write_text('{}')
        with self.assertRaises(RuntimeError):m.read_run(driver,s,graph,1)
    def test_source_commit_rebinding_rejected(self):
        r,w=records(1)
        for record in (r,w):record['source_commit']=m.P
        with self.assertRaises(RuntimeError):m.validate_scope(r,w,1)
    def test_current_scope74_72_and_no_compiler_or_mutator_call(self):
        active=h.closure(graph,m.ACCEPTED)
        self.assertEqual(len(active),74);self.assertEqual(len(active-set(m.ACCEPTED)),72)
        self.assertNotIn(m.FAMILY,active)
        self.assertEqual(d.compile_order([],m.ACCEPTED,graph),m.ACCEPTED)
        tree=ast.parse(COLLECTOR.read_text());attrs={n.func.attr for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)}
        self.assertFalse(attrs&{'save','write_frozen','attempt','install_sources','run_owner','worker','normal_one','audit','run','Popen'})
        self.assertTrue({'preflight','require_completed_existing_owner','acceptance_binding','snapshot'}<=attrs)
    def test_two_current_source_pins(self):
        self.assertEqual(m.raw_fp((LOCAL/'Part3AllKLambdaChartCorrection.lean').read_bytes()),m.SOURCE_PINS[m.ALLK])
        self.assertEqual(m.raw_fp((BASE/h.module_path(m.ADMISSIBLE)).read_bytes()),m.SOURCE_PINS[m.ADMISSIBLE])
    def test_actual_captured_results_match_all_four_cloud_pins(self):
        base=Path('/tmp/p15-q-evidence')
        captured=[json.loads((base/'AllK_final.json').read_bytes()),next(r for r in json.loads((base/'Q_later_records.json').read_bytes()) if r.get('batch6')=='P15_CURRENT_CORRECTIONS_RESULT')]
        for i,value in enumerate(captured):
            r={k:v for k,v in value.items() if k not in ('batch6','path')}
            w={k:v for k,v in r.items() if k not in ('worker_exit_code','all_selected_owners_accepted','dispatch_error')}
            for name,record in (('RESULT.json',r),('WORKER_RESULT.json',w)):
                self.assertEqual(m.raw_fp((json.dumps(record,sort_keys=True,indent=2)+'\n').encode()),ACTUAL_RUN_PINS[i][name])
            m.validate_scope(r,w,i)
    def test_flat_single_owner_maps_and_generic_plain_fingerprints(self):
        runs=[]
        for index in (0,1):
            self.freeze(index);runs.append(m.read_run(driver,s,graph,index))
        path=Path(self.tmp.name)/'receipt-fixture';path.write_bytes(b'fingerprint fixture\n')
        fingerprint=m.file_fp(path)
        owners={owner:{'source_commit':m.Q,'source_sha256':m.SOURCE_PINS[owner]['sha256'],
            'receipt_bindings':{key:fingerprint for key in ('normal','audit_plan','audit_result','owned_exports','owned_log','reused_normal_evidence')},
            'owner_live_source_closure_count':len(h.closure(graph,[owner]))} for owner in m.ACCEPTED}
        for i,owner in enumerate(m.ACCEPTED):
            flat=m.flat_summary(owner,i,runs,owners)
            self.assertEqual(set(flat['owners']),{owner})
            self.assertEqual(flat['compiler_job'],m.JOBS[i])
            self.assertEqual(flat['original_run'],'runs/attempt-%05d'%i)
            self.assertEqual(flat['selected_owners_revalidated'],m.ACCEPTED)
            self.assertEqual((flat['current_read_live_source_count'],flat['current_read_preserved_dependency_count']),(74,72))
            self.assertEqual(flat['owner_live_source_closure_count'],73 if i==0 else 70)
            self.assertEqual(set(flat['original_result']),{'bytes','sha256'})
            for fp in flat['owners'][owner]['receipt_bindings'].values():
                self.assertEqual(set(fp),{'bytes','sha256'})
                self.assertEqual(driver.retained_read(s,NS(retained_inputs={}),path,fp),path.read_bytes())
            self.assertEqual(flat['original_group_accepted_owners'],[m.ALLK] if i==0 else m.ACCEPTED)
            self.assertEqual(flat['original_group_reused_complete_selected_owners'],[] if i==0 else [m.ALLK])
            self.assertEqual(flat['original_group_failed_modules'],[] if i==0 else [m.FAMILY])

if __name__=='__main__':unittest.main(verbosity=2)
