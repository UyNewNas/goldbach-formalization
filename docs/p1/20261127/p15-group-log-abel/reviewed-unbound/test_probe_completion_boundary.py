"""In-memory adversarial receipt tests; no Lean or formal credit."""
import copy
import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace
import unittest

HERE=Path(__file__).parent
spec=importlib.util.spec_from_file_location('group_adapter',HERE/'run_group_log.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class ProbeCompletionBoundary(unittest.TestCase):
    def setUp(self):
        self.run=Path('/workspace/p15-in-memory-test/attempt-00000')
        self.state='/workspace/p15-in-memory-test/state.json'
        self.raw={self.state:b'synthetic runtime fixture'}
        self.source=b'synthetic source fixture'
        self.raw[str(self.run/m.NAME)]=self.source
        self.raw[str(self.run/'probe_driver.py')]=b'synthetic driver fixture'
        self.raw[str(self.run/'probe.log')]=b'synthetic probe log\n'
        self.raw[str(self.run/'serialized-probe.log')]=b'synthetic serializer log\n'
        guard=lambda lane,cmd:['python3','guard','--state',self.state]+cmd
        serialize=lambda lane,receipt,cmd:['python3','serialize','--state',self.state,'--receipt',str(receipt)]+cmd
        self.s=SimpleNamespace(h=SimpleNamespace(guard=guard,serialize=serialize),api=SimpleNamespace(read_json=lambda p:json.loads(self.raw[str(p)])))
        worker=['python3','-B',str(self.run/'probe_driver.py'),'--worker']
        def command(argv,name):
            b=self.raw[str(self.run/(name+'.log'))]
            return {'argv':argv,'cwd':str(m.PROJECT),'exit_code':0,'actual_built_modules':[],'actual_failed_modules':[],
                    'log':str(self.run/(name+'.log')),'log_bytes':len(b),'log_sha256':m.digest(b)}
        self.result={'schema':'p15_original_group_log_abel_probe_v1','source_base':m.BASE,'original_source_path':m.ORIGINAL_PATH,
            'original_source_sha256':m.ORIGINAL_SHA,'source_sha256':m.digest(self.source),'source_bytes':len(self.source),
            'exit_code':0,'probe_passed':True,'output_object_requested':False,'new_formal_credit':0,'whole_P1_5_complete':False,
            'command':command(guard(0,['lake','--no-build','env','lean',str(self.run/m.NAME)]),'probe')}
        self.outer=command(serialize(0,self.run/'LANE.json',worker),'serialized-probe')
        self.lane={'status':'VALIDATION_LANE_FINISHED','exit_code':0,'argv':worker,'state':self.state,
            'state_sha256':m.digest(self.raw[self.state]),'no_compiler_guard_runtime_or_memory_limit_changes':True,
            'whole_chain_including_original_checker_serialized':True}
        for n in ('PRESERVED_BEFORE.json','PRESERVED_AFTER.json','GIT_BEFORE.json','GIT_AFTER.json'):
            self.raw[str(self.run/n)]=b'{}'

    def execute(self):
        for name,obj in [('PROBE_RESULT.json',self.result),('serialized-probe-command.json',self.outer),('LANE.json',self.lane)]:
            self.raw[str(self.run/name)]=json.dumps(obj,sort_keys=True).encode()
        result=self.raw[str(self.run/'PROBE_RESULT.json')]
        m.INPUTS={'source_sha256':m.digest(self.source),'source_bytes':len(self.source),'failed_probes':[],
            'probe':{'directory':str(self.run),'job_id':'SYNTHETIC_TEST_ONLY','result_sha256':m.digest(result),'result_bytes':len(result),
                     'driver_sha256':m.digest(self.raw[str(self.run/'probe_driver.py')])}}
        old_regular,old_git=m.regular,m.git
        m.regular=lambda p:self.raw[str(p)]
        m.git=lambda commit,path:self.raw[str(self.run/Path(path).name)]
        try:return m.verified_probe('a'*40,self.source,self.s)
        finally:m.regular,m.git=old_regular,old_git

    def test_completed_outer_control(self):
        self.assertEqual(self.execute()['job_id'],'SYNTHETIC_TEST_ONLY')

    def test_worker_success_outer_failure_rejected(self):
        self.outer['exit_code']=1
        with self.assertRaisesRegex(ValueError,'serializer did not finish'):self.execute()

    def test_worker_success_incomplete_lane_rejected(self):
        self.lane['status']='VALIDATION_LANE_STARTED'
        with self.assertRaisesRegex(ValueError,'lane is incomplete'):self.execute()

    def test_different_runtime_lane_rejected(self):
        self.lane['state_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'lane is incomplete'):self.execute()

    def test_dependency_build_in_outer_rejected(self):
        self.outer['actual_built_modules']=[m.DEPENDENCY]
        with self.assertRaisesRegex(ValueError,'serializer did not finish'):self.execute()

if __name__=='__main__':unittest.main()
