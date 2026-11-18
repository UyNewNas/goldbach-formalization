import json,os,pathlib,subprocess,sys,tempfile,unittest
SCRIPT=str(pathlib.Path(__file__).with_name('run_stage.py').resolve())
class Tests(unittest.TestCase):
 def run_case(self,program,deadline=2):
  with tempfile.TemporaryDirectory() as d:
   r=subprocess.run([sys.executable,SCRIPT,'--timeout',str(deadline),'--grace','.2','stub',sys.executable,'-u','-c',program],env=dict(os.environ,RUNNER_TEMP=d),capture_output=True,timeout=8)
   log=pathlib.Path(d,'lean-verification-logs');receipt=json.loads((log/'stub.supervisor.json').read_text());return r,receipt,(log/'stub.log').read_text()
 def test_success(self):
  r,s,l=self.run_case('print("kept")');self.assertEqual(r.returncode,0);self.assertEqual(s['status'],'PASS');self.assertIn('kept',l)
 def test_failure(self):
  r,s,l=self.run_case('import sys; print("failed");sys.exit(7)');self.assertEqual(r.returncode,7);self.assertEqual(s['status'],'FAILED')
 def test_timeout_kills_term_ignoring_grandchild(self):
  r,s,l=self.run_case('import subprocess,sys,time; subprocess.Popen([sys.executable,"-c","import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)"]);print("started");time.sleep(60)',.3)
  self.assertEqual(r.returncode,124);self.assertEqual(s['remaining_live_pids'],[]);self.assertIn('SIGKILL',[x['signal'] for x in s['cleanup']]);self.assertIn('started',l)
 def test_successful_parent_cannot_leave_residual(self):
  r,s,l=self.run_case('import subprocess,sys;subprocess.Popen([sys.executable,"-c","import time;time.sleep(60)"])');self.assertEqual(r.returncode,125);self.assertEqual(s['remaining_live_pids'],[])
 def test_bash_pipeline_children_are_cleaned(self):
  with tempfile.TemporaryDirectory() as d:
   r=subprocess.run([sys.executable,SCRIPT,'--timeout','.2','--grace','.2','bashstub','bash','-c','sleep 60 | cat'],env=dict(os.environ,RUNNER_TEMP=d),capture_output=True,timeout=8)
   receipt=json.loads(pathlib.Path(d,'lean-verification-logs/bashstub.supervisor.json').read_text());self.assertEqual(r.returncode,124);self.assertEqual(receipt['remaining_live_pids'],[])
 def test_term_signal_cleanup(self):
  import signal,time
  with tempfile.TemporaryDirectory() as d:
   p=subprocess.Popen([sys.executable,SCRIPT,'--timeout','60','--grace','.2','signalstub','bash','-c','sleep 60'],env=dict(os.environ,RUNNER_TEMP=d),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
   time.sleep(.25);p.send_signal(signal.SIGTERM);p.communicate(timeout=5)
   receipt=json.loads(pathlib.Path(d,'lean-verification-logs/signalstub.supervisor.json').read_text());self.assertEqual(p.returncode,143);self.assertEqual(receipt['remaining_live_pids'],[])
if __name__=='__main__':unittest.main()
