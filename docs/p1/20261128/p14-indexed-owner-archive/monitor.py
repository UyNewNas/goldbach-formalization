from pathlib import Path
import subprocess,time,os,signal,json,datetime
ROOT=Path(__file__).resolve().parent
assert not (ROOT/'WATCHDOG_00018.json').exists()
p=subprocess.Popen(['python','-B',str(ROOT/'validate_00018.py')])
peak=0;cgpeak=0;seen=[];killed=[];limit=int(Path('/sys/fs/cgroup/memory.max').read_text())-2**30
while p.poll() is None:
 current=int(Path('/sys/fs/cgroup/memory.current').read_text());cgpeak=max(cgpeak,current);own=[];parents={};rss={}
 for item in Path('/proc').iterdir():
  if not item.name.isdigit():continue
  try:
   lines=(item/'status').read_text().splitlines();pid=int(item.name)
   parents[pid]=int(next(x.split()[1] for x in lines if x.startswith('PPid:')))
   rss[pid]=int(next(x.split()[1] for x in lines if x.startswith('VmRSS:')))*1024
  except (OSError,StopIteration):pass
 for pid,usage in rss.items():
  a=pid;visited=set()
  while a!=p.pid and a>1 and a not in visited:
   visited.add(a);a=parents.get(a,0)
  if a==p.pid:
   own.append((usage,pid));peak=max(peak,usage)
   if pid not in seen:seen.append(pid)
 if own:
  usage,pid=max(own)
  if usage>26*2**30 or current>limit:
   try:os.kill(pid,signal.SIGTERM);killed.append(dict(pid=pid,rss_bytes=usage,cgroup_current=current,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
   except OSError:pass
 time.sleep(.25)
(ROOT/'WATCHDOG_00018.json').write_text(json.dumps(dict(status='FINISHED',exit_code=p.returncode,all_stage_peak_sampled_process_rss_bytes=peak,cgroup_peak_bytes=cgpeak,observed_own_descendant_pids=seen,terminated=killed,limit_gib=26,cgroup_limit_bytes=limit,sampling_seconds=.25,only_largest_own_process_signaled=True,guard_source_state_runtime_unchanged=True),indent=2)+'\n')
raise SystemExit(p.returncode)
