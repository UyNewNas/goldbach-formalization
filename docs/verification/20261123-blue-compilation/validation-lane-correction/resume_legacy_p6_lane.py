"""Drain the existing P6 named chain without repeating any completed command."""
from pathlib import Path
import datetime, fcntl, json, os, signal, time
R=Path(__file__).resolve().parent
state=json.loads(Path('/workspace/blue-build-tools/runtime-evidence/state.json').read_text())
lane=Path(state['slot']+'.validation-lane.lock')
paused=json.loads((R/'PAUSED_OWN_PARENT_CONTROLLERS.json').read_text())['records']
def proc(pid):
    p=Path('/proc')/str(pid)
    try:
        a=[x for x in (p/'cmdline').read_text().split('\0') if x]
        s=(p/'stat').read_text().rsplit(')',1)[1].split()
        return {'pid':pid,'argv':a,'state':s[0],'starttime':s[19]}
    except (OSError,UnicodeError):return None
def live(x):
    p=proc(x['pid']);return p is not None and p['starttime']==x['starttime'] and p['state']!='Z'
def save(x):
    p=R/'LEGACY_P6_LANE.json';q=p.with_suffix('.tmp');q.write_text(json.dumps(x,indent=2)+'\n');q.replace(p)
current=proc(176883)
assert current is None or current['argv']==['python3','/workspace/blue-member-repair-batch56/run_validation.py']
record={'pid':os.getpid(),'lock':str(lane),'old_current_batch56':current,'paused_controllers':paused,
        'scope':'Only owner parent scheduling resumes; no Lean/checker/runtime is signalled.','events':[]}
with lane.open('a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    record.update(acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),inode=lane.stat().st_ino)
    record['proc_locks_owner_lines']=[s for s in Path('/proc/locks').read_text().splitlines() if 'FLOCK' in s and '->' not in s and (' '+str(os.getpid())+' ') in s and str(lane.stat().st_ino) in s]
    assert record['proc_locks_owner_lines'];save(record)
    while current and live(current):time.sleep(1)
    for batch in [57,59]:
        x=next((x for x in paused if x['batch']==batch),None)
        if x and live(x):
            actual=proc(x['pid']);assert actual['argv']==x['argv'] and actual['state']=='T'
            os.kill(x['pid'],signal.SIGCONT)
            record['events'].append({'batch':batch,'pid':x['pid'],'signal':'SIGCONT_PARENT_CONTROLLER_ONLY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat()});save(record)
            while live(x):time.sleep(1)
    record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save(record)
