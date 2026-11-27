"""Readonly replay of the accepted original owner, then exact evidence export."""
from pathlib import Path
import base64,hashlib,json,subprocess,time,zlib

COMMIT='ce08ba304bafb7732c8fd9f27553822f87cfb7d0'
ROOT=Path('/workspace/p1-complete-proof')
BASE=ROOT/'20261126-p15-current-corrections-v1'/COMMIT
SCRIPT=BASE/'published-entrypoints/run_group_log.py'
TARGET='ImbalancedChen.P5OriginalGroupLogAbelVariation'
assert hashlib.sha256(SCRIPT.read_bytes()).hexdigest()=='9f618457ddd5dd25b251b153cf5f278bbf37ffead78247a034146efa95c49057'
out=ROOT/'20261127-p15-group-log-readonly-v1'/COMMIT/'attempt-00000'
assert out.resolve()==out
out.mkdir(parents=True,exist_ok=False)
argv=['python3','-B',str(SCRIPT),'--source-commit',COMMIT,'--check']
start=time.time()
p=subprocess.run(argv,cwd='/workspace',capture_output=True)
for name,raw in [('READONLY_RESULT.json',p.stdout),('readonly.stderr.log',p.stderr)]:
    with (out/name).open('xb') as f:f.write(raw)
command={'argv':argv,'cwd':'/workspace','exit_code':p.returncode,'elapsed_seconds':time.time()-start,
         'stdout_sha256':hashlib.sha256(p.stdout).hexdigest(),'stderr_sha256':hashlib.sha256(p.stderr).hexdigest(),
         'normal_or_kernel_commands_executed':0}
with (out/'READONLY_COMMAND.json').open('x') as f:json.dump(command,f,indent=2,sort_keys=True);f.write('\n')
assert p.returncode==0,'Readonly replay failed; original evidence retained'
result=json.loads(p.stdout);assert result['status']=='REVALIDATED'

def entry(path):
    assert path.is_file() and not path.is_symlink() and path.resolve()==path,str(path)
    b=path.read_bytes();assert len(b)<8*1024*1024; b.decode('utf-8')
    return {'remote_path':str(path),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),
            'base64':base64.b64encode(b).decode()}

def tree(root):
    assert root.is_dir() and root.resolve()==root,str(root)
    files={}
    for path in sorted(root.rglob('*')):
        assert not path.is_symlink(),str(path)
        if path.is_file() and path.suffix in ('.json','.log','.lean','.py','.txt'):
            files[path.relative_to(root).as_posix()]=entry(path)
    return files

groups={'group-log-operation':tree(BASE/'group-log-operation'),
        'group-log-owner':tree(BASE/TARGET),'group-log-readonly':tree(out),
        'group-log-stage':{'GROUPLOG_STAGE_RECEIPT.json':entry(BASE/'published-entrypoints/GROUPLOG_STAGE_RECEIPT.json')}}
raw=(json.dumps({'schema':'p15_group_log_exact_acceptance_export_v1','read_only':True,'groups':groups},sort_keys=True,separators=(',',':'))+'\n').encode()
compressed=zlib.compress(raw,9)
print(json.dumps({'schema':'p15_compressed_group_log_acceptance_export_v1','encoding':'zlib+base64',
                  'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),
                  'compressed_bytes':len(compressed),'files':sum(len(g) for g in groups.values()),
                  'status':result['status'],'owner':result['owner'],
                  'data_base64':base64.b64encode(compressed).decode()},sort_keys=True),flush=True)
