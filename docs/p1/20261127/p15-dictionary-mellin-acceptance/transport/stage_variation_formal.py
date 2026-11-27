"""Stage the published Variation adapter using the existing immutable staging primitives."""
from pathlib import Path
from types import ModuleType
import hashlib, json, os, subprocess, sys, tomllib
sys.dont_write_bytecode=True
os.environ.update({'GIT_OPTIONAL_LOCKS':'0','GIT_NO_LAZY_FETCH':'1',
                   'GIT_TERMINAL_PROMPT':'0','PYTHONDONTWRITEBYTECODE':'1'})
REPO=Path('/workspace/goldbach-formalization')
BASE='040d46058821746c69c5183b3f6c22792287c4ba'
COMMIT='f7e9219f4860a819758d52752c5a9309dd14a8c7'
BOOTSTRAP='docs/p1/20261127/p15-historical-coefficient-dictionary/deploy_dictionary_formal.py'
ADAPTER='docs/p1/20261127/p15-mellin-variation/run_variation.py'
raw=subprocess.check_output(['git','show',BASE+':'+BOOTSTRAP],cwd=REPO)
assert hashlib.sha256(raw).hexdigest()=='a73a6f6b8a0f641c0556d65e1aa6cf4092487da37a4e58d07b06e2537ea63f31'
h=ModuleType('original_staging_primitives');h.__file__=BOOTSTRAP
exec(compile(raw,BOOTSTRAP,'exec'),h.__dict__)
before=h.gitstate()
fetch=subprocess.run(['git','-c','maintenance.auto=false','fetch','--quiet','--no-tags',
                      '--no-write-fetch-head','origin',COMMIT],cwd=REPO,capture_output=True)
assert fetch.returncode==0, 'Exact immutable source fetch failed; no checkout changed'
assert subprocess.run(['git','merge-base','--is-ancestor',BASE,COMMIT],cwd=REPO).returncode==0
adapter=h.git('show',COMMIT+':'+ADAPTER)
assert h.fp(adapter)=={'bytes':19017,'sha256':'1c132fefea799e8a3a3127defb07785138e3669e1f80beee2f5aa733b1914f50'}
dest=h.ROOT/COMMIT/'published-entrypoints/run_variation.py'
h.put(dest,adapter)
after=h.gitstate();assert before==after,'Original Git state changed'
lakefile=Path('/workspace/blue-member-build/lakefile.toml').read_bytes()
config=tomllib.loads(lakefile.decode())
def lean_settings(v,prefix=''):
    found={}
    if isinstance(v,dict):
        for k,x in v.items():
            key=prefix+'.'+k if prefix else k
            if 'lean' in k.lower() or 'warning' in k.lower():found[key]=x
            elif isinstance(x,(dict,list)):found.update(lean_settings(x,key))
    elif isinstance(v,list):
        for i,x in enumerate(v):found.update(lean_settings(x,prefix+'['+str(i)+']'))
    return found
receipt={'schema':'p15_variation_stage_v1','source_commit':COMMIT,'adapter_path':str(dest),
         'adapter':h.fp(adapter),'original_git_state_unchanged':True,'git_before':before,'git_after':after,
         'lakefile':h.fp(lakefile),'lean_settings':lean_settings(config),
         'normal_or_kernel_commands_executed':0,'new_owner_accepted':False,'whole_P1_5_complete':False}
h.put(dest.parent/'VARIATION_STAGE_RECEIPT.json',(json.dumps(receipt,indent=2,sort_keys=True)+'\n').encode())
print(json.dumps(receipt,sort_keys=True),flush=True)
