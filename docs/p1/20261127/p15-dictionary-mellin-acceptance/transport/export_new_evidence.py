"""Read exact new dictionary acceptance and Tau probe evidence; no validation execution."""
from pathlib import Path
import base64, hashlib, json, zlib

ROOT = Path('/workspace/p1-complete-proof')
COMMIT = '040d46058821746c69c5183b3f6c22792287c4ba'
FORMAL = ROOT / '20261126-p15-current-corrections-v1' / COMMIT
INSTALL = ROOT / '20261127-p15-dictionary-source-install-v1' / COMMIT / 'runs/attempt-00000'
DICT = 'ImbalancedChen.P1OriginalHistoricalCoefficientDictionary'
TAU = ROOT / '20261127-p15-tau-mathlib-probe-v1/bb3e9be4179da59d60bae5698ce53ac4995084a29d557ed4679dbd72bc7409f3/runs/attempt-00000'

def entry(path):
    assert path.is_file() and not path.is_symlink() and path.resolve()==path, str(path)
    b=path.read_bytes()
    assert len(b)<8*1024*1024, str(path)
    b.decode('utf-8')
    return {'remote_path':str(path),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),
            'base64':base64.b64encode(b).decode()}

def tree(root):
    assert root.is_dir() and root.resolve()==root, str(root)
    result={}
    for p in sorted(root.rglob('*')):
        assert not p.is_symlink(), str(p)
        if p.is_file() and p.suffix in ('.json','.log','.lean','.py','.txt'):
            result[p.relative_to(root).as_posix()]=entry(p)
    return result

accepted=json.loads((FORMAL/'runs/attempt-00000/RESULT.json').read_bytes())
assert accepted['new_owner_accepted'] is True and accepted['worker_exit_code']==0
assert accepted['owner']['only_standard_axioms'] is True and accepted['owner']['full_owned_including_private_generated'] is True
tau_result=json.loads((TAU/'PROBE_RESULT.json').read_bytes())
assert tau_result['probe_passed'] is True and tau_result['exit_code']==0
groups={'dictionary-install':tree(INSTALL),
        'dictionary-run':tree(FORMAL/'runs/attempt-00000'),
        'dictionary-owner':tree(FORMAL/DICT),
        'tau-probe':{name:entry(TAU/name) for name in (
            'PROBE_RESULT.json','PRECOMPILE_INVENTORY.json','probe.log','PROBE_LANE.json','Part3ElementaryTauTruncation.lean')}}
groups['tau-probe']['probe_driver.py']=entry(ROOT/'p15-staged-scripts/probe_tau_mathlib_bb3e9be4.py')
groups['tau-probe']['inventory_tau_readiness.py']=entry(ROOT/'p15-staged-scripts/inventory_tau_readiness_7c2b06a3.py')
total=sum(row['bytes'] for group in groups.values() for row in group.values())
assert total<64*1024*1024
packet={'schema':'p15_new_evidence_exact_export_v1','read_only':True,'groups':groups}
raw=(json.dumps(packet,sort_keys=True,separators=(',',':'))+'\n').encode()
compressed=zlib.compress(raw,9)
print(json.dumps({'schema':'p15_compressed_new_evidence_export_v1','encoding':'zlib+base64',
                  'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),
                  'compressed_bytes':len(compressed),
                  'files':sum(len(g) for g in groups.values()),
                  'data_base64':base64.b64encode(compressed).decode()},sort_keys=True),flush=True)
