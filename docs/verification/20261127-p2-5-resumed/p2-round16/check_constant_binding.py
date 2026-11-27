"""Resolve the accepted theorem's actual type from the stock environment inventory, without rerunning Lean."""
import hashlib
import json
from pathlib import Path
import re
import sys

out=Path(sys.argv[1])
owner='ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7'
name=owner+'.cell0_affine_semantic'
d=out/'new-owned'/owner
declared=d/'artifacts/declarations.json'
types=d/'artifacts/types.txt'
stock=d/'latest.json'
summ=json.loads((out/'RUN_RESULT.json').read_bytes())
receipt=json.loads(stock.read_bytes())
assert receipt['accepted']
for item in [declared,types]:
    hashes=[value for path,value in receipt['artifacts'].items() if Path(path).name==item.name]
    assert hashes==[hashlib.sha256(item.read_bytes()).hexdigest()]
j=json.loads(declared.read_bytes());found=[v for v in j['declarations'] if v['name']==name]
assert len(found)==1 and j['declaration_count']==len(j['declarations'])==29
assert summ['audit_summary']['modules'][owner]==dict(accepted=True,reused=False,declarations=29)
typed=found[0]['type'];assert name+'\n'+typed in types.read_text()
s=' '.join(typed.split());c='ImbalancedChen.VariableEnvelope.C'
assert c in s and '⋯' not in typed
prefix,sep,formula=s.partition('And ')
assert sep and prefix == '∀ (t : '+owner+'.Point8) (h : '+owner+'.Cell0Affine t), '
assert not re.search(r'(?<![A-Za-z0-9_.])C(?![A-Za-z0-9_.])',s)
record=dict(schema='p25-r16-compiled-constant-C-binding-v1',module=owner,constant=name,
    source_commit=summ['source_commit'],native_run_result_sha256=hashlib.sha256((out/'RUN_RESULT.json').read_bytes()).hexdigest(),
    owned_receipt_sha256=hashlib.sha256(stock.read_bytes()).hexdigest(),owned_count=j['declaration_count'],
    declarations_file=str(declared.relative_to(out)),declarations_sha256=hashlib.sha256(declared.read_bytes()).hexdigest(),
    types_file=str(types.relative_to(out)),types_sha256=hashlib.sha256(types.read_bytes()).hexdigest(),
    physical_plane_constant=c,compiled_binder_prefix=prefix.strip(),has_implicit_C_parameter=False,
    complete_native_environment_type=typed)
(out/'AFTER_SEED7_C_BINDING.json').write_text(json.dumps(record,sort_keys=True,indent=2,ensure_ascii=False)+'\n')
print('Bound',name,'with explicit',c,'and no extra C binder')
