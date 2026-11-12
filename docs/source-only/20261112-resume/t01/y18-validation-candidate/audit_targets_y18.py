"""Exact17 Y18 original theorem owners/types/collectAxioms/#print axioms dual gate."""
from pathlib import Path
import hashlib,json,os,re
assert os.environ.get('GITHUB_ACTIONS')=='true'
here=Path(__file__).resolve().parent;manifest_path=here/'Y18_MANIFEST.json'
m=json.loads(manifest_path.read_text());logs=Path(os.environ['LOGS']);project=Path(os.environ['PROJECT'])
prov=json.loads((project/'Y18_PROVENANCE.json').read_text());assert prov['manifest_sha256']==hashlib.sha256(manifest_path.read_bytes()).hexdigest()
raw=(logs/'batch-types.log').read_bytes();text=raw.decode('utf-8')
records=[json.loads(line.removeprefix('P0_ROUND6_DECL ')) for line in text.splitlines() if line.startswith('P0_ROUND6_DECL ')]
assert len(records)==len({r['name'] for r in records})
by={r['name']:r for r in records};selected=[];allowed={'propext','Classical.choice','Quot.sound'}
assert len(m['target_declarations'])==len({r['name'] for r in m['target_declarations']})==17
for expected in m['target_declarations']:
 r=by[expected['name']];assert r['module']==expected['module'] and r['kind']==expected['kind']=='theorem'
 assert not(r['is_axiom'] or r['is_partial'] or r['is_unsafe']) and set(r['axioms'])<=allowed
 assert all(isinstance(r[k],str) and r[k].strip() and not any(x in r[k] for x in ['⋯','…']) for k in ['type','readable_type'])
 name=re.escape(r['name'])
 deps=re.findall(r"['\"]?"+name+r"['\"]?\s+depends on axioms:\s*\[([^\]]*)\]",text)
 none=re.findall(r"['\"]?"+name+r"['\"]?\s+does not depend on any axioms",text)
 assert len(deps)+len(none)==1,('Missing/duplicate independent axiom output',r['name'])
 printed={x.strip() for x in deps[0].split(',') if x.strip()} if deps else set()
 assert printed==set(r['axioms']);selected.append(r)
out=logs/'TARGET17_RESULT.json';assert not out.exists() and not out.resolve().is_relative_to(project.resolve())
out.write_text(json.dumps({'status':'PASS_EXACT_ORIGINAL17_OWNER_FULL_TYPES_AND_DUAL_AXIOMS','manifest_sha256':prov['manifest_sha256'],'log_sha256':hashlib.sha256(raw).hexdigest(),'targets':selected,'whole_P2_or_PP_or_K_accepted':False},indent=2)+'\n')
