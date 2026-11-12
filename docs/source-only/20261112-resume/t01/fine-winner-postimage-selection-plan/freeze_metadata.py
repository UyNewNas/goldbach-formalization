"""Freeze source-selection metadata; no installation or proof execution."""
from pathlib import Path
import ast,hashlib,json
BASE=Path('E:/timot/Documents/FilesForGPT/Myath');HERE=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def ident(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
def dump(n,x):(HERE/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
for p in HERE.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
reuse=BASE/'output/resume-20261112/t02/dependency-reuse-plan'
assert sha((reuse/'REGISTRY.json').read_bytes())=='d2ffa97c6e6a7337d7fb7149ae32ceb7474caaaf1a2303a4fdcd809931d2c350'
assert sha((reuse/'REPORT.txt').read_bytes())=='8bc55e639470c43162c721b03b42c10da2d3070f9da24b9fcf280a606ada9261'
assert sha((HERE/'REQUIRED_REMOTE_OUTPUTS_AND_CONES.json').read_bytes())=='197c0a8f089f3e351c09216a0d3f79955e638be16786cc91877bf5093a84bb9d'
dump('RECOVERY_REVIEW_IDENTITIES.json',{'owner':'T02','independent_facet_analysis':[ident(reuse/'REGISTRY.json'),ident(reuse/'REPORT.txt')],'this_cone_bound_by_T02':ident(HERE/'REQUIRED_REMOTE_OUTPUTS_AND_CONES.json'),'no_runtime_or_restoration_implemented':True})
files=[ident(p) for p in sorted(HERE.rglob('*')) if p.is_file() and p.name not in {'REGISTRY.json','ALLOWLIST.json'}]
for r in files:r['relative_path']=str(Path(r['path']).relative_to(HERE)).replace('\\','/')
dump('REGISTRY.json',{'schema':'T01_FINE_WINNER_POSTIMAGE_SELECTION_PLAN_V1','status':'FROZEN_STATIC_SUCCESSOR_SELECTION_UNVALIDATED_TAIL_NOT_DRIVER_READY','driver_ready':False,'Fine_or_ca9_changed':False,'project_modules':1816,'native_research_modules':43,'mathematical_modules':1859,'explicit_existing_source_repins':72,'accepted20_reproduced_exact_bytes':True,'unaccepted_stored52':True,'pending020_030_acceptance_not_inferred':True,'new_winner_sources':8,'new071_source':'partial-tail/P5SubdivisionStoredBlock071.lean','new071_rows':1817,'new071_chunks':[64]*28+[25],'new071_validated':False,'source_repin_reverse_cone':266,'outside_source_cone':1550,'verified_coherent_restore_modules':[],'other_project_outputs':1736,'kernel_type_axiom_gates_preserved':True,'prepare_stage_proof_producer_Git_or_CI_executed':False,'files':files,'self_hash_not_embedded':True})
dump('ALLOWLIST.json',{'status':'FOR_T10_STATIC_SELECTION_AND_TAIL_REVIEW_NOT_DEPLOYMENT','files':files+[ident(HERE/'REGISTRY.json')],'no_self_hash':True})
print(json.dumps({'REGISTRY':ident(HERE/'REGISTRY.json'),'REPORT':ident(HERE/'REPORT.md'),'ALLOWLIST':ident(HERE/'ALLOWLIST.json'),'TAIL071':ident(HERE/'partial-tail/P5SubdivisionStoredBlock071.lean'),'payload_files':len(files)},indent=2))
