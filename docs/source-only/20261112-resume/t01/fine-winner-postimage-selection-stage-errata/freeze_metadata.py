"""Hash-only metadata sealing."""
from pathlib import Path
import ast,hashlib,json
HERE=Path(__file__).resolve().parent
def row(p):
 b=p.read_bytes();return {'path':str(p),'relative_path':p.name,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
def dump(n,x):(HERE/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
for p in HERE.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name not in {'REGISTRY.json','ALLOWLIST.json'}]
dump('REGISTRY.json',{'status':'STATIC_METADATA_ERRATUM_FOR_REVIEW_NOT_DRIVER_READY','corrected_pre_input_origins':72,'uniform_actual_targets':9,'source_or_transform_changes':False,'stage_or_prepare_execution':False,'Fine_or_ca9_or_original_freeze_modified':False,'driver_ready':False,'files':files,'self_hash_not_embedded':True})
dump('ALLOWLIST.json',{'status':'METADATA_ONLY_ERRATUM','files':files+[row(HERE/'REGISTRY.json')],'no_self_hash':True})
print(json.dumps({'REGISTRY':row(HERE/'REGISTRY.json'),'ALLOWLIST':row(HERE/'ALLOWLIST.json'),'REPORT':row(HERE/'REPORT.md')},indent=2))
