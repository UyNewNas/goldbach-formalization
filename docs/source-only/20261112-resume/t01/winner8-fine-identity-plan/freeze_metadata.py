"""Freeze static comparison metadata only."""
from pathlib import Path
import ast,hashlib,json
HERE=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def row(p):
 b=p.read_bytes();return {'path':str(p),'relative_path':p.name,'bytes':len(b),'sha256':sha(b),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
def dump(n,x):(HERE/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
for p in HERE.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
files=[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name not in {'REGISTRY.json','ALLOWLIST.json'}]
dump('REGISTRY.json',{'schema':'T01_WINNER8_FINE_AND_STORED_EXACT_COMPARISON_V1','status':'FROZEN_STATIC_FACTS_NOT_DRIVER_READY','Fine_or_ca9_changed':False,'winner_targets':8,'winner_project_closure':1646,'Fine_project_closure':1808,'intersection_same_bytes':1638,'same_name_replacements':0,'new_project_sources':8,'combined_project':1816,'native_research':43,'new_native_or_direct_external':0,'combined_mathematical_module_set':1859,'audit_module_set_frozen':False,'Fine_Stored_originals_reached':72,'accepted_postimages':20,'accepted_postimages_same_as_Fine_source':0,'future20_repin_reverse_cone':214,'coherent_restore_accepted':False,'driver_ready':False,'prohibited_execution_performed':False,'files':files,'self_hash_not_embedded':True})
dump('ALLOWLIST.json',{'status':'STATIC_COMPARISON_FILES_ONLY_NOT_SOURCE_INSTALLATION_AUTHORIZATION','files':files+[row(HERE/'REGISTRY.json')],'no_self_hash':True})
print(json.dumps({'REGISTRY':row(HERE/'REGISTRY.json'),'REPORT':row(HERE/'REPORT.md'),'ALLOWLIST':row(HERE/'ALLOWLIST.json'),'files_without_self':len(files)},indent=2))
