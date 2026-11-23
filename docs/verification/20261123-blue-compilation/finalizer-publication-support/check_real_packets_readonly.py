"""Read only the pure preparation gate. Never call publisher.main()."""
from pathlib import Path
import sys,hashlib,json,importlib.util,datetime
sys.dont_write_bytecode=True
SCRIPT=Path('/workspace/blue-build-tools/publish_verified_member_batch.py')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('verified_member_publisher_gate',SCRIPT);publisher=importlib.util.module_from_spec(spec);spec.loader.exec_module(publisher)
rows=[]
for batch in ['58','61','64','65','68']:
 source=Path('/workspace/blue-member-repair-batch'+batch);required=['PUBLICATION_FILES.json','FINAL_RELEASE.json','INDEPENDENT_REVIEW.json','LATE_FINALIZER_LOG_BINDING.json','FINAL_REVIEW_NEW_FILES_MANIFEST.json']
 missing=[n for n in required if not(source/n).exists()]
 if missing:rows.append({'batch':batch,'status':'PENDING_OWNER_REVIEW_FILES','missing':missing});continue
 before={n:sha(source/n)for n in required};manifest=publisher.read(source/'PUBLICATION_FILES.json');original=json.loads(json.dumps(manifest));review=publisher.read(source/'INDEPENDENT_REVIEW.json');files,exception=publisher.prepare_publication_files(source,manifest,review);assert manifest==original and exception;changed=[x['path']for x,y in zip(files,original['files'])if x!=y];assert changed==['finalizer.log'];assert all(sha(source/n)==before[n]for n in required);rows.append({'batch':batch,'status':'PASS_READ_ONLY_PREPARATION_GATE','input_hashes':before,'original_file_count':len(files),'original_current_exact_count':len(files)-1,'copy_list_only_replacement':changed,'original_manifest_exception':exception})
out={'schema':'readonly_real_finalizer_gate_checks_v1','checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'publisher_sha256':sha(SCRIPT),'only_function_called':'prepare_publication_files','actual_main_publication_Lean_build_kernel_or_numeric_replay_run':False,'production_records_modified':False,'batches':rows};p=Path(__file__).with_name('READ_ONLY_GATE_RESULTS.json');p.write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'publisher_sha256':sha(SCRIPT),'batches':[{'batch':x['batch'],'status':x['status']}for x in rows],'receipt_path':str(p),'receipt_sha256':sha(p)},indent=2))
