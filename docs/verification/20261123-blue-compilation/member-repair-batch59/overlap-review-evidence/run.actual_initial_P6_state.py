from pathlib import Path
import json,hashlib,subprocess,time,datetime
R=Path(__file__).resolve().parent;P=Path('/workspace/blue-member-build');M='ImbalancedChen.P1OriginalFourthSmallCellPointwise';S=Path('/workspace/blue-build-tools/runtime-evidence/state.json');rel=M.replace('.','/');src=P/(rel+'.lean');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=sha(src)
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit():continue
 try:a=proc.joinpath('cmdline').read_bytes().split(b'\0')
 except (FileNotFoundError,PermissionError):continue
 assert str(src).encode() not in a,('another_source_writer',proc.name)
stock_argv=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(S),'lake','--no-build','build','+'+M+':olean'];stock_start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (R/'stock.log').open('x') as out:stock=subprocess.run(stock_argv,cwd=P,stdout=out,stderr=subprocess.STDOUT)
import re
stock_rec={'argv':stock_argv,'exit_code':stock.returncode,'started_utc':stock_start,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'log_sha256':sha(R/'stock.log'),'not_an_actual_source_failure':True};(R/'STOCK_COMMAND.json').write_text(json.dumps(stock_rec,indent=2)+'\n');assert stock.returncode in [0,3]
fails=set(re.findall(r'(?m)^✖ .*? (?:Building|Running) ([A-Za-z0-9_.]+)',(R/'stock.log').read_text()))
if fails-{M}:
 (R/'IMPORTS_NOT_READY_NORMAL_NOT_STARTED.json').write_text(json.dumps({'failed_import_suppliers':sorted(fails-{M}),'source_not_compiled':True},indent=2)+'\n');raise SystemExit(3)
if stock.returncode==0:
 (R/'ALREADY_CURRENT_STOCK_NORMAL_NOT_REPEATED.json').write_text(json.dumps({'module':M,'source_sha256':sha(src),'no_new_normal_credit':True},indent=2)+'\n');raise SystemExit(0)
argv=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(S),'lake','build',M+':olean'];t=time.monotonic();start=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (R/'normal.log').open('x') as out:result=subprocess.run(argv,cwd=P,stdout=out,stderr=subprocess.STDOUT)
assert sha(src)==before
record={'module':M,'argv':argv,'cwd':str(P),'started_utc':start,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-t,'exit_code':result.returncode,'log_sha256':sha(R/'normal.log'),'source_before_after_sha256':before,'original_selected_source_bytes_unchanged':True,'scope':'NORMAL_ONLY_UNCHANGED_ORDINARY_NECESSARY_P1_DEPENDENCY','no_new_kernel_or_owned_acceptance_claim':True,'no_broad_DAG_controller':True}
(R/'COMMAND.json').write_text(json.dumps(record,indent=2)+'\n')
if result.returncode==0:
 paths=[rel+'.lean','.lake/build/lib/lean/'+rel+'.olean','.lake/build/lib/lean/'+rel+'.ilean','.lake/build/ir/'+rel+'.c','.lake/build/ir/'+rel+'.setup.json','.lake/build/lib/lean/'+rel+'.trace'];snap={name:{'bytes':(P/name).stat().st_size,'sha256':sha(P/name)} for name in paths};assert len(snap)==6;(R/'NORMAL_SOURCE_PLUS_FIVE_OUTPUTS.json').write_text(json.dumps(snap,indent=2)+'\n')
print(json.dumps(record),flush=True)
raise SystemExit(result.returncode)
