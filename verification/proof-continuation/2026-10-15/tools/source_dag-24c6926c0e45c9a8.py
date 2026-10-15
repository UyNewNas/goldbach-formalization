from pathlib import Path
import re,json,hashlib,subprocess
from datetime import datetime,timezone
WORKSPACE=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
PROVIDERS={
 'goldbach':(Path('/home/slava/codex-lean-ve/native-packages/goldbach'),'09b97db5764ade1246bfb77206baa1b124760958'),
 'mathlib':(Path('/home/slava/codex-lean-ve/native-packages/mathlib'),'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1')}
ROOTS=[('project',WORKSPACE)]+[(k,v[0]) for k,v in PROVIDERS.items()]
BASELINE='ImbalancedChen.Part3ComplexDispersion'
CANDIDATE='ImbalancedChen.Part3CommonSmoothCutoff'
def sha(b):return hashlib.sha256(b).hexdigest()
def strip_comments_strings(s):
 out=[];i=0;depth=0;string=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif s.startswith('/-',i):depth=1;out.append(' ');i+=2
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
cache={}
def source(m):
 if m in cache:return cache[m]
 for kind,r in ROOTS:
  p=r/(m.replace('.','/')+'.lean')
  if p.is_file():
   b=p.read_bytes();im=[]
   for line in strip_comments_strings(b.decode('utf-8-sig')).splitlines():
    mat=re.match(r'^\s*(?:(?:public|private|meta|all)\s+)*import\s+(.*)$',line)
    if mat:im.extend(re.findall(r'[\w]+(?:\.[\w]+)*',mat.group(1)))
   cache[m]={'module':m,'kind':kind,'path':str(p),'sha256':sha(b),'imports':im}
   return cache[m]
 cache[m]=None
 return None
def closure(start):
 seen=set();found=set();unresolved=set()
 def visit(m):
  if m in seen:return
  seen.add(m);entry=source(m)
  if entry is None:unresolved.add(m);return
  found.add(m)
  for x in entry['imports']:visit(x)
 visit(start)
 return found,unresolved
base,bu=closure(BASELINE);cand,cu=closure(CANDIDATE)
new=cand-base
providers={}
for k,(p,pin) in PROVIDERS.items():
 head=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
 status=subprocess.check_output(['git','-C',str(p),'status','--porcelain=v1','--untracked-files=no'],text=True)
 providers[k]={'root':str(p),'required_pin':pin,'actual_head':head,'head_matches_pin':head==pin,'tracked_status_lines':status.splitlines()}
report={
 'kind':'source_only_import_closure_review','generated_utc':datetime.now(timezone.utc).isoformat(),
 'baseline_module':BASELINE,'baseline_source_sha256':source(BASELINE)['sha256'],
 'candidate_module':CANDIDATE,'candidate_source_sha256':source(CANDIDATE)['sha256'],
 'script_sha256':sha(Path(__file__).read_bytes()),'providers':providers,
 'method':'recursive actual import declarations with public/private/meta/all prefixes; nested Lean block comments, line comments and strings removed; unresolved roots retained explicitly',
 'scope_limit':'Source-DAG comparison only; no compiler, object, declaration, axiom or analytic-estimate acceptance. Only these three source roots are resolved; equal unresolved roots are preserved, not claimed inspected.',
 'baseline_resolved_modules':sorted(base),'baseline_unresolved_modules':sorted(bu),
 'candidate_resolved_modules':sorted(cand),'candidate_unresolved_modules':sorted(cu),
 'new_resolved_project_modules':sorted(m for m in new if source(m)['kind']=='project'),
 'new_resolved_foreign_modules':sorted(m for m in new if source(m)['kind']!='project'),
 'new_unresolved_modules':sorted(cu-bu),
 'all_resolved_source_manifest':[source(m) for m in sorted(base|cand)],
 'candidate_direct_imports':source(CANDIDATE)['imports']}
report['no_new_foreign']=not report['new_resolved_foreign_modules'] and not report['new_unresolved_modules']
report['counts']={'baseline_resolved':len(base),'baseline_unresolved':len(bu),'candidate_resolved':len(cand),'candidate_unresolved':len(cu)}
out=Path(__file__).with_name('source-review.json');out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'report':str(out),'script_sha256':report['script_sha256'],'report_sha256':sha(out.read_bytes()),'candidate_sha256':report['candidate_source_sha256'],'counts':report['counts'],'new_foreign':report['new_resolved_foreign_modules'],'new_unresolved':report['new_unresolved_modules'],'no_new_foreign':report['no_new_foreign'],'pins_match':{k:v['head_matches_pin'] for k,v in providers.items()}},ensure_ascii=False))
