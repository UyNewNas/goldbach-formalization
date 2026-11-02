"""Text/metadata audit only: never evaluate a mathematical row or Lean body."""
from pathlib import Path
import hashlib,json,re,zipfile
H=Path(__file__).resolve().parent
R=H.parents[3]
Z=R/'.lake/proof-continuation/source-reviews/drafts/20261028-EvidenceLocator/chen-numerical-evidence-20261010.zip'
B='chen-numerical-evidence-20261010-renewal-v2/goldbach-research/'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def named_rows(text):
    return [(n,[x.strip() for x in coeffs.split(',')])
      for n,coeffs in re.findall(r'\("([^"]*)",\s*!\[([^\]]+)\]\)',text)]
def original_rows(cells):
    return [(r['name'],r['affine']) for c in cells for r in c['affine_constraints']]
checks=[]
with zipfile.ZipFile(Z) as z:
    def read(n):return json.loads(z.read(B+n))
    asc=read('eighth-prefix-family-20261009-navigation.json')['strict_cells']
    nine=read('eighth-unequal-parent-nine-20261009-family-navigation.json')['strict_cells']
    a50=read('eighth-unequal-parent-fifty-20261009-navigation.json')
    d50=read('eighth-unequal-parent-fifty-desc-20261009-navigation.json')
    groups=read('eighth-history-first-failure-20261009-navigation.json')['groups']
    h5=next(g['strict_cells'] for g in groups if g['separation']=='H5')
    h7=next(g['strict_cells'] for g in groups if g['separation']=='H7')
    for name,expected in [
      ('P4AOriginalSeed7Unequal15Literal.lean',original_rows([asc[7]]+nine+[a50,d50])),
      ('P4AOriginalFirstFailureH5H7Literal.lean',original_rows(h5+h7))]:
        observed=named_rows((H/name).read_text(encoding='utf-8'))
        checks.append(dict(file=name,kind='ordered names and literal coefficient strings',
          expected_rows=len(expected),observed_rows=len(observed),equal=observed==expected))
    source=(H/'P4AOriginalAscendingFourteenAffineSource.lean').read_text(encoding='utf-8')
    poolText=source.split('def literalPool',1)[1].split('def literalIndex',1)[0]
    indexText=source.split('def literalIndex',1)[1].split('def rows',1)[0]
    pool=[[x.strip() for x in line.split(',')] for line in re.findall(r'!\[([^!\[\]]+)\]',poolText)]
    indices=[[int(x.strip()) for x in line.split(',')] for line in re.findall(r'!\[([^!\[\]]+)\]',indexText)]
    observed=[pool[i] for cell in indices for i in cell]
    expected=[r['affine'] for c in asc if c['cell_id']!=7 for r in c['affine_constraints']]
    checks.append(dict(file='P4AOriginalAscendingFourteenAffineSource.lean',kind='literal pool/index reconstruction',
      expected_rows=len(expected),observed_rows=len(observed),equal=observed==expected))
    checks.append(dict(kind='H5/H7 priority source row names',
      H5={str(k):h5[0]['affine_constraints'][k]['name'] for k in [18,36,37]},
      H7={str(k):h7[0]['affine_constraints'][k]['name'] for k in [18,36,37,38]}))

new=[]
for p in sorted(H.glob('*.lean')):
    text=p.read_text(encoding='utf-8')
    ns=re.search(r'^namespace\s+(\S+)',text,re.M).group(1)
    declarations=[dict(name=ns+'.'+m.group(2),kind=m.group(1),line=text.count('\n',0,m.start())+1)
      for m in re.finditer(r'^(?:private\s+)?(def|abbrev|theorem|inductive|structure)\s+(\w+)',text,re.M)]
    imports=[]
    for mod in re.findall(r'^import\s+(\S+)',text,re.M):
        local=H/(mod.split('.')[-1]+'.lean')
        prod=R/('/'.join(mod.split('.'))+'.lean')
        special=R/'docs/source-only/20261102-resume-30p/adopted87_policy'/(mod.split('.')[-1]+'.lean')
        q=next((x for x in [local,prod,special] if x.is_file()),None)
        imports.append(dict(module=mod,path=str(q.relative_to(R)).replace('\\','/') if q else None,
          sha256=sha(q) if q else None,status='source-found-uncompiled' if q else 'external-library-unchecked'))
    new.append(dict(path=str(p.relative_to(R)).replace('\\','/'),module=ns,bytes=p.stat().st_size,
      sha256=sha(p),direct_imports=imports,declarations=declarations,
      compiled=False,kernel_verified=False,formal_credit=0,finite_bodies='UNEVALUATED'))

out=dict(status='TEXT_METADATA_ONLY',source_string_checks=checks,files=new,
  compiler_run=False,finite_guard_evaluated=False,numerical_row_evaluated=False,
  original_producer_run=False,git_operation_run=False)
(H/'SOURCE_TEXT_AUDIT.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(new),source_string_checks=[{k:v for k,v in x.items() if k in ['file','expected_rows','equal']} for x in checks]),ensure_ascii=False))
