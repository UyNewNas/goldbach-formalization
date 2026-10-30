from pathlib import Path
import hashlib,re,json
MODULE='MathlibNt.SieveTheory.LinearSieve'
SOURCE_SHA256='f7ce98fbbcf3d7baca1ef6a0a3829c0ee6de85c39e7d1a6935b8f013557c5d03'
GOLDBACH_PIN='09b97db5764ade1246bfb77206baa1b124760958'
EXPLICIT_IMPORTS=['MathlibNt.SieveTheory.LinearSieve.'+x for x in ['FiniteWeights','RosserChains','BoundaryMass','BoundaryRegularity','BoundaryIntegrals','UpperRosserDensity','SieveApplications']]
def validate_source(module,data):
 assert module==MODULE, 'empty exception module not allowed'
 assert hashlib.sha256(data).hexdigest()==SOURCE_SHA256, 'empty exception source SHA mismatch'
 # Exact fixed bytes plus independent nested-comment-aware source inspection.
 s=data.decode();out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i): depth+=1;i+=2
  elif depth and s.startswith('-/',i): depth-=1;i+=2
  elif depth:i+=1
  elif s.startswith('--',i):
   e=s.find('\n',i);i=len(s) if e<0 else e
  else:out.append(s[i]);i+=1
 assert depth==0, 'unterminated source comment'
 commands=[line.strip() for line in ''.join(out).splitlines() if line.strip()]
 assert commands==['import '+m for m in EXPLICIT_IMPORTS], 'source not exactly the seven allowed imports'
 return {'module':MODULE,'sourceSha256':SOURCE_SHA256,'sourceOnlyImports':True,'explicitImports':EXPLICIT_IMPORTS,'ownDeclarations':0,'ownProofs':0}
def bind_closure(root,graph,evidence):
 # Every non-toolchain descendant is mapped from the reviewed explicit import graph.
 seen=set()
 def visit(m):
  if m in seen:return
  seen.add(m)
  for d in graph['imports'].get(m,[]):visit(d)
 for m in EXPLICIT_IMPORTS:visit(m)
 assert graph['imports'][MODULE]==EXPLICIT_IMPORTS
 objects={};accepted={}
 for m in sorted(seen):
  source=graph['source_paths'].get(m)
  if source is None:
   assert m in graph['toolchain_boundary_modules'], 'unresolved imported module '+m
   continue
  p=Path(source);parts=p.parts
  assert parts[:2]==('.lake','packages'), 'unexpected aggregator dependency package'
  pkg=parts[2];obj=root/'.lake/packages'/pkg/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean')
  assert obj.is_file(), 'missing imported object '+m
  for q in obj.parent.glob(obj.stem+'.*'):
   if q.is_file():objects[str(q.relative_to(root))]=hashlib.sha256(q.read_bytes()).hexdigest()
  if pkg=='goldbach':
   # Require earlier fresh strict external acceptance for every external ancestor.
   hits=[]
   for receipt in evidence.glob('*/receipt.json'):
    r=json.loads(receipt.read_text())
    if r.get('status')=='PASS_PINNED_EXTERNAL_MODULES' and m in r.get('objects',{}):
     for rel,h in r['objects'][m].items():
      assert (root/rel).is_file() and hashlib.sha256((root/rel).read_bytes()).hexdigest()==h
     reviewPath=receipt.parent/'independent-review.json'
     assert reviewPath.is_file(), 'external import lacks independent review '+m
     review=json.loads(reviewPath.read_text())
     assert review['status']=='PASS_INDEPENDENT_PINNED_EXTERNAL_MODULE_REVIEW' and review['receiptSha256']==hashlib.sha256(receipt.read_bytes()).hexdigest() and m in review['modules'], 'external import independent review binding mismatch'
     hits.append({'receipt':str(receipt),'sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),'independentReview':str(reviewPath),'independentReviewSha256':hashlib.sha256(reviewPath.read_bytes()).hexdigest()})
   assert hits,'external import not previously fully audited '+m
   accepted[m]=hits
 return {'objects':objects,'priorExternalAcceptance':accepted,'explicitImports':EXPLICIT_IMPORTS,'toolchainBoundary':'fixed official toolchain binary/source hashes in runtime state'}
