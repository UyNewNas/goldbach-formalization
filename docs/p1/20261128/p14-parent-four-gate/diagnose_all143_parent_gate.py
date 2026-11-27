import subprocess,re,json,hashlib
from pathlib import Path
repo='/workspace/p14-continue-20261128';head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
blocks=[];total=0;failures=[]
for k in range(143):
 name=f'ImbalancedChen/Data/P1HistoricalFifthSavedDataBlock{k:03d}.lean'
 raw=subprocess.check_output(['git','show',f'{head}:{name}'],cwd=repo)
 rows=re.findall(r'⟨\s*(-?\d+),\s*!\[([^\]]+)\],\s*(-?\d+),\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)\s*⟩',raw.decode())
 assert len(rows)==(2048 if k<142 else 1817),(k,len(rows))
 bad=[]
 for idx,(grid,coords,mask,d,A,B) in enumerate(rows):
  lo=[int(s.strip()) for s in coords.split(',')];assert len(lo)==5
  m=int(mask);S=sum(v for i,v in enumerate(lo) if m>=0 and m>>i&1)
  if min(6400+16*S,11400-48*S)>32*(sum(lo)+4*lo[4]):bad.append(idx)
 blocks.append(dict(block=k,rows=len(rows),source_sha256=hashlib.sha256(raw).hexdigest(),parentFourGate_failures=bad))
 failures.extend((k,idx) for idx in bad);total+=len(rows)
assert total==292633,total
r=Path('/workspace/p1-complete-proof/20261128-p14-parent-four-gate')
x=dict(status='PYTHON_LINEAR_DIAGNOSTIC_ONLY_NOT_FORMAL_NOT_NPY_AUTHENTICITY',commit=head,total_rows=total,blocks=blocks,failures=failures,sorting_or_deduplication_performed=False,parent_gate_formal_theorem_already_accepted=True,archive_gate_formal_certificate_not_yet_supplied=True)
(r/'ALL143_PARENT_GATE_DIAGNOSTIC.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(rows=total,blocks=len(blocks),parent_gate_failures=len(failures),status=x['status'])))
