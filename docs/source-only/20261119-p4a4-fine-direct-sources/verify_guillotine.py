#!/usr/bin/env python3
"""Replay the pinned G1 midpoint checker and compare with a Python reference.
This numerical test does not elaborate Lean or prove the checker sound.
"""
import argparse, hashlib, json, random, resource, struct, subprocess, tempfile, time
from pathlib import Path
PINS={
 'cpp':'70b1ff17ae8392476b0a8cfaa92d36ee637fcb64d8ce41e7b308e3fd9f81e499',
 'lean':'6c35152304371c09efa877a6ab24a45a3e517bb92f7c4018266d7113c92a08c0',
 'wire':'561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da',
}
def pinned(p,h):
 with p.open('rb') as f: assert hashlib.file_digest(f,'sha256').hexdigest()==h

def reference(rows,a=(0,0,0,0),b=(65536,65536,65536,65536),fuel=64):
 if len(rows)<=1:return True
 if fuel==0:return False
 for dim in range(4):
  if b[dim]-a[dim]<=1:continue
  mid=(a[dim]+b[dim])//2
  if all(r[1][dim]<=mid or mid<=r[0][dim] for r in rows):break
 else:return False
 left=[r for r in rows if r[1][dim]<=mid];right=[r for r in rows if not r[1][dim]<=mid]
 bl=list(b);bl[dim]=mid;ar=list(a);ar[dim]=mid
 return reference(left,a,tuple(bl),fuel-1) and reference(right,tuple(ar),b,fuel-1)

def mkbox(lo,hi):return ((lo,)*4,(hi,)*4,9)
def generate():
 yield []
 yield [mkbox(128,256)]
 yield [mkbox(128,256),mkbox(256,384)]
 yield [mkbox(100,200),mkbox(200,300)]
 yield [mkbox(128,256),mkbox(192,320)]
 rng=random.Random(20261120)
 for i in range(320):
  n=2+rng.randrange(7);rows=[]
  for j in range(n):
   lo=tuple(32*rng.randrange(32) for _ in range(4))
   hi=tuple(lo[k]+32*(1+rng.randrange(4)) for k in range(4))
   rows.append((lo,hi,9+rng.randrange(7)))
  if i%4==0: rows[-1]=rows[0]
  yield rows

def main():
 p=argparse.ArgumentParser();p.add_argument('--cpp',type=Path,required=True);p.add_argument('--lean',type=Path,required=True);p.add_argument('--wire',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 for k in PINS:pinned(getattr(a,k),PINS[k])
 assert a.wire.stat().st_size==62885159
 version=subprocess.run(['g++','--version'],text=True,capture_output=True,check=True).stdout.splitlines()[0]
 with tempfile.TemporaryDirectory() as tmp:
  tmp=Path(tmp);binary=tmp/'check';test=tmp/'micro.bin'
  compile_cmd=['g++','-std=c++17','-O2','-Wall','-Wextra','-Werror',str(a.cpp),'-o',str(binary)]
  subprocess.run(compile_cmd,check=True,capture_output=True,text=True)
  cases=accept=reject=0
  for rows in generate():
   expected=reference(rows)
   with test.open('wb') as f:
    for lo,hi,mask in rows:f.write(struct.pack('<8HB',*lo,*hi,mask))
   p=subprocess.run([str(binary),'--micro',str(test)],text=True,capture_output=True)
   assert p.returncode in (0,1),(p.returncode,p.stderr)
   actual=json.loads(p.stdout)['pass'];assert actual==expected,(cases,rows,expected,p.stdout)
   cases+=1;accept+=actual;reject+=not actual
  assert accept and reject
  start=time.monotonic();p=subprocess.run([str(binary),str(a.wire)],text=True,capture_output=True);elapsed=time.monotonic()-start
  if p.returncode!=0:raise RuntimeError('full run failed '+str(p.returncode)+' '+p.stderr+' '+p.stdout)
  full=json.loads(p.stdout);assert full['pass'] and full['rows']==3699127 and full['singletons']==3699127
  assert full['max_depth']<=64 and full['nodes']==2*full['cuts']+1
  out={'status':'PASS','scope':'independent numerical replay of exact Lean source check, not Lean compilation or kernel evaluation',
       'input_sha256':PINS,'compiler':version,'compile_exit':0,'full_run_exit':p.returncode,
       'full_run_seconds':round(elapsed,6),'max_child_rss_kib_including_compiler':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
       'crosscheck':{'seed':20261120,'cases':cases,'accepted':accept,'rejected':reject,'reference':'direct ordered Python translation of the Lean recursive predicate'},
       'full_result':full,
       'notes':['C++ uses in-place partition; Lean filters preserve order, but cut selection and membership are permutation invariant.',
                'This only checks the finite midpoint decision on the exact bytes. The Lean soundness theorem and all other proof bodies were not evaluated.']}
  a.output.write_text(json.dumps(out,indent=2)+'\n')
  print('PASS',cases,'micro-cases and',full['rows'],'original rows; nodes',full['nodes'],'depth',full['max_depth'])
if __name__=='__main__':main()
