#!/usr/bin/env python3
"""Recompute the registered G4 Q80 floor sum from 632104 archived rows.
Exact integer arithmetic only; not a Lean check and does not rederive gaps or geometry.
"""
import argparse, ast, hashlib, itertools, json, math, mmap, struct
from pathlib import Path

SHA='406623527077e0cd424f2098713e70125795eafbee758d21f16d19d89dfb9be8'
SIZE=55625280
EXPECTED=1163968980828875260040
SOURCE_HASHES={
 'P4AOriginalSavedSixthBank.lean':'d37c1a5846272475bf16bf697df46a13f3f6eb1c1aed07b62124263b063cbedc',
 'P4AOriginalSavedSixthPlanes.lean':'cc8297db54d8cdf2c22fcf7faec050d9e0ae58752322d6df729c38ff7d66314b',
 'P4AOriginalSavedSixthWordAccess.lean':'a6b10008b98ebe948aa423169f92aa4975ff478df90123ad1cbbbf5c374a3162',
 'P4AOriginalSavedSixthArchive.lean':'d37522cadea7b16c4af97607ea97345ee1bca2fc89d572f2733d22dee7fcae6a',
}

def corner_sum(row):
 """Independently evaluate all 64 signed corner gaps in units of 1/102400."""
 lo=list(row[1:7]); mask=row[7]; branches=[]
 for m in range(1,32):
  sm=sum(2*lo[j]+1 for j in range(5) if (m>>j)&1)
  asc=51200+64*sm; desc=91200-192*sm
  branches.append(0 if asc<=desc and asc<=61200 else 1 if desc<=61200 else 2)
 gaps=[]
 for bits in itertools.product((0,1),repeat=6):
  t=[lo[j]+bits[j] for j in range(6)]
  def select(m,k): return sum(t[j] for j in range(k) if (m>>j)&1)
  new_sum=select(mask,6)
  new=min(51200+128*new_sum,91200-384*new_sum)
  old=[61200-96*t[2]]
  for m,branch in enumerate(branches,1):
   sm=select(m,5);old.append((51200+128*sm,91200-384*sm,61200)[branch])
  gaps.append(new-max(old))
 return {'sum':sum(gaps),'min':min(gaps),'max':max(gaps),'negative_corners':sum(g<0 for g in gaps)}

def main():
 p=argparse.ArgumentParser();p.add_argument('--npy',type=Path,required=True);p.add_argument('--source-dir',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 for name,wanted in SOURCE_HASHES.items():
  assert hashlib.sha256((a.source_dir/name).read_bytes()).hexdigest()==wanted
 assert a.npy.stat().st_size==SIZE
 with a.npy.open('rb') as f:
  assert hashlib.file_digest(f,'sha256').hexdigest()==SHA
  f.seek(0)
  assert f.read(8)==b'\x93NUMPY\x01\x00'
  n=struct.unpack('<H',f.read(2))[0];header=ast.literal_eval(f.read(n).decode('latin1').strip())
  assert header=={'descr':'<i8','fortran_order':False,'shape':(632104,11)}
  offset=10+n; assert offset==128 and offset+632104*11*8==SIZE
  total=0;min_gap=None;negative_gaps=0;first=None;samples=[]
  chosen={0,1,2047,2048,123456,316052,632103}
  with mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as mm:
   view=memoryview(mm)[offset:]
   try:
    for idx,row in enumerate(struct.iter_unpack('<11q',view)):
     grid,*tail=row;lo=tail[:6];mask=tail[6];ds,old,new=tail[7:]
     assert grid==400 and all(8<=x for x in lo) and lo[0]+1<=78
     assert all(lo[j+1]+1<=lo[j] for j in range(5)) and 32<=mask<64 and old>0 and new>0
     # Rational floor equals Python integer // for positive denominator, even when ds < 0.
     denom=16*old*new*math.prod(x+1 for x in lo)
     numerator=(1<<80)*102400*ds
     floor=numerator//denom; total+=floor
     min_gap=ds if min_gap is None else min(min_gap,ds)
     negative_gaps+=int(ds<0)
     if idx==0: first={'row':list(row),'numerator':str(numerator),'denominator':str(denom),'floor80':str(floor)}
     if idx in chosen:
      sample=corner_sum(row); assert sample['sum']==ds
      samples.append({'row_index':idx,'recorded_gap_sum':ds,**sample})
    assert idx+1==632104
   finally: view.release()
 assert total==EXPECTED
 out={'status':'PASS','scope':'stored rational Q80 sum only; not a Lean computation or proof',
      'input':{'sha256':SHA,'bytes':SIZE,'npy_header':header,'data_offset':offset},
      'rows':632104,'sum_floor80':str(total),'G4_literal':'145496122603609407505 / 2^77',
      'min_stored_corner_gap_sum':min_gap,'negative_gap_sum_rows':negative_gaps,'first_row_trace':first,
      'simple_row_checks':'grid, lower coordinate/order, mask range and positive residuals',
      'source_sha256':SOURCE_HASHES,'corner_gap_samples':samples,
      'limitations':['64 signed corner gaps independently rederived only for the seven listed rows; other gap sums are accepted as recorded',
                     'does not verify gate/parent/residual certificates, row uniqueness, real integral or Lean decide bodies',
                     'no source compilation, transitive axiom check or kernel replay']}
 a.output.write_text(json.dumps(out,indent=2)+'\n')
 print('PASS rows=632104 sum_floor80='+str(total)+' negative_gap_sum_rows='+str(negative_gaps))
if __name__=='__main__':main()
