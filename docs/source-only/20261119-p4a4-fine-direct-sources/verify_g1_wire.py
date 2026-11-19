#!/usr/bin/env python3
"""Replay the original G1 producer's geometry and sum all four Q80 floors.
Numerical audit only: this does not execute Lean, establish analytic bounds,
verify box disjointness, or kernel-replay any finite proof body.
"""
import argparse, hashlib, importlib.util, json, math, re
from fractions import Fraction
from pathlib import Path
import numpy as np

PINS={
 'wire':'561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da',
 'producer':'25069573985d30beae59a1a2a89ddeb79e56f696e78a5fae5153de0bb8bd378a',
 'table':'8b57193d727e81fbdc31be1c65810a593121cdc6ec34e4c56561301515fea2e9',
}
EXPECTED_ROWS=3699127
EXPECTED_SUM=4*10601625247768616959055
BATCH=32768

def pinned(path,wanted):
 with path.open('rb') as f: got=hashlib.file_digest(f,'sha256').hexdigest()
 if got!=wanted: raise ValueError('incorrect input SHA-256: '+str(path))

def exact_ceil(q): return -((-q.numerator)//q.denominator)

def main():
 p=argparse.ArgumentParser();p.add_argument('--wire',type=Path,required=True);p.add_argument('--producer',type=Path,required=True);p.add_argument('--table',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 for path,key in [(a.wire,'wire'),(a.producer,'producer'),(a.table,'table')]:pinned(path,PINS[key])
 assert a.wire.stat().st_size==17*EXPECTED_ROWS
 spec=importlib.util.spec_from_file_location('frozen_g1_producer',a.producer)
 producer=importlib.util.module_from_spec(spec);spec.loader.exec_module(producer)
 assert producer.N==204800 and producer.D==6553600 and producer.Q==1<<80 and producer.MESH==4096 and producer.LOG_TERMS==24
 metadata=a.table.read_text()
 match=re.search(r'\bdef\s+derivativeLowerUnits\s*:\s*List\s+Nat\s*:=\s*\[([^\]]*)\]',metadata,re.S)
 assert match
 tokens=match.group(1).split(',');assert len(tokens)==8193 and all(re.fullmatch(r'\s*\d+\s*',x) for x in tokens)
 table=[int(x) for x in tokens]
 dtype=np.dtype([('lo','<u2',(4,)),('hi','<u2',(4,)),('mask','u1')]);assert dtype.itemsize==17
 data=np.memmap(a.wire,mode='r',dtype=dtype);assert len(data)==EXPECTED_ROWS
 total=0;counts={str(i):0 for i in range(9,16)};mins={'old_cube':None,'correlated_gap':None,'gate':None,'residual_to_five':None};samples=[];sampled=set()
 for start in range(0,EXPECTED_ROWS,BATCH):
  end=min(start+BATCH,EXPECTED_ROWS);batch=data[start:end]
  assert np.all((batch['mask']>=9)&(batch['mask']<=15))
  processed=0
  for mask in range(9,16):
   positions=np.flatnonzero(batch['mask']==mask);selected=batch[positions];processed+=len(selected);counts[str(mask)]+=len(selected)
   if not len(selected):continue
   lo=selected['lo'].astype(np.int64);hi=selected['hi'].astype(np.int64)
   assert np.all(hi>lo) and np.all(lo[:,3]>=3*producer.N//200) and np.all(hi[:,0]<=39*producer.N//200)
   delta,r0,r1,old_slack,gap_slack,gate_slack=producer.geometry(lo,hi,mask)
   margins={'old_cube':int(old_slack.min()),'correlated_gap':int(gap_slack.min()),'gate':int(gate_slack.min()),'residual_to_five':int((160*lo[:,3]-r1).min())}
   for k,v in margins.items():mins[k]=v if mins[k] is None else min(mins[k],v)
   for i in range(len(lo)):
    L=tuple(map(int,lo[i]));H=tuple(map(int,hi[i]));g=int(delta[i]);u=int(r0[i]);v=int(r1[i]);assert 0<u<=v and g>0
    volume_num=math.prod(H[j]-L[j] for j in range(4));volume_den=math.prod(H)
    num=16*volume_num*g*producer.D;amount=0;four=[];is_sample=mask not in sampled
    for k in range(1,5):
     A=(5-k)*u+(k-1)*v;B=(4-k)*u+k*v;div=128*L[3]
     ix=max(0,(4096*(B-3*div)+div-1)//div);assert 0<=ix<8193
     floor=num*table[ix]//(volume_den*A*B);amount+=floor
     if is_sample:
      # Independent rational version of Lean unitExpr and Nat.ceil for this row.
      R0=Fraction(u,producer.D);R1=Fraction(v,producer.D)
      left=((5-k)*R0+(k-1)*R1)/4;right=((4-k)*R0+k*R1)/4
      arg=right/Fraction(L[3],producer.N);index=max(0,exact_ceil(4096*(arg-3)))
      expr=Fraction(volume_num,volume_den)*Fraction(g,producer.D)*table[index]/(left*right)
      assert index==ix and expr.numerator//expr.denominator==floor
      four.append({'part':k,'index':ix,'floor':str(floor)})
    assert amount>0;total+=amount
    if is_sample:
     samples.append({'row_index':start+int(positions[i]),'mask':mask,'lo':L,'hi':H,'delta_average':g,'R0':u,'R1':v,'parts':four,'total':str(amount)})
     sampled.add(mask)
  assert processed==end-start
  if end%524288==0:print('checked rows',end,flush=True)
 assert sum(counts.values())==EXPECTED_ROWS and total==EXPECTED_SUM
 out={'status':'PASS','scope':'producer integer geometry plus independently reaggregated four Q80 floors; not a Lean evaluation',
      'source_sha256':PINS,'numpy_version':np.__version__,'rows':EXPECTED_ROWS,'batch_size':BATCH,'mask_counts':counts,
      'minimum_strict_slacks':mins,'sum_four_floors_Q80':str(total),'G1_original':'10601625247768616959055 / 2^78',
      'rational_formula_samples':samples,
      'limitations':['geometry uses the hash-pinned original producer implementation rather than an independent Lean checker',
       'no independent disjointness or all-record decoder proof; no proof of derivative or integral inequalities',
       'not a Lean compilation, decide evaluation, transitive axiom check or kernel replay']}
 a.output.write_text(json.dumps(out,indent=2)+'\n')
 print('PASS rows',EXPECTED_ROWS,'sum_Q80',total,flush=True)
if __name__=='__main__':main()
