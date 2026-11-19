#!/usr/bin/env python3
"""Independent numerical cross-check of the selected G4 finite Facts.
Not Lean evaluation, proof compilation, or a kernel/axiom check.
"""
import argparse,ast,hashlib,importlib.util,json,re,resource,struct,subprocess,tempfile,time
from pathlib import Path
PINS={
 'cpp':'b85c657f79948597fd25a4ed2891ca1047270ca5995288ae4915023473b74cad',
 'reference':'f10dddcf8b8b4b6f9964f81562ad1fd8eb6d12a418b77e08d3ffda4c0bcf93ae',
 'npy':'406623527077e0cd424f2098713e70125795eafbee758d21f16d19d89dfb9be8',
 'P4AOriginalSavedSixthBank.lean':'d37c1a5846272475bf16bf697df46a13f3f6eb1c1aed07b62124263b063cbedc',
 'P4AOriginalSavedSixthPlanes.lean':'cc8297db54d8cdf2c22fcf7faec050d9e0ae58752322d6df729c38ff7d66314b',
 'P4AOriginalSavedSixthWordAccess.lean':'a6b10008b98ebe948aa423169f92aa4975ff478df90123ad1cbbbf5c374a3162',
 'P4AOriginalSavedSixthArchive.lean':'d37522cadea7b16c4af97607ea97345ee1bca2fc89d572f2733d22dee7fcae6a',
}
def verify(p,h):
 with p.open('rb') as f: assert hashlib.file_digest(f,'sha256').hexdigest()==h

def main():
 p=argparse.ArgumentParser();p.add_argument('--cpp',type=Path,required=True);p.add_argument('--reference',type=Path,required=True);p.add_argument('--source-dir',type=Path,required=True);p.add_argument('--npy',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 for k in ('cpp','reference','npy'):verify(getattr(a,k),PINS[k])
 for k,h in PINS.items():
  if k.endswith('.lean'):verify(a.source_dir/k,h)
 assert a.npy.stat().st_size==55625280
 archive=(a.source_dir/'P4AOriginalSavedSixthArchive.lean').read_text()
 match=re.search(r'def\s+originalHeader\s*:\s*List\s+ℕ\s*:=\s*(\[[^\]]*\])',archive,re.S);assert match
 expected=bytes(ast.literal_eval(match.group(1)));assert len(expected)==128
 with a.npy.open('rb') as f:assert f.read(128)==expected
 spec=importlib.util.spec_from_file_location('g4_fraction_reference',a.reference);ref=importlib.util.module_from_spec(spec);spec.loader.exec_module(ref)
 indexes=[0,1,2047,2048,123456,316052,632103];rows=[]
 with a.npy.open('rb') as f:
  for i in indexes:f.seek(128+88*i);rows.append(struct.unpack('<11q',f.read(88)))
 cases=[]
 for index,row in zip(indexes,rows):
  cases.append((index,'original',row,True))
  for field,value,label in [(0,399,'grid'),(7,31,'mask'),(8,row[8]+1,'signed_gap_sum'),(9,0,'old_residual_positive'),(10,0,'new_residual_positive')]:
   altered=list(row);altered[field]=value;cases.append((index,label,tuple(altered),False))
 version=subprocess.run(['g++','--version'],text=True,capture_output=True,check=True).stdout.splitlines()[0]
 with tempfile.TemporaryDirectory() as t:
  t=Path(t);binary=t/'g4_facts';rowfile=t/'row.bin'
  subprocess.run(['g++','-std=c++17','-O2','-Wall','-Wextra','-Werror',str(a.cpp),'-o',str(binary)],text=True,capture_output=True,check=True)
  accepted=rejected=0
  for index,label,row,wanted in cases:
   truth=ref.facts(row);assert truth==wanted,(index,label,truth)
   rowfile.write_bytes(struct.pack('<11q',*row));r=subprocess.run([str(binary),'--row',str(rowfile)],text=True,capture_output=True)
   assert r.returncode in (0,1),(r.returncode,r.stderr);actual=json.loads(r.stdout)['pass'];assert actual==truth,(index,label,truth,r.stdout)
   accepted+=actual;rejected+=not actual
  begin=time.monotonic();r=subprocess.run([str(binary),str(a.npy)],text=True,capture_output=True);elapsed=time.monotonic()-begin
  if r.returncode!=0:raise RuntimeError('full C++ test failed: '+str(r.returncode)+' '+r.stderr+' '+r.stdout)
  result=json.loads(r.stdout);assert result['pass'] and result['rows']==632104 and result['keys_unique']
  assert result['old_bound_all_old']+result['old_bound_via_new']==632104
  assert sum(result['third_first_witness'])==632104 and sum(result['fifth_first_witness'])==632104
  out={'status':'PASS','scope':'numeric implementations of selected G4 Facts only; not Lean or kernel evaluation',
       'source_sha256':PINS,'compiler':version,'compile_exit':0,'full_run_exit':r.returncode,
       'full_run_seconds':round(elapsed,6),'max_child_rss_kib_including_compiler':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
       'reference_cases':{'rows':indexes,'cases':len(cases),'accepted':accepted,'rejected':rejected,'method':'independent Python Fraction formulas for the 16 source fields'},
       'full_result':result,
       'limitations':['implementation correspondence to Lean is checked by source inspection and samples, not formally proved',
                      'all Lean decidable block proofs and ownerBody remain UNEVALUATED',
                      'no analytic integration, signed policy payment, downstream All22, Lean compilation, axiom check or kernel replay']}
  a.output.write_text(json.dumps(out,indent=2)+'\n')
  print('PASS',len(cases),'Fraction/C++ cases and',result['rows'],'original rows; negative signed corners',result['negative_corners'],flush=True)
if __name__=='__main__':main()
