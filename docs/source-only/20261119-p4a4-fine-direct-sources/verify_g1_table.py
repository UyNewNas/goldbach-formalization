#!/usr/bin/env python3
"""Recompute the exact 8193-entry original G1 Q80 integer recurrence.
This is independent arithmetic, not Lean compilation or analytic proof.
"""
import argparse, hashlib, json, re
from pathlib import Path

PINS={
 'P1OriginalFourthRawTableMetadata.lean':'8b57193d727e81fbdc31be1c65810a593121cdc6ec34e4c56561301515fea2e9',
 'P1OriginalFourthQ80LogBounds.lean':'459ac78b5bd93b3370b989289a3e3e613e98dae7daefb58884b1d069d6c0011f',
 'P1OriginalFourthN8193.lean':'34189a0794db9d7acd35989f28356503de5d0e5f202b2f37e1331969f44ec0cc',
}
def ceil_div(n,d):
 assert d>0
 return -((-n)//d)

def main():
 p=argparse.ArgumentParser();p.add_argument('--source-dir',type=Path,required=True);p.add_argument('--archive-json',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 for name,h in PINS.items():
  with (a.source_dir/name).open('rb') as f: assert hashlib.file_digest(f,'sha256').hexdigest()==h
 text=(a.source_dir/'P1OriginalFourthRawTableMetadata.lean').read_text()
 m=re.search(r'\bdef\s+derivativeLowerUnits\s*:\s*List\s+Nat\s*:=\s*\[([^\]]*)\]',text,re.S)
 assert m
 tokens=m.group(1).split(','); assert len(tokens)==8193
 assert all(re.fullmatch(r'\s*\d+\s*',x) for x in tokens)
 values=[int(x) for x in tokens]
 with a.archive_json.open('rb') as f:
  assert hashlib.file_digest(f,'sha256').hexdigest()=='b9fb8fdd3cdcb8ae89d00e561cb9a8ddcc5683365de773df7c36bbf31c406d36'
 archive=json.loads(a.archive_json.read_text())
 assert archive['scale']==str(1<<80) and archive['mesh']==4096 and archive['log_terms']==24
 assert len(archive['N_lower_units'])==8193
 assert [str(x) for x in values]==archive['N_lower_units']
 Q=1<<80;credit=Q;first_bad=None
 min_value=min(values);max_step=0;max_penalty=0
 for j,value in enumerate(values):
  d=8192+j;j2=j*j;d2=d*d;pn=j;pd=d;lo=0
  for k in range(24):
   lo+=(2*Q*pn)//((2*k+1)*pd)
   pn*=j2;pd*=d2
  # pn=j^49 and pd=d^49, with the zero endpoint handled exactly.
  hi=0 if j==0 else lo+24+ceil_div(2*Q*pn,49*(pd//d2)*(d2-j2))
  penalty=ceil_div((12288+j)*hi,d)
  if value+penalty!=credit:
   first_bad={'j':j,'stored':str(value),'penalty':str(penalty),'credit':str(credit)};break
  step=lo//d;max_step=max(max_step,step);max_penalty=max(max_penalty,penalty);credit+=step
 if first_bad is not None: raise AssertionError('recurrence mismatch: '+str(first_bad))
 assert values[0]==Q and values[-1]==39643994026485390435670 and min_value>0
 out={'status':'PASS','scope':'exact integer recurrence only, not Lean elaboration or analytic derivative proof',
      'source_sha256':PINS,'archive_sha256':'b9fb8fdd3cdcb8ae89d00e561cb9a8ddcc5683365de773df7c36bbf31c406d36',
      'rows':len(values),'scale':str(Q),'first':str(values[0]),'last':str(values[-1]),
      'minimum':str(min_value),'last_credit_after_step':str(credit),'max_step':str(max_step),'max_penalty':str(max_penalty),
      'checks':['8193 exact values equal registered original JSON','24 separately floored terms','ceiling of 49th-power upper tail','special zero endpoint',
                'upward-rounded penalty','left-step floor','all 8193 exact stored equalities'],
      'limitations':['does not check the analytic log/derivative inequalities, the 3,699,127-row G1 floor sum, geometric guards, Lean proof evaluation, compilation or kernel replay']}
 a.output.write_text(json.dumps(out,indent=2)+'\n')
 print('PASS 8193 exact stored recurrence equalities; last='+str(values[-1]))
if __name__=='__main__':main()
