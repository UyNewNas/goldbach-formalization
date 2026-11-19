#!/usr/bin/env python3
"""Independently rederive G14's 536 rational simplex rows; no Lean execution."""
import argparse, hashlib, json, math, sys
from fractions import Fraction as F
from pathlib import Path

PINS = {
 'P2OriginalLaterSixthArchive.lean': 'b76b2559bcff838a680d0b931fba5817d709da35d395eaa21ca31190be38128d',
 'P2OriginalLaterSixthKernel.lean': '5cb132dd52bac5cd4c6bf5914dff23b4f3da78db33df7b752adae8c556dadbdd',
 'P4AOriginalSixthLaterLiteral.lean': '1a6afe8b9ca4a361d34bd6465a0d0352228bf1b2395bea8dfb4500ebf640e5d5',
 'sixth-nonsingleton-freecap-20261009.witness.json': '18b38a75557fbd2633f95ff6a482d9fd8fd6d03ae33c6ca64d5e5d2eb21be8ae',
}
def pinned(path):
    h=hashlib.sha256(path.read_bytes()).hexdigest()
    if h!=PINS[path.name]: raise ValueError(f'{path}: unexpected SHA-256 {h}')
    return h

def det(q):
    # Scale each row to integers; fraction-free Bareiss elimination retains det exactly.
    ints=[]; scale=1
    for row in q:
        d=math.lcm(*(x.denominator for x in row)); scale*=d
        ints.append([int(x*d) for x in row])
    a=ints; sign=1; prev=1
    for k in range(5):
        if a[k][k]==0:
            z=next((j for j in range(k+1,6) if a[j][k]),None)
            if z is None: return F(0)
            a[k],a[z]=a[z],a[k]; sign=-sign
        pivot=a[k][k]
        for i in range(k+1,6):
            for j in range(k+1,6):
                num=a[i][j]*pivot-a[i][k]*a[k][j]
                quot,rem=divmod(num,prev)
                if rem: raise ArithmeticError('nonexact Bareiss division')
                a[i][j]=quot
            a[i][k]=0
        prev=pivot
    return F(sign*a[5][5],scale)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--source-dir',type=Path,required=True)
    ap.add_argument('--witness',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    hashes={n:pinned(args.source_dir/n) for n in list(PINS)[:3]}
    hashes[args.witness.name]=pinned(args.witness)
    doc=json.loads(args.witness.read_text()); Q=1<<96
    assert doc['coordinates']=='physical t; Jacobian1' and int(doc['Q'])==Q
    assert len(doc['cells'])==4
    patterns=[1355,1355,1867,1867]; counts=[60,153,322,1]
    results=[]
    for i,cell in enumerate(doc['cells']):
        assert cell['pattern']==patterns[i] and len(cell['simplices'])==counts[i]
        v=[[F(q) for q in x] for x in cell['vertices']]
        assert all(len(x)==6 for x in v)
        # Kernel.lower = R17; upper = a33,d33,a33,d33 minus eta.
        vf=[]
        for t in v:
            lo=F(57,64)-F(3,2)*(t[0]+t[4])
            hi=(F(1,2)+t[0]/2+t[5]/2 if i%2==0 else F(57,64)-F(3,2)*(t[0]+t[5]))-F(1,1000000)
            gap=hi-lo; sm=sum(t,F(0)); fac=[lo-sm,hi-sm,*t]
            vf.append((gap,fac))
        total=0
        for idx,s in enumerate(cell['simplices']):
            ids=s['vertex_ids']; assert s['simplex_id']==idx and len(ids)==7 and all(0<=j<len(v) for j in ids)
            pts=[v[j] for j in ids]; gs=[vf[j][0] for j in ids]; fs=[vf[j][1] for j in ids]
            mat=[[pts[r+1][c]-pts[0][c] for c in range(6)] for r in range(6)]
            determinant=det(mat); assert determinant!=0
            vol=abs(determinant)/math.factorial(6); assert vol==F(s['physical_volume'])
            assert all(g>=0 for g in gs) and sum(gs)>0
            assert all(f>=F(53,4608) for row in fs for f in row)
            mean_gap=sum(gs)/7; assert mean_gap==F(s['mean_gap'])
            means=[(sum(row[j] for row in fs)+sum(gs[k]*fs[k][j] for k in range(7))/sum(gs))/8 for j in range(8)]
            assert means==[F(x) for x in s['weighted_factor_means']]
            exact=4*vol*mean_gap/math.prod(means); assert exact==F(s['exact_lower'])
            num=(exact*Q).numerator//(exact*Q).denominator
            assert num==int(s['floor_Q96']); total+=num
        assert F(total,Q)==F(cell['gain_lower'])
        results.append({'piece':15+i,'pattern':cell['pattern'],'simplex_count':counts[i],'vertex_count':len(v),'floor_sum_Q96':str(total)})
        print(f'piece {15+i}: {counts[i]} simplices verified',flush=True)
    out={'status':'PASS','scope':'G14 pieces 15-18; exact Python rational arithmetic, not Lean compilation or kernel replay',
      'source_sha256':hashes,'checks':['identity and original piece labels/counts','simplex IDs and bounds','nonzero determinant and exact physical volume','gap nonnegative at all vertices and positive sum','eight factors >= 53/4608 at all simplex vertices','mean gap, all eight weighted means, exact Jensen lower, Q96 floor and piece sum'],
      'pieces':results,'total_Q96':str(sum(int(x['floor_sum_Q96']) for x in results)),
      'limitations':['Does not establish the real integral theorem, source gate/triangulation coverage, disjointness, complete All22 policy instantiation, Q80 correction, Lean compilation or kernel replay.']}
    args.output.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
    print('total Q96 numerator:',out['total_Q96'])
if __name__=='__main__': main()
