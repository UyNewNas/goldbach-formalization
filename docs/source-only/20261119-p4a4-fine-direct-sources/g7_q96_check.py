#!/usr/bin/env python3
"""Audit G7 recorded Q80-to-Q96 arithmetic; no Lean execution or Q80 proof."""
import argparse, hashlib, json, math
from fractions import Fraction as F
from pathlib import Path

SOURCES = [('singleton','sixth-license-family-20261009-exact.witness.json'),
 ('singleton','sixth-license-family-20261009-mask50-residual.witness.json'),
 ('pair17','sixth-pair17-winner-20261009-exact.witness.json'),
 ('pair12','sixth-pair12-ascending-cell-20261009.witness.json'),
 ('tent33','sixth-tent33-ascending-20261009.witness.json')]
LOG='sixth-log-moment-jensen-20261009.witness.json'
NAV='sixth-pair12-ascending-cell-20261009.navigation.json'

def floor(x): return x.numerator // x.denominator

def at(kind, raw):
    x,y,z,a,c,r = map(F,raw)
    if kind=='pair12':
        t=(x,y,z,a,c,r)
    else:
        t=(x,y,z,(1-x)/2-y-z-3*a/2+c/2,(a-c)/2,r)
    R=(1+t[0])/2
    if kind=='pair17': R=F(57,64)-3*(t[0]+t[4])/2
    if kind=='pair12': R=(1+t[2]+t[3])/2
    M=((1+t[0]+t[5])/2 if kind=='tent33' else sum(t[:5],F(0))+4*t[5])-F(1,10**6)
    gap=M-R
    fac=(R-sum(t,F(0)),M-sum(t,F(0)),*t)
    return gap,fac

def factor_q80(ys, gs):
    # Independent transcription of the manuscript duplicated-node formula.
    peak=max(ys); assert min(ys)>0 and peak>0
    ys=[1-y/peak for y in ys]; G=sum(gs,F(0))
    moments=[F(0)]*7
    for gi,yi in zip(gs,ys):
        h=[F(1)]+[F(0)]*6
        for z in [*ys,yi]:
            for k in range(1,7): h[k]+=z*h[k-1]
        for k in range(7): moments[k]+=gi*h[k]
    moments=[v/G/math.comb(7+k,k) for k,v in enumerate(moments)]
    assert moments[0]==1
    m=moments[1]
    gap=sum(((moments[k]-m**k)/k for k in range(2,7)),F(0))
    assert gap>=0
    return floor(gap*2**80)

def physical_volume(vs):
    # Determinant of six physical edge vectors; no chart or factorial twice.
    mat=[[vs[c+1][r]-vs[0][r] for c in range(6)] for r in range(6)]
    det=F(1)
    for col in range(6):
        pivot=next((r for r in range(col,6) if mat[r][col]),None)
        assert pivot is not None
        if pivot!=col:
            mat[col],mat[pivot]=mat[pivot],mat[col]; det=-det
        d=mat[col][col];det*=d
        for row in range(col+1,6):
            ratio=mat[row][col]/d
            for j in range(col+1,6): mat[row][j]-=ratio*mat[col][j]
    return abs(det)/math.factorial(6)

def check(root,receipts):
    items=json.loads(receipts.read_text()); selected={x['name']:x for x in items}
    names=[x[1] for x in SOURCES]+[LOG,NAV]
    assert len(set(names))==7
    hashes={}
    for name in names:
        b=(root/name).read_bytes(); rec=selected[name]; digest=hashlib.sha256(b).hexdigest()
        assert len(b)==rec['bytes'] and digest==rec['sha256']
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert git==rec['git_blob_sha1']; hashes[name]={'sha256':digest,'git_blob_sha1':git,'bytes':len(b)}
    j=json.loads((root/LOG).read_text()); assert (j['log_moment_degree'],j['exp_degree'],int(j['log_floor_denominator']),int(j['final_floor_denominator']))==(6,3,2**80,2**96)
    records={}
    for r in j['records']:
        key=(r['group'],r['cell_id'],r['simplex_id']); assert key not in records
        records[key]=r
    assert len(records)==len(j['records'])==2631
    totals=[]; seen=set(); oldtotal=newtotal=0; total_strict=0; sampled_q80=0
    for group,name in SOURCES:
        doc=json.loads((root/name).read_text()); cells=doc.get('cells',[doc])
        for cell in cells:
            cid=cell.get('cell_id','pair12-fixed'); vals=[at(group,v) for v in cell['vertices']]
            old_sum=new_sum=strict=0
            for idx,s in enumerate(cell['simplices']):
                assert idx==s['simplex_id'] and len(s['vertex_ids'])==7
                key=(group,cid,idx); assert key in records and key not in seen; seen.add(key); r=records[key]
                gs=[vals[i][0] for i in s['vertex_ids']]; G=sum(gs,F(0)); assert min(gs)>=0 and G>0
                means=[]
                for f in range(8):
                    ys=[vals[i][1][f] for i in s['vertex_ids']]; assert min(ys)>=F(53,4608)
                    means.append((sum(ys,F(0))+sum((g*y for g,y in zip(gs,ys)),F(0))/G)/8)
                vol=F(s['physical_volume']); assert vol>0
                assert physical_volume([vals[i][1][2:] for i in s['vertex_ids']])==vol
                old=4*vol*G/7/math.prod(means)
                oldfloor=floor(old*2**96); assert oldfloor==int(r['old_floor_Q96'])
                ts=list(map(int,r['log_gap_factor_floors_Q80'])); assert len(ts)==8 and min(ts)>=0
                for f in range(8):
                    ys=[vals[i][1][f] for i in s['vertex_ids']]
                    assert factor_q80(ys,gs)==ts[f]
                    sampled_q80+=1
                t=F(sum(ts),2**80); new=old*(1+t+t*t/2+t*t*t/6)
                newfloor=floor(new*2**96); assert newfloor==int(r['new_floor_Q96']) and newfloor>=oldfloor
                old_sum+=oldfloor; new_sum+=newfloor; strict+=newfloor>oldfloor
            totals.append(dict(group=group,cell=cid,rows=len(cell['simplices']),old_Q96=str(old_sum),new_Q96=str(new_sum),strict_improvements=strict))
            oldtotal+=old_sum; newtotal+=new_sum; total_strict+=strict
    assert set(records)==seen and len(totals)==11
    assert oldtotal==1201130581437641342320905
    assert newtotal==1208544915921356327515701
    return {'scope':'EXTERNAL_NUMERIC_DIAGNOSTIC_NOT_LEAN','sources':hashes,'cells':totals,'rows':len(seen),
            'old_total_Q96':str(oldtotal),'new_total_Q96':str(newtotal),'increment_Q96':str(newtotal-oldtotal),
            'strict_improvement_rows':total_strict,
            'q80_factors_recomputed':sampled_q80,'all_q80_values_recomputed':sampled_q80==2631*8,'all_physical_determinant_volumes_recomputed':True,'full_geometry_or_admission_proved':False,
            'compiler_or_kernel_check':False}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--receipts',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=check(a.root,a.receipts);a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('sources','cells')}))
