#!/usr/bin/env python3
"""Static literal inventory for the selected All22 sources; not a Lean checker."""
import argparse,hashlib,json,re,subprocess
from fractions import Fraction
from pathlib import Path

PINS={
'CurrentUpperEighteenBudget.lean':'f8b1ad2fbb13297c55d7c12706252d7980195429',
'P4AAll22OriginalKLedger.lean':'b34635e0078592b84fb9a2b4fd4469358819dc80',
'P4AOrderedThirdPositiveRoot.lean':'269578f7681a0d83f1d13320711ddf7dc4c6fe8d',
'P4AOriginalEarlyFinitePayment.lean':'de1c9ecc19c72a87b646c83f68aea8b99caad243',
'P4AOriginalElevenOrderedPayment.lean':'854528d31fb418fd0abc769ef16f7046230e1f00',
'P4AOriginalFiniteAll22FineCofinalCoefficient.lean':'eef0d3cc4864763b14037ed8bc58721f60170583',
'P4AOriginalFiniteAll22Nineteen.lean':'abadf4d9fbbec16085deb732f4e3388e35500218',
'P4AOriginalFiniteAll22PaidSixth.lean':'cdef0be4f600a2cb88be6acd756e3d451c9eb40a',
'P4AOriginalFiniteAll22RawLedger.lean':'88a37861a9d5bdfaec4cdb34196cc0fe5f91afe2',
'P4AOriginalFiniteFallbackJointGain.lean':'fad727a357ca6965b7a481702614ed4b919fc2b8',
'P4AOriginalFull87SavedGain.lean':'9bfd401afcfcb4431d6124559e09017074f48ec3',
'P4AOriginalOrderedLaterPaid.lean':'1541b581431d83d1535eff1e6463604db4c894bb',
'P4AOriginalOrderedSavedGain.lean':'97c0595fda739e528012365e2b565b67f5004621',
'P4AOriginalR17Full87SavedEndpoint.lean':'89321bd21ab4798423aafdb54b064197e5485cda',
}
def table(text,name):
    m=re.search(r'def\s+'+name+r'\s*:\s*Fin\s+\d+\s*→\s*ℝ\s*:=\s*!\[(.*?)\]',text,re.S)
    if not m: raise ValueError('missing table '+name)
    out=[]
    for item in m.group(1).split(','):
        s=item.strip(); mm=re.fullmatch(r'(\d+)\s*/\s*(?:(\d+)\^(\d+)|(\d+))',s)
        if not mm: raise ValueError('unexpected literal '+s)
        n,b,e,d=mm.groups(); out.append({'literal':s,'exact':str(Fraction(int(n),int(b)**int(e) if b else int(d)))})
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--source-dir',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    sources={};identity=[]
    for name,expected in PINS.items():
        raw=(a.source_dir/name).read_bytes();sha=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        if sha!=expected: raise ValueError(name+' blob mismatch '+sha)
        sources[name]=raw.decode('utf-8');identity.append({'file':name,'git_blob':sha,'sha256':hashlib.sha256(raw).hexdigest()})
    budget=sources['CurrentUpperEighteenBudget.lean'];ledger=sources['P4AAll22OriginalKLedger.lean']
    positives=table(budget,'currentUpperEighteenPositive');first=table(budget,'currentUpperEighteenGains');last=table(ledger,'finalFourGains')
    assert len(positives)==4 and len(first)==18 and len(last)==4
    checks={
      'fine_raw':'P4AOriginalFiniteAll22Nineteen.exists_final_raw_upper_with_early_defect',
      'fine_early':'P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect',
      'fine_schedule':'P4AOriginalFiniteFallbackFinePPSchedule.joined',
      'root':'P4AOrderedThirdPositiveRoot.original_four_positive',
      'G4':'P4AOriginalOrderedSavedGain.exists_original_G4',
      'G7':'P4AOriginalElevenOrderedPayment.exists_original_G7_ordered_payment',
      'G8_G14':'P4AOriginalOrderedLaterPaid.exists_original_later_payment',
      'G15_G22':'P4AOriginalR17Full87SavedEndpoint.original_ordinary_saved',
      'G5_G6':'P4AOriginalFiniteFallbackJointGain.gains',
    }
    for key,term in checks.items():
        module='P4AOriginalFiniteAll22FineCofinalCoefficient.lean' if key.startswith('fine_') else ('P4AOriginalFiniteAll22PaidSixth.lean' if key in ('root','G4','G7','G8_G14') else 'P4AOriginalFiniteAll22Nineteen.lean')
        assert sources[module].count(term)==1,(key,term)
    rows=[]
    for i,v in enumerate(positives,1):
        rows.append({'kind':'positive','number':i,**v,'supplier':'P4AOrderedThirdPositiveRoot.original_four_positive','bound_scope':'four together on fresh raw root'})
    for i,v in enumerate(first+last,1):
        if i<=3: supplier='P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect';actual='lowerEarly';scope='combined three-slot payment'
        elif i==4: supplier='P4AOriginalOrderedSavedGain.exists_original_G4';actual='lowerSaved';scope='single slot'
        elif i<=6: supplier='P4AOriginalFiniteFallbackJointGain.gains';actual='upperFallback';scope='combined two-slot payment'
        elif i==7: supplier='P4AOriginalElevenOrderedPayment.exists_original_G7_ordered_payment';actual='lowerEleven';scope='single slot, replacement endpoint'
        elif i<=14: supplier='P4AOriginalOrderedLaterPaid.exists_original_later_payment';actual='lowerLater';scope='combined seven-slot payment via eight chronological stages'
        else: supplier='P4AOriginalR17Full87SavedEndpoint.original_ordinary_saved';actual='lowerEighth';scope='combined eight-slot payment via 87 sources and two successive increments'
        rows.append({'kind':'saving','number':i,**v,'supplier':supplier,'raw_signed_difference':actual,'bound_scope':scope})
    vals=lambda xs:sum((Fraction(x['exact']) for x in xs),Fraction())
    E=vals(positives)-vals(first)-vals(last)
    expected=Fraction(9979702576710911234850619807816847864907359959,1475913550962201227946780619099353215139840000)
    u=Fraction(145007961227048312210593427530128000784681,11807308407697609823574244952794825721118720000)
    slack=Fraction(71229286727542131248758574547050908572431,737956775481100613973390309549676607569920000000)
    assert E==expected and E+2*u+slack==Fraction(8452171,1250000)
    a.output.write_text(json.dumps({'status':'STATIC_SOURCE_INVENTORY_ONLY_UNCOMPILED','base_commit':'40091251b7cd76b178a311da3562ae9e757cc608','source_identity':identity,'entries':rows,'exact_arithmetic':{'quotedAll22Raw':str(E),'densityReserve':str(u),'compilerReserve':str(u),'exactSlack':str(slack),'K':str(E+2*u+slack)},'limitations':['Static source text and rational arithmetic only; individual rows of aggregate payments are not separately asserted as independently proved.','No elaboration, import closure, finite guard evaluation, kernel replay or transitive axiom check.']},ensure_ascii=False,indent=2)+'\n')
    print('PASS: 14 exact source blobs; 4 positive and 22 ordered saving literals; original two-reserve identity')
if __name__=='__main__':main()
