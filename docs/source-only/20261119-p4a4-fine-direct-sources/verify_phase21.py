"""Exact source/ledger comparison only. Does not elaborate or evaluate Lean."""
import argparse, hashlib, json, re
from fractions import Fraction as F
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--inputs', type=Path, required=True)
p.add_argument('--paper-root', type=Path, required=True)
p.add_argument('--lean-root', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
meta = json.loads(a.inputs.read_text(encoding='utf-8'))

def blob(path):
    b = path.read_bytes()
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def checked(path, expected):
    actual = blob(path)
    if actual != expected:
        raise ValueError(f'{path}: blob {actual} != {expected}')
    return path.read_text(encoding='utf-8-sig')

replay = checked(a.paper_root/'replay_selected_ledger.py', meta['replay_git_blob'])
eighteen = checked(a.lean_root/'CurrentUpperEighteenBudget.lean', meta['lean_eighteen_git_blob'])
ledger = checked(a.lean_root/'P4AAll22OriginalKLedger.lean', meta['lean_all22_git_blob'])
pos = {r['name']:json.loads(checked(a.paper_root/r['name'],r['sha'])) for r in meta['positive_sources']}
entries = re.findall(r"\('([^']+)','([^']+)','([^']+)'\)",
                     replay.split('    savings = [',1)[1].split('    upper_rows =',1)[0])
assert len(entries) == len(meta['savings']) == 22

def array(text, name):
    block = re.search(r'def\s+'+re.escape(name)+r'\s*:\s*Fin\s+\d+\s*→\s*ℝ\s*:=\s*!\[(.*?)\]',text,re.S)
    if not block: raise ValueError('missing array '+name)
    terms = []
    for numerator, denominator in re.findall(r'(\d+)\s*/\s*(2\s*\^\s*\d+|\d+)',block.group(1)):
        d = denominator.replace(' ','')
        terms.append(F(int(numerator), 2**int(d.split('^')[1]) if '^' in d else int(d)))
    return terms

positive = array(eighteen,'currentUpperEighteenPositive')
savings = array(eighteen,'currentUpperEighteenGains')+array(ledger,'finalFourGains')
assert len(positive)==4 and len(savings)==22
ext = pos['certify_extended_prefix.json']
tail = pos['numerical-primitive-adversarial-20261009.json']
paper_positive = [4/F(ext['theta']),F(ext['first_integral_upper_exact']),
                  F(ext['third_integral_upper_exact']),F(tail['independent_tail_upper_Q112'])]
assert positive == paper_positive

groups = [
 ('early fourth + old/new fifth', 'P4AOriginalEarlyHistoricalFloors.historical_payment; P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect'),
 ('early fourth + old/new fifth', 'P4AOriginalEarlyHistoricalFloors.historical_payment; P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect'),
 ('early fourth + old/new fifth', 'P4AOriginalEarlyHistoricalFloors.historical_payment; P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect'),
 ('saved sixth', 'P4AOriginalOrderedSavedGain.exists_original_G4; P4AOriginalFiniteAll22PaidSixth.lowerSaved_eq_paid_source'),
 ('second upper fallback', 'P4AOriginalFiniteFallbackSecondGain.gain; P4AOriginalFiniteFallbackJointGain.gains'),
 ('third upper fallback', 'P4AOriginalFiniteFallbackThirdGain.gain; P4AOriginalFiniteFallbackJointGain.gains'),
 ('ordered G7 replacement', 'P4AOriginalElevenOrderedPayment.exists_original_G7_ordered_payment; P4AOriginalFiniteAll22RawLedger.lowerEleven_eq_paid_source'),
] + [('seven sixth slots jointly across eight epochs', 'P4AOriginalOrderedLaterPaid.exists_original_later_payment; P2OriginalLaterSixthStageMass.seven_slots_le_eight_stage_integrals')]*7 + [('eight eighth-source slots jointly', 'P4AOriginalFull87SavedGain.original_saved_gain_q96; P4AOriginalFiniteAll22Nineteen.savedGain_eq_final_eight_slots; P4AOriginalFull87UpperDispatch.lowerEighth_eq_paid_source')]*8
result = []
for i, ((ident,filename,field), row, candidate, group) in enumerate(zip(entries,meta['savings'],savings,groups),1):
    assert (ident,filename,field)==(row['id'],row['file'],row['field'])
    obj = json.loads(checked(a.paper_root/filename,row['sha']))
    for part in field.split('.'): obj=obj[part]
    assert F(obj)==F(row['value'])==candidate, (i,ident,obj,candidate)
    result.append({'original_index':i,'id':ident,'paper_file':filename,'paper_field':field,
                   'paper_git_blob':row['sha'],'value':str(candidate),
                   'actual_supplier_group':group[0],'source_endpoint':group[1],
                   'verification':'exact numeric/source identity only; proof and full closure uncompiled'})

baseline=pos['positive-pair-deletion-improvement-assembly-20261010.json']['selected_result']
current=pos['corpus-renewal-improvement-assembly-20261010.json']['selected_result']
def scalar(name):
    m=re.search(r'def\s+'+name+r'\s*:\s*ℝ\s*:=\s*(\d+)\s*/\s*(\d+)',ledger)
    if not m: raise ValueError(name)
    return F(int(m.group(1)),int(m.group(2)))
E=sum(positive,F(0))-sum(savings,F(0))
ud,uc,slack=scalar('densityReserve'),scalar('compilerReserve'),scalar('exactSlack')
assert E==F(current['new_upper_raw_endpoint'])==F(baseline['new_upper_raw_endpoint'])
assert ud==F(current['upper_density_approximation_budget'])
assert uc==F(current['upper_compiler_budget'])
assert slack==F(current['remaining_upper_slack'])
assert ud==F(baseline['upper_density_approximation_budget'])
assert uc==F(baseline['upper_compiler_budget'])
assert slack==F(baseline['remaining_upper_slack'])
assert F(current['safe_K'])==F(8452171,1250000) and F(current['safe_c'])==F(49044063,25000000)
assert F(baseline['safe_K'])==F(current['safe_K'])
assert F(baseline['safe_c'])==F(current['previous_safe_c'])==F(12258223,6250000)
assert E+ud+uc+slack==F(current['safe_K']) and ud>0 and uc>0 and slack>0
positive_names=['ordinary root 4/theta','first-stop integral','compact third integral','complete third tail']
positive_fields=['4/theta','first_integral_upper_exact','third_integral_upper_exact','independent_tail_upper_Q112']
positive_files=['certify_extended_prefix.json']*3+['numerical-primitive-adversarial-20261009.json']
positive_rows=[{'original_index':i+1,'id':positive_names[i],'paper_file':positive_files[i],
                'paper_field':positive_fields[i],'value':str(value),
                'source_endpoint':'P4AOriginalFourPositiveEndpoints.actual_positive_entry_le_original; P4AOrderedThirdPositiveRoot.original_four_positive',
                'verification':'exact numeric/source identity only; proof and full closure uncompiled'}
               for i,value in enumerate(positive)]
output={'schema':'p4a4-26-numeric-source-comparison-v1','paper_commit':meta['paper_commit'],
 'lean_status':'SOURCE_ONLY_UNCOMPILED','positive':positive_rows,
 'savings':result,'raw_endpoint':str(E),'density_reserve':str(ud),'compiler_reserve':str(uc),
 'slack':str(slack),'same_numeric_value_but_separate_reserves':ud==uc,
 'baseline_c':str(F(baseline['safe_c'])),'final_c':str(F(current['safe_c'])),
 'scope':'Exact source bytes and rational values only; no numerical certificate replay, Lean elaboration, kernel check, transitive axiom check, or independent mathematical proof review.'}
a.output.write_text(json.dumps(output,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print('source_blobs_verified', 3+len(meta['positive_sources'])+len(entries))
print('positive_values_equal',len(positive))
print('saving_values_equal_in_original_order',len(result))
print('raw_endpoint_and_two_reserves_and_slack_match',True)
print('lean_elaboration_or_kernel',False)
