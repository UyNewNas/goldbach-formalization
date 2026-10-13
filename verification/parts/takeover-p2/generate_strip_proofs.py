"""Emit a structurally complete proof dispatch, not numerical proof results.

Every strip is still verified by ordinary Lean kernel reduction.  This
avoids retaining a single monolithic 17572-row dependent decision term.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
lines=['import ImbalancedChen.Certificates.PairedV2FullCertificateData','','/-! Ordinary-kernel checks, partitioned into all 186 exact adopted strips.',
'No row is sampled or dropped, and no native numerical evaluator is used. -/','',
'namespace ImbalancedChen.Certificates.PairedV2.FullMask','',
'set_option maxRecDepth 100000','set_option maxHeartbeats 0','']
for k in range(186):
    index=f'(⟨{k}, by decide⟩ : Fin 186)'
    row=f'(⟨{index}, j⟩ : Row)'
    lines += [f'theorem strip{326+k}_checked : ∀ j : Fin (512 - firstU {index}),',
      f'    (makeCertificate {row} (approximation {row})).check = true := by',
      '  decide +kernel','']
lines += ['theorem strip_certificates_checked (i : Fin 186) (j : Fin (512 - firstU i)) :',
'    (makeCertificate ⟨i,j⟩ (approximation ⟨i,j⟩)).check = true := by',
'  fin_cases i']
for k in range(186):
    lines += [f'  · exact strip{326+k}_checked j']
lines += ['','end ImbalancedChen.Certificates.PairedV2.FullMask','']
(ROOT/'ImbalancedChen/Certificates/PairedV2StripCertificates.lean').write_text('\n'.join(lines),encoding='utf-8',newline='\n')
print('Generated exactly 186 exhaustive ordinary-kernel strip checks.')
