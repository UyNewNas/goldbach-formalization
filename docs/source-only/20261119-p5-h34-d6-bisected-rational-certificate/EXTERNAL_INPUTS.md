# P5.6 h34 — external input ledger (D6 bisected rational packet)

**New external analytic/number-theory inputs: NONE.**

Fixed dependencies consumed (not reimplemented, and not newly verified):
- Manuscript-local `ImbalancedChen.P2EnhancedSeedInheritedCellBounds.d6_rational_cell_integral_lower` and `continuousOn_d6OuterSlice` from pinned source blob `102ae477b91160148a3476f10eaa105d4dbb05ac`. Exact real domain [50/227,100/353], two-term rational log lower series and same-Q geometry are unchanged.
- `ImbalancedChen.Certificates.RationalLogCertificate.check_sound`, reached through the previous theorem; it uses Mathlib's original log series. No custom axiom.
- `ImbalancedChen.Part5OriginalH430ActualD6RationalLower.actual_lambda_ge_d6_over_five`, from previous source blob `ff7ffcff74294741b267b4f64f9128fb5c36de59`.
- Mathlib interval-integral additivity, continuous-on interval integrability, rational casts and `norm_num`.

Manuscript-INTERNAL and still open: original seven-integral total >= 0.65 (i.e. lambda >= 0.13); true analytic fixed 0.020249 intercept; frozen F dominance on all seed cells; retention/Buchstab/bank CLOSED-CELL successor; original U3/U4 owner/count/full/selected/inherited filters and exclusion payments; same-Q/PP, native-history, integral–Theta–count and common 430+11 refinement.

No PNT/Mertens/BV theorem is implemented or reclassified. Exact assumptions of reused inputs, toolchain and frozen manuscript are not changed.
