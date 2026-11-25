# Original Gamma5 gates in fixed affine coordinates

For N>1 write each coordinate as log(p)/log(N), O as the sum over the original old slots, F0,F1 for the ordered fresh slots, and Tj for the tail slots. For a fixed same-Q cell let ν = codeLevel(n,c). The only cell input to the identity is log(Q)/log(N) = ν; this follows from the original cellQ = N^codeLevel and log_rpow. All N, width and tuple choices follow the choice of rank, gate, omitted slot and form. At fixed precision c ranges over the original finite RootCode n.

| Original gate | Linear form L | Intercept b | Passed at L-b = 0? | Omitted slot |
|---|---|---|---|---|
| Fresh lower i | a0 O + Fi | a0 ν | Yes | Other fresh |
| Fresh upper i | -a2 O - Fi | -a2 ν | No | Other fresh |
| Pair order | F1 - F0 | 0 | No | An old slot if present, else a tail slot |
| Bad square | O + 2 F0 + F1 | ν | Yes | A tail slot |
| Rough floor j | a0 O + Tj | a0 ν | Yes | Fresh 0 |
| Tail order i<j | Tj - Ti | 0 | Yes | Fresh 0 |

Positive and negative signs give the original margin divided by log N, exactly L-b. Each old slot retains its individual coefficient. Tail-order indices are distinct on the active program; their prime values can coincide. The number assigned to each slot is transported by the existing slotEquiv and only reassociated to a successor-sized Fin type. Removing an index uses succAbove. Nonvanishing is proved by a retained basis vector, so the selected CLM satisfies the nonzero-form requirement of the prior affine reserve.

The result connects the original one-sided properStrip to an absolute affine strip of width width/log N. Closed and open faces retain their original definition; absolute-strip majorization can include equality. The complete-product gate is already separate. A bad square at r=0 and a fresh pair-order at k=r=0 have no omitted coordinate; the geometric adapter records these alternatives. The separate unit-tail product bound applies under its own scale condition, and the empty old prefix has zero matching U4 weight. No arithmetic coprimality, unit-tail payment or selected-history total follows from this identity itself.

The manuscript source is the 20261106 release at commit a988cba584d803ae2856a0de50efb582f4f3dd6a: paper/release-20261106/en/argument.tex lines 359–407 and sieve-appendix.tex lines 584–660. This source candidate has no normal compilation, kernel replay or owned audit. The separate finite union, physical width/δ threshold choice, target-coprimality exclusion, unit-tail charge, and actual marked-sum connection remain open.
