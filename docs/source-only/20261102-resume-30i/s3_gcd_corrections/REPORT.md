# I s3_gcd_corrections: original close-pair deletion under the actual shift cutoff

`local_step_complete=true` for the specified close-pair deletion and its residual insertion; `task_complete=false`, `broad_S3_task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`. This is a source proposal requiring independent review. No compiler, build, CI, checker, finite/numerical execution, quota query, subagent, or commit was run. Only this I task directory was written. Assigned model/effort: `gpt-6-astra` / `xhigh`; assignment is the evidence, not independent runtime attestation.

Branch and HEAD read at delivery are `codex/proof-continuation-20261015`, `25afcbff11562df51ef7ac5113c879123fcd64c6`. Current production and older sources were read without changes. Exact raw byte pins and installation targets are in `REGISTRY.json`.

## Original obligation and chosen scope

The original body is `paper/source/manuscript-body.tex`, proposition `prop:current-medium`, lines 125–166. The detailed proof is `paper/source/modules/distribution-medium-completion-20261010.txt`: lines 114–124 supply the original Lambda and occupied-block geometry; 156–160 require exact-product deletion before Cauchy; 169–181 put the logarithmic coefficient/nonzero-shift cutoff before the three rough/gcd exclusions and the close-pair restriction; 183–189 restore precisely two off-diagonal single zeros; 251–257 require payment after the original outside Cauchy multiplier.

H has implemented and independently source-reviewed the actual deleted diagonal/two-single-zero restoration payment. The chronologically earliest still-missing obligation is the large-coefficient/nonzero-shift cutoff estimate at lines 169–171. That estimate is **not** completed here. This delivery advances the independently executable close-pair deletion at lines 179–181, under the literal cutoffs required by that passage. The cutoff complement is independently defined, reconstructed, and retained; no assertion that it is small is introduced. This distinction is why the broad assigned task remains open.

In manuscript notation `N=atom.U`, `M=atom.V`, `x=U*V`, `Y=keyY atom k`, and `V(D)=M*N^2/Y`. Fix a cutoff exponent `c`; define `H=(log x)^c`. `ShiftCut` requires **both** signed shifts to be nonzero and their ordinary divisor counts to be at most H. The original close restriction is `abs(n1-n2)<T`. No gcd condition is added: all r/s, n1/n2 and s/ell exceptions remain on these carriers.

## Actual proof and payment

`Part3OriginalS3ClosePairCount.lean` starts at E's actual `S3DeletedTerm` on `offDiagonalCarrier`, including the original same q,d,m, both alpha labels, lambdaTrim coefficients, primitive-q filter, and paperPsi. From an active summand it proves:

1. q,d,r divide the first **nonzero** shift, and s divides the second **nonzero** shift.
2. q,d belong to the actual native primitive source. The gamma support and first congruence derive that m is a unit modulo ell=qd; cancellation gives `n2=n1 mod ell`.
3. The actual lower bound `ell>=Y/2` and the exact real-interval progression count bound the close n2 fibre by `4*T/Y+1`.
4. A concrete sigma-type encoding, with an explicit decoder, preserves every original label. The q,d fibre costs H^2; the r,s fibre costs H^2; both lambda coefficients together cost H^2. The original (m,n1) carrier has at most 12*x elements.

Thus the actual norm is at most `12*x*(4*T/Y+1)*H^6`. This is a proved count, not a premise. Exact-product shifts are never fed into a divisor estimate. The ordinary divisor cutoff also bounds both actual lambda coefficients, so no independent assumed coefficient envelope is needed.

`Part3OriginalS3ClosePairPayment.lean` chooses `T=N/(log x)^(A+6*c)` after the fixed cutoff. The finite bound becomes

```
48*V(D)/(log x)^A + 12*x*(log x)^(6*c).
```

H/G's actual occupied-key geometry gives `x^(1+sigma/2)<=V(D)`. A fixed logarithm-versus-power theorem pays the endpoint term, giving `60*V(D)/(log x)^A` at one threshold preceding every atom and key. No x^epsilon divisor bound is placed on the logarithmic main term.

For the original outside sum, request local precision `D=A+betaMomentOrder(B)+12` once. The same actual `outerL2<=6*Y*betaL2`, original beta-square ordinary divisor mean, and both key multiplicities used by H give

```
actualOuterCloseBudget <=
  720 * betaLogConstant^betaMomentOrder(B) * (2*keyLogConstant)^12
      * x^2/(log x)^A.
```

The separation exponent at this consumer is exactly `D+6*c`. B and c are fixed before constants and thresholds; the varying signed residue, atom, receiver and key are quantified afterwards. The original `0<sigma<1/100`, `MediumAdmissible B sigma kappa c0 atom`, `c0>0`, original trim and nonnegative numeric receiver are unchanged. Kappa need not be restricted in this local proof; the full original caller still has its original cap.

## Source reconstruction and unchanged consumer

`Part3OriginalS3ClosePairResidual.lean` defines `largeShiftDeleted`, `largeShiftFull` and `farFull` directly by filtering the original off-diagonal summands. It proves, rather than assumes,

```
restoredOffDiagonal = largeShiftFull + farFull + closeDeleted
primitiveS3 = largeShiftFull + farFull + closeDeleted + restorationCorrection
largeShiftFull = largeShiftDeleted + actualFirstZero + actualSecondZero.
```

The last identity prevents the full cutoff complement from being mislabeled as a pure large-value source: it contains exactly those two original zero additions. There is no double-zero diagonal restoration.

An exact bridge to the existing `retainedSourceKey` identifies the far physical sum after subtracting the original full off-diagonal zero and omitted modes and adding the original retained diagonal. This is an explicit expression in independently defined sources. It is **not** asserted to be the clean retained E2 Fourier kernel. The still-required close/gcd zero-mode restoration and Fourier disintegration are visible in that expression.

The final theorem `exists_actualResidualFunctional_close_paid` consumes H's original all-key restoration theorem and the new all-key close count, takes the maximum of their thresholds, and bounds the **existing** `actualResidualFunctional`. It does not redefine that functional. Its unpaid ledger displays the far physical centred expression, the full cutoff complement, offDiagonalOmitted, diagonalRetained, roughReplacementCorrection, genuineDiagonalZero, and all four original S2 packet norms with factor 2 and the unchanged outside weights. The two paid constants can be chosen with total factor 756 in the common beta/key normalization. No bound on the unpaid ledger is a hypothesis or conclusion.

## Remaining internal obligations and limitations

- The first large-coefficient/nonzero-shift cutoff estimate and reinstatement remain open. The inspected elementary shifted moment source has an extra fixed-kappa/moment issue and is not silently substituted for full translated Shiu (10).
- The three original rough/gcd exclusions, full rough zero-mode replacement, and close/gcd zero-mode reinstatement remain open. They remain inside the independently filtered physical sources or explicit old correction terms.
- Identification and estimation of the far retained clean/nonclean phase source, omitted-mode outer payment, retained Fourier diagonal, genuine zero diagonal, S2 rough/nonzero terms, and the spectral return remain open.
- This does not supply general-B linear entrance, full medium assembly, K/PP, or the restricted-medium theorem. The new close estimate needs no auxiliary SW and introduces no new external mathematical input.

There is no new suspected mathematical contradiction in the manuscript. There are genuine source implementation gaps: the logarithmic shift cutoff estimate and the far/zero/Fourier source transformation just listed. These are internal obligations, not renamed external inputs.

An inherited source-body issue was observed, without running any compiler: `Part3MediumLiteralS3DeletedCarrier.lean` at the cohort04 raw SHA `f82624c17dfa0dbc2fe7d7b485c86a3ad071bef57ba4535436c44fa8ad2bfe0e` and the equal current ExactProduct-Sol6 draft places the second hmod branch of `fullIndicator_eq_deleted_add_zero` after `deletedIndicator_norm_le_one`, where hzero/hmod are out of that theorem's scope. Root was notified; no older source was edited. This is distinct from a mathematical manuscript gap and precludes any claim of import/kernel closure here.

The previously corrected H metadata issue is not repeated: `.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Saving-Sol6/Part3OriginalS2PaperBlockEmbedding.lean` is locally present and rehashed in this registry. All direct new/project imports have inspected source locations, but source-only modules still require installation at their recorded `ImbalancedChen/*.lean` targets. The source and full transitive import closure remain uncompiled and user-owned. Mathlib and Lean are pinned by the current manifest/toolchain; no local Mathlib checkout or kernel acceptance is claimed.
