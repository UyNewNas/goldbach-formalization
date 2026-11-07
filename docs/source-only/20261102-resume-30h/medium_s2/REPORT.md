# H medium_s2: the original S2 single-zero payment

Status: local source step complete; broad medium_s2 task incomplete. All new and reused draft interfaces remain uncompiled here. `compiled=false`, `kernel_verified=false`, `formal_credit=0`. Author model/effort selected in TASKS.json: `gpt-6-astra`, `xhigh`. No compiler, build, CI, certificate/decision replay, subagent, quota check, production edit, older-batch edit or commit was performed.

## Original source and the missing obligation

The authoritative current branch is `codex/proof-continuation-20261015`, HEAD `25afcbff11562df51ef7ac5113c879123fcd64c6`. Current production `ImbalancedChen/Part3DistributionTargets.lean` has SHA256 `a0b43f877bb7bcdf7606e19281521a0165538c08c0495a2a3e2d58b66aeb08cc`. Its lines 126–145 define `MediumAdmissible`; the actual complete target remains `RestrictedMediumObligation`.

The manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, proposition at lines 125–168. The relevant original proof is `paper/source/modules/distribution-medium-completion-20261010.txt`, SHA256 `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`:

- Lines 115–122 keep all d in one dyadic block, with Y=Q1*D and Rcal the rough length.
- Lines 161–169 delete the exact product before Cauchy, remove the other rough gate, and then restore the S2 single equality at cost Rcal*N*x^o(1).
- Lines 183–189 describe the distinct two S3 off-diagonal single zeros. Their source is not the S2 coprime-mean source.
- Lines 207–210 compare the S2 zero mode with MT; lines 251–257 explain the outer-Cauchy scale and single-zero absorption.

I read F's independent medium review (`reviews/medium.md`, current SHA256 `5ca97d81a85272d878e53ad541e29acb33bae84b941c1465f7ed3a1e5c4fef13`) and the actual G S2 files. G's `actualFirstZero` and `actualSecondZero` are the S3 off-diagonal correction sources, and G supplies their subpower budgets. F's unchanged actual S2 ledger instead contains `singleZeroCorrection` from E `Part3OriginalS2PrimitiveLiteralDictionary.lean:117`. Its second leg is the original coprime mean with denominator phi(q*d*s). The G S3 estimates cannot simply be renamed to pay that term.

## Implemented proof and exact consumer

`Part3OriginalS2SingleZeroCounting.lean` works on the independently defined E `pairedCarrier`, `restoredTerm`, and `singleZeroCorrection`. It filters only exact first products and nonzero summands, proves the unchanged sum equals that active sum, and injects its labels through G's actual `firstCode`. The code carrier contains original q,d,r; a true factor pair m*n1=|a|; and the free n2,s leg. G's `firstProductPairs_card_le_divisors` pays the factor-pair cardinality. No second-congruence restriction is fabricated.

The elementary lemma `reciprocal_totient_le_divisor_ratio` proves 1/phi(l) <= tau(l)/l from `Nat.sum_totient` and divisibility of totients. On the native smooth-q support q>=Q1/2, d>=D and s>=Rcal, the actual denominator l=q*d*s is at least Y*Rcal/2. Two actual Lambda norms and this totient ratio cost H^3 per term, divided by Y*Rcal. The exact-product count is at most 12*Y*Rcal^2*N*H. Thus `actual_S2_singleZero_integer_budget` proves the actual source norm is at most 24*Rcal*N*H^4. Every integer envelope in this intermediate theorem is discharged in the next file.

`Part3OriginalS2SingleZeroPayment.lean` uses G's `exists_uniform_polynomial_tau` at epsilon/4. Both actual Lambda coefficients are bounded through E's exact `keyKept = lambdaTrim` dictionary, the original physical support, and the already proved actual Lambda divisor bound. For the actual mean modulus, nonzero right Lambda produces a genuine original rough fibre. F's `nativePhysicalCap_le_original_range` gives q*d*s <= x^(4/5) once x>=10^10. The moving residue uses the unchanged |a|<=x^(1+kappa), and c0>0 proves a!=0 before divisor counting. This yields `exists_actual_S2_singleZero_subpower` with constant 24*C0^4 and no assumed source estimate.

The new scale step is

    (Rcal*N)*x^(3/10) <= 4*fixedDScale(d,2^k.d).

It uses G's actual occupied-key `D*Rcal<=4*Q2*Q3` and F's consequence of the original medium inequalities `Q1*Q2*Q3<x^(7/10)`. The native scale remains exactly `fixedDScale = V*U^2/(Q1*D)`. Selecting epsilon=1/10 leaves x^(1/5) to pay any requested logarithm by the current production `TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow`. This is a genuine power-to-log implication, rather than an arbitrary-log hypothesis or a free-key size assumption.

`exists_actual_S2_singleZero_arbitrary_log kappa A` chooses C and X before B, sigma, c0, atom, key and receiver. It requires only the original admissibility, sigma>=0, c0>0, z>=0, the actual occupied-key membership, and x>=X. It concludes the actual correction is at most C*fixedDScale*log(x)^(-A). A may be any real here. The original theorem's stricter positive sigma and constrained kappa therefore suffice unchanged.

The final theorem `exists_original_S2_centered_except_rough_and_nonzero` consumes F's exact `actual_primitive_S2_centered_identity` and its already implemented zero-Gram payment. Its left side is exactly

    |primitiveS2 - nativeMT.re - actualS2NonzeroModes.re
      + otherRoughCorrection.re|.

This equals the real zero-Gram error minus the real single-zero correction. The two actual errors are paid with one maximum threshold and Cg+Cz. The key hypothesis is the original E `originalNumericKeys`, explicitly unfolded to the same `keyBank` and `roughY`; this is already an occupied-key bank. The actual full signed nonzero series and other-rough correction keep their original signs and identities.

## Eliminated versus remaining

Eliminated at source level in this delivery:

1. The missing quantitative original S2 coprime-mean single-zero source bound, including actual coefficient norms and the native reciprocal totient.
2. All local divisor-envelope, positive-integer, native physical-modulus and exact-product count premises used in that bound.
3. Its original fixedDScale and arbitrary-log absorption, uniform before the moving original data.
4. The single-zero term in the actual primitive S2-MT consumer, combined with F's independent zero-Gram payment at one threshold.

Still internal and open at the broad task level:

- Quantitative `otherRoughCorrection` on this actual S2 source, including the requisite shifted-progression/tail estimates and complete reinstatement bookkeeping.
- The full `actualS2NonzeroModes` to retained E1 dictionary, omitted-frequency payment, and genuine spectral return.
- Any remaining rough/mixed restoration terms beyond E/F's already implemented three smooth-tail and zero-Gram payments.
- Final all-key outerL2/key-cardinality aggregation with the complete S1/S2/S3 residual and signed entrance/discard terms. This delivery does not assert the full restricted-medium estimate.
- S3's two distinct single-zero log/restoration payment is a separate H medium_s3 consumer of G's existing source theorem; no H peer module or final aggregate is assumed or imported here.

No new classical external input is postulated. The divisor-subpower and log-versus-power suppliers are existing implemented declarations, with their existing package/source prerequisites retained. The complete prior import closure and all new proof bodies still require user-owned compilation/kernel verification. No mathematical obstruction was found in the narrow step; the listed original analytic obligations have not been proved by it.

## Installation and exact bytes

Install only after the user's normal integration/review process, as `ImbalancedChen/Part3OriginalS2SingleZeroCounting.lean` and `ImbalancedChen/Part3OriginalS2SingleZeroPayment.lean`. Current proposed source hashes:

- Counting: `82c1ea891edd72af9922d805ecd28d2b8b5a7edf747383f922520291c8866af4`.
- Payment: `c68b48689018b6ebb15895ff169e84a78e28b92a1e8b5292bcefbec73eebeb88`.

REGISTRY records exact selected local predecessor paths and SHA256 values. No mirror was silently substituted. The workspace currently has no `.lake/packages` directory; Mathlib package revision is the current manifest pin `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, not a claimed resolved import tree. Two read-only mathlib backup files were consulted for lemma signatures; they are explicitly recorded as reference-only, not selected import replacements. There is no inherited compiled credit.
