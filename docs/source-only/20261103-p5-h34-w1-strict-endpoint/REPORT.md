# P5.6 / h34 — original W1 half-open window to strict fresh row

Date: 2026-11-03.
Base: `20125ddf3144d3f60f0b88c221ddf5003a97d3f5`.
Repository: `UyNewNas/goldbach-formalization`.
Intended branch: `chatgpt/p5-h34-w1-strict-endpoint-20261103`.

**PARTIAL_SOURCE_INCREMENT. Full h34 and the original selected-count/441
realization remain OPEN.** Three new Lean modules contain 740 lines,
34 theorem declarations and 18 definitions/abbreviations.

`compiled=false`, `kernel_verified=false`, `formal_credit=0`;
all Lean proof bodies and inherited finite guards are UNEVALUATED.
Neither Lean nor Lake is available on PATH. No compiler, kernel replay,
transitive axiom audit, independent reviewer, connected computer, Codex job,
child agent, or CI dispatch was used. The commit requests `[skip ci]`.
Only this new directory is written. Production, preceding packets,
P1.4 and P3.6 are unchanged. No merge into the default branch is requested.

## Exact gap addressed

The preceding selected-bank packet deliberately distinguished:

* R16/S18 W1 arithmetic rows over the original `childWindow`: d*N mask,
  included lower endpoint and excluded upper endpoint;
* production `singleChildren (.w1 i j)`: the same fresh mask, but an open
  W1 interval, plus physical ceiling, product support and Fin(N+1) bounds.

P's `P2OriginalLiteralW1OldProfile` already paid the N-mask to d*N-mask
change when establishing its old-profile limit. That correction is NOT
charged again here. The remaining W1 difference is the actual lower-endpoint
prime, which cannot be discarded by Lebesgue nullity.

The new proof sources establish the exact finite dictionary and pay that
endpoint before applying the existing coefficientwise bank estimates to
production strict children. W2's restored N-window repeats are untouched.

This session re-read the pinned carrier/profile/payment code. It does not
claim an independent new manuscript audit or an original-source count licence.

## 1. Part5OriginalH430W1WindowDictionary

`mem_halfWindow` preserves the exact original d*N mask and both endpoints.
`window_product_lt` derives d*q < Q from the actual upper W1 endpoint;
`window_prime_cap` then derives q <= N from Q <= N and d >= 1.
The finite representation does not receive an unproved truncation cap.

`mem_strictWindow_iff_child` supplies BOTH directions between the strict
natural window and production singleChildren. Its geometric premise is
L/W1Target(i) <= ceiling, already supplied for selected parents by 20125dd.
It derives the strict physical ceiling and product filters, rather than
pretending these filters were absent from the original constructor.

`window_sum_split` is valid for EVERY signed test:

    half-open W1 window sum = strict production child sum + endpoint sum.

The fibre is defined by relativePrime = 1/W1Anchor(j).
`endpoint_card_le_one` derives at most one prime using logarithmic
injectivity. It does not assert an empty fibre.
`window_primeFloor_le` derives q >= N^(L/6) from the stronger original
W1 lower endpoint; this permits reuse of the earlier common floor threshold.

`childQuery_is_physical` connects the original inherited scalar query to
perform(parent, w1Singleton, actual prime coordinates). No new query or
ceiling is chosen after observing a later prime.

## 2. Part5OriginalH430W1StrictRows

`strictChildAtom` is an actual sum over production singleChildren, not a
renamed ideal integral. `arithmeticRow_split` keeps the upper fixed point
unchanged and splits the lower coefficient as

    original child / 2 = strict child / 2 + endpoint child / 2.

The factor one-half is used exactly once. All closed table knots remain.
`strictRow_value` recovers the full applied profile with the unchanged
upper point and the actual strict prime-child sum against the old h table.

`window_theta_nonneg` uses actual product support. `window_theta_le` reuses
the original thetaAtom_single singular-factor identity and the proved
localPrimeFactor bound. On the real W1 interval relativePrime <= 1/2,
so for 4 <= A <= N^(L/6):

    endpointMass <= (4/A) * thetaAtom(parent).

The endpoint coefficientwise error, including its original one-half,
is consequently bounded by

    atomMagnitude(oldh) * (2/A) * thetaAtom(parent).

This is absolute error at each atom BEFORE applying a signed array or
combining different histories. No positive-total-mass premise and no division
by Theta is used. W1 repeats are not deleted a second time.

`lowerMagnitudeEnvelope` is a symbolic finite bound for all literal
precedingh(g), g<430. It is not a new row norm, an executed 430 replay,
a supplied array bound, or a change to the main-term/reserve ledger.
`uniform_rowGap` fixes A and one natural threshold before N, Q, old words,
ceilings, both W1 parameters and g. Its residual-floor premise is discharged
by the selected-family module below.

## 3. Part5OriginalH430SelectedStrictW1Supply

`uniform_selected_strictW1` applies the two error estimates with epsilon/2
each. The old selected bank theorem pays original-row versus ideal-row;
the new endpoint theorem pays original-row versus strict-row.

The actual selected slot provides the target/ceiling test. Existing frozen
Member support provides parentWindow, residual identity, the positive fixed
floor and the same cell Q. These are not new caller-provided analytic licences.
The arithmetic generation map g and nonnegative marks sigma remain explicit
until the entire original selected-count history is constructed.

For every selected W1 family, the new source conclusion is

    strict coefficientwise error <= epsilon * selectedTheta,
    every strict row coefficient >= 0,
    sum_atom strict row <= 12 * selectedTheta,
    selectedTheta = 0 -> strict error = 0 and every strict coefficient = 0.

Deleting a nonnegative endpoint cannot increase the row mass. Therefore
there is NO 12+epsilon mass budget and no modification of the 441 propagation
constant. `strict_profile_error_le` derives applied signed-profile error
from absolute coefficient error. `uniform_selected_strictW1_applied` exports
that applied bound for the actual strict rows.

`uniform_selected_outer_strictW1` aggregates after selected W1-slot and
root-cell selection. Every root cell retains its own Q, and alternatives
are not added in place of the original maximum.

## Remaining h34 obligations

1. The complete original U3/U4 selected-count histories, their generation
   assignments, positive marks, full/selected/inherited filters and owner
   multiplicities must still be identified with the relevant Member family.
   This transfer does not supply those assignments or count semantics.
2. The W2 half-open endpoints and restored N-window repeat/selected lanes
   still need their dictionary and payment against strict fresh children.
   W1's completed local endpoint transfer is NOT a proof for W2 pairs.
3. Original W1/W2 point indices, per-product rounded weights, candidate-to-
   profile/base comparisons, ordinary/fixed/switched bases, the analytic
   positive seed, count licences and same-rho PP input remain separate.
4. Full native-history proper/equality/inherit mass control, native outer
   integral/Theta/count correspondence and ONE nested causal refinement
   through 430+11 levels remain open in the original reserve order.
5. The full pinned held dependency closure must be staged and compiled;
   kernel replay and transitive axiom inspection remain outstanding.

No mathematical counterexample to the manuscript is asserted. No h34,
hLower, count/error licence or target-equivalent structure field is added.
Original c, K, root norm7/2, row norm12 and depth440/441 are unchanged.

## Checks and staging

Static checks cover forbidden proof-bypass tokens, comment/string/delimiter
balance, trailing whitespace, declaration/import inventories and raw-byte
hashes. These checks are NOT a Lean parser, elaborator or proof verifier.

One small synthetic exact-integer test has N=100000007, d=3, Q=1875,
residual base625, W1 target12/5 and anchor4. The masked half-open primes are
[5,7,11,13], the strict primes are [7,11,13], and the endpoint is [5].
The test uses p^3<5^5 for the upper cutoff and exact gcd tests, not floating
point decisions. It also verifies Q<=N and d*625^2<=N (the alpha>=2 condition).
It illustrates that an endpoint can survive the mask, even on that alpha
range. It is not an original-root realization or Lean/kernel evidence.

Stage the prior held closure unchanged, then these modules in order:
W1WindowDictionary, W1StrictRows, SelectedStrictW1Supply, each with the
Part5OriginalH430 prefix under ImbalancedChen. Use the existing Lean and
Mathlib/native pins. Copying these three files alone is not a complete build.
Exact dependency identifiers and source hashes are in REGISTRY.json.

## Narrow state delta

    黄｜P5.6 → h34
        蓝｜W1原dN半开窗口到生产strict fresh子载体的精确分解、自然素数重索引与端点质量付款
        蓝｜selected W1严格行的同Q逐系数绝对供应、原12Theta行质量、零质量与外层聚合
        黄｜完整原始selected-count历史/代数/正标记及全部继承过滤条件绑定
        黄｜W2端点/repeat/selected异常衔接与统一付款
        黄｜bank数值candidate/基项/seed/count/同rho PP许可及430+11共同细化

Blue is narrow source coverage only. Append the actual publication commit
identifier to the two new blue entries; no green credit is asserted.
