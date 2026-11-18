# P1.4 — upper-endpoint orientation correction, original receiver witness

## Verified chain and error being corrected
Verified source base: branch chatgpt/p1-full87-upper-rho0-six-receiver-20261118-1610 at GitHub HEAD ba94e8bb4802cd13901328c0991533fee57f08cb. Read REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and the complete 278-line original candidate P4AOriginalFull87UpperRho0SixReceiver.lean. Also read RoughPrimeUniverse.lean, ChenInitialPrimeSource.lean and frozen manuscript at 9731290e8f53cffda44129906cde6a965eaa869b, manuscript-body.tex blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. No applicable root/docs/source-only AGENTS.md found. No other branch modified.

The prior literal-w theorem is a mathematically conditional result: IF w=N^(19/96), THEN every six-factor full modulus exceeds N and its receiver vanishes. However the ORIGINAL rough universe is

  roughPrimeUniverse N cap w z = [p prime : p ∤ N, w ≤ p < z].

Frozen manuscript section "Upper construction" assigns rho0=19/96 to the UPPER sieve endpoint N^rho0 (the roughness level in its majorant); it separately mentions a presieve below which primes have already been handled. The implementation has TWO arguments w,z, with w the lower boundary and z the upper boundary. There is no producer proof that its lower w equals N^rho0. Identifying upper z with lower w is an endpoint-direction error. The preceding literal-w theorem remains valid *only* at that literal w, but it is not evidence that the actual production upper sixth event is zero. No physical invoice, density saving or H_N coefficient can be discharged by that inference.

## New concrete mathematical witness in genuine source objects
Candidate source P4AOriginalFull87UpperEndpointDirectionAudit.lean: initial source commit 72e9af94aad9f1cacd5c42d3ba8216021e6d8ca2; 107 source lines. It does not assert a fabricated fifth-exclusive event.

Take even N=2^24=16,777,216, cap=100, lower w=3. All six distinct primes 3,5,7,11,13,17 belong to the ORIGINAL roughPrimeUniverse N cap 3 z for every z≥26. They are coprime to N and their product is d=255255<N. More strongly the literal target-deleted prime receiver is positive at d: the integer P=N-d=16,521,961 is prime and does not divide N, hence x=N-P=d lies in the ORIGINAL chenPrimeReceiverSource N; receiverTest N d≥1.

The frozen upper numerical endpoint is z=N^(19/96) = 2^(19/4), and 26^4=456976 < 2^19=524288, so z>26. This elementary endpoint calculation is independently checked but is NOT a Lean theorem of the packet; the Lean membership result is stated precisely for all z≥26. This is a counterexample to *inferring* vanishing from the UPPER z alone; it is NOT a counterexample to the conditional literal-w theorem or a proof that the actual fifth-event+PLUS-Rosser+strict X filters admit this word. The original event generator's lower w and all remaining gates must still be traced.

## Candidate Lean theorem scope
- six_word_mem_original_rough_universe: all 6 primes genuinely in the implementation's [w,z) universe at w=3, z=26;
- six_word_mem_of_upper_at_least_26: preserves membership for arbitrary z≥26, with fixed lower w;
- six_word_product_below_target: exactly d=255255<N;
- six_word_actual_receiver_positive: actual receiver at d is positive, using genuine chenAdditivePrimeCarrier and chenPrimeReceiverSource;
- actual_upper_endpoint_not_a_six_lower_cutoff: bundles the unchanged universe membership, sub-N full modulus, and actual receiver witness. Does not claim stopped event producer membership.

Independent arithmetic diagnostics: exhaustive trial division for P through floor(sqrt(P))=4064 found zero divisors, d was directly multiplied, the receiver shift verified, and 26^4 < 2^19 checked exactly. This is NOT Lean elaboration or a kernel proof.

## Verification
Current worker: lean --version, lake --version, elan --version each exit 127 (not found); no pinned Lean/mathlib/native checkout or source-only import staging. Source candidate is UNEVALUATED/UNCOMPILED; proof terms, including large-prime norm_num, may fail elaboration or resources. No kernel replay, axiom audit, independent review, saved87 replay or CI. SOURCE_ONLY remains the only valid credit. No new axiom, sorry/admit, native_decide or unsafe escape; static text scan alone does not establish soundness.

## Actual remaining P1.4 obligations
1. Source-level actual UPPER producer w and z arguments: establish separate values, e.g. z=N^rho0 only where really passed, and DO NOT substitute into w. If the original producer uses a small presieve w, the preceding all-six-receiver-zero conclusion does not transfer.
2. Return to quantitative same-source stopped receiver/primitive discrepancy for N^theta<full q≤N; keep actual full a*b, strict X and occurrence multiplicities, all compiler/physical invoices and two independent reserves.
3. Ordinary residual integral, actualParent/saved87 original numerical archive, unfiltered sixth BOTH, RAW eighth, rank9/changed/tagged, same rho fixed theta and outside invoices still open.
4. Typecheck staged source-only imports under Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native 09b97db5764ade1246bfb77206baa1b124760958; correct any Lean errors without modifying pins. c=49044063/25000000, K=8452171/1250000 unchanged. No new CI, Codex, user workstation, memory changes or main/master updates.

P1.4 stays YELLOW; this packet corrects scope and prevents an unsound upper-to-lower cutoff promotion.