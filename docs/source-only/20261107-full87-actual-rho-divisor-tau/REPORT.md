# P1.4 — actual signed full-rho coefficient bound on the two true prime-exception fibres

## Recovered state, manuscript and toolchain

Verified parent `443f9b3467cafc6d6184c5f1fd08a3cecf506f2d` on `chatgpt/p1-full87-exception-divisor-fibres-20261107`. Read its full REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and 248-line source; read the original eighth prime-mean ledger, the sixth physical signed ledger, the signed source helper, the initial prime source, ActualSmallRoughAttachment and its coefficient theorem. No applicable AGENTS.md at root, docs, source-only or packet-level paths on inspected ref. Independently fetched pinned manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, especially lines 720–805.

Lean leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958. c=49044063/25000000, K=8452171/1250000 unchanged.

## Genuine manuscript-internal advance

The preceding packet gave exact *same-rho* full-modulus centre and modulus-prime divisor-fibre invoices, but did not justify an absolute bound on the physical signed coefficients. The actual fixed source `ImbalancedChen/ActualSmallRoughAttachment.lean` already proves `actualSmallRoughRho_abs_le_one` for EVERY original retained policy, N, cap, w,z,L and modulus (including off-support). This packet finally instantiates that actual, previously unconnected theorem on both sixth and eighth original policies.

For nonprime N, `centre_factor_gap_pos` gives N-p>0 for each centre prime p|N, so each true centre fibre d|(N-p) lies in the finite divisor set of the **same positive N-p**. By the literal one-bound, for each original policy P,
`centreDivisorInvoice P N cap w z L ≤ Σ_{p∈centrePrimeFactors N} τ(N-p)`.
In particular the two actual original policies together cost at most twice that same positive-divisor sum. The N nonprime premise is essential; for prime N, p=N is a genuine zero-gap term and τ(0) does NOT provide this bound. The intended even N>2 satisfies nonprimeness but its explicit algebraic instantiation remains a caller obligation.

For the *different* p|d modulus-prime fibre, applying the same proved coefficient bound yields `modulusDivisorInvoice P ≤ unitModulusDivisorInvoice P`, where the new upper invoice is exactly `Σ_{p≤N prime} Σ_{d∈actual moduli, p|d} 1/φ(d)`. No change to full physical moduli, prime prefix, support, original sign attachment or occurrence aggregation. A separate candidate lemma uses `actualSmallRoughModuli_coprime_target` to show each supported full d excludes any prime divisor p|N, so the two prime populations are arithmetically disjoint; no geometric measure argument.

Combining these genuine bounds with the previous receiver-density inequality gives an original-source explicit upper bound:
`|Gain(receiver)-π(N)Gain(density)| ≤ absoluteGainBudget(primitiveError) + unitModulusInvoice(sixth) + unitModulusInvoice(eighth) + 2 Σ_{p|N prime} τ(N-p)`.
This is a finite, centre-aware coefficient reduction, **not** an estimate relative to H_N or an external signed PP result. It replaces a missing coefficient-size premise with a verified existing internal theorem; it does not assume |rho|≤1 for arbitrary beta.

## Concrete source and checks

`P4AOriginalFull87ActualRhoDivisorTau.lean`: 136 lines, Git blob `4dd2a130993b5afd502388d417767fb2a752100a`. It has candidate proof bodies for the true centre divisor count, two-policy bound, actual unit-modulus invoice, target-coprime exclusion, and combined receiver-density comparison. Explicit import of `ActualSmallRoughAttachment` resolves the boundedness supplier. There is no new axiom, sorry/admit, native_decide or unsafe escape.

2,000 independent synthetic small-N signed rational coefficient tests, using actual prime prefixes and gcd(d,N)=1 full-modulus-shaped supports with |rho|≤1. Of these 1,617 had composite/nonprime centre; all centre τ bounds, p|N versus supported d exclusion, and modulus unit-fibre upper bounds held (0 mismatches). These do NOT instantiate the real saved87 archive or evaluate Lean proof terms. Static forbidden-token scan passed. Actual Git blob SHA was returned by GitHub.

## Verification and honest boundary

SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT. No Lean/Lake or source-only dependency staging, kernel replay, transitive axiom audit, external verification, independent review, new CI dispatch, Codex, toolchain upgrade or extra resources. Neither compiler nor density reserve paid. Existing external lemmas remain REGISTER_ONLY_UNVERIFIED_NOT_INVOKED.

Remaining: show quantitative *same-rho* H_N comparison of centre τ and modulus unit invoices (the crude tau sum alone is NOT o(H_N)), adapt exact signed primitive PP to literal original full beta and centre/copime normalization, ordinary continuation residual integral, sixth filtering, saved87 original weighted gain and rank9 history/cubic fees, changed/tagged and two separate reserves. P1.4 remains YELLOW.
