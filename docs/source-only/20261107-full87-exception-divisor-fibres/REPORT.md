# P1.4 — exact divisor-fibre arithmetic of the two original prime exceptions

## Recovery and pin
Verified predecessor: `25aff27f4b2b332435ab459f71e70e7f613d0604` on `chatgpt/p1-full87-terminal-prime-exception-20261107`; verified handoff, report, input boundary, registered source `P4AOriginalFull87TerminalPrimeExceptionBudget.lean`, the original `P4AOriginalFull87EighthPrimeMeanLedger.lean` and `ChenInitialPrimeSource.lean`. No AGENTS.md exists at repository root, docs or docs/source-only on the fetched baseline. Manuscript pin `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Frozen Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native 09b97db5764ade1246bfb77206baa1b124760958, c=49044063/25000000, K=8452171/1250000.

## Material manuscript-internal new candidate
Original sixth and eighth source policies, actualSmallRoughModuli (FULL d), original sign-attached actualSmallRoughRho, inclusive chenPrimePrefix and actual centre are unchanged. For every N,d, the original centre prime count admits the **exact** fibre formula

`chenCentrePrimeAPCount N N d = Σ_{p≤N prime, p|N} 1_{d|(N-p)}`.

Likewise the actual modulus-prime correction is exactly

`modulusPrimeTerm N d = Σ_{p≤N prime} 1_{p|d}/phi(d)`.

Both formulas include the totalized d=0 boundary. In the original physical absolute coefficient sum, finite Fubini/reindexing produces the exact two genuine divisor-fibre invoices

`C_P = Σ_{p≤N prime, p|N} Σ_{d∈M_P, d|(N-p)} |rho_P(d)|`

`D_P = Σ_{p≤N prime} Σ_{d∈M_P, p|d} |rho_P(d)|/phi(d)`.

The original receiver-to-density discrepancy is therefore bounded by the same primitive AP discrepancy budget plus `C_6+C_8+D_6+D_8`, with exactly the original sixth and eighth rho families and no unrelated coefficients. This is more informative than charging `omega(N)*B_P(1)`: it identifies the true shifted-centre divisor fibres used by the endpoint argument in the pinned manuscript at its sharp-original-prime discussion. This is NOT a proof that the invoices are small.

When N is nonprime, each actual p dividing N has 0<N-p, hence the centre term at physical modulus d=0 vanishes. This is applicable to even N>2 after the ordinary elementary fact that such N is nonprime. The source proves the nonprime implication, not an unrelated geometric zero claim.

## Scope and checks
File `P4AOriginalFull87ExceptionDivisorFibres.lean`, 248 lines, Git blob `d02ab0f30ad93034f503b94e71a7caebb3e3b731`. All finite incidence and Fubini steps have candidate proof terms; SOURCE_ONLY / UNEVALUATED / UNCOMPILED, **no kernel credit**. The previous finite moment bounds remain valid, with the explicit new exact reindexing as an alternative invoice; no double charging of any reserve.

Independent synthetic exact rational checker: 3,500 generated N and distinct full-modulus support/rho families, including 875 cases explicitly inserting d=0, 722 prime centres and 2,695 nonzero centre invoice cases. It checks centre and modulus physical absolute invoices against their two double divisor sums, and the nonprime zero-modulus case, all with zero mismatches. These are test models, NOT a replay of actual saved87 archives or a proof of the Lean terms.

No Lean/Lake, kernel replay, transitive axiom audit, independent reviewer, CI dispatch, Codex, toolchain upgrade or resource expansion performed. Banned tactic/keyword static scan passed. No external input called and neither compiler nor density reserve paid.

## Precise remaining proof obligations
1. Prove useful **quantitative** same-rho bounds on the original two divisor-fibre invoices relative to H_N. For the centre this requires an actual full-beta coefficient bound on each d|(N-p), not silently assuming |rho|≤1; for the modulus correction it requires the true factorized coefficient estimate, not arbitrary-modulus absolute PP. Handle both original sixth/eighth polices and actual occurrence weights.
2. Instantiate signed primitive discrepancy on exactly the same original full rho and residue N, checking the pinned restricted-medium and sharp-prime hypotheses including endpoint, centre and coprime normalization; registered external input is not implemented.
3. Verify original saved87 weighted population for historical wide-gap rank9 and cubic annulus, ordinary integral semantics, sixth filtering, raw/finite/filtered gain, changed/tagged and TWO distinct reserve payments at one rho.
4. Stage the full source-only dependency tree for fixed-toolchain Lean kernel acceptance. No candidate here is automatically importable at ImbalancedChen without that staging.

P1.4 remains YELLOW; no claim of manuscript-internal closure or H_N control.
