# P1.4 — external input boundary for actual eighth carrier

Manuscript pinned to `UyNewNas/chen-imbalanced-semiprimes`
`9731290e8f53cffda44129906cde6a965eaa869b`,
`paper/source/manuscript-body.tex`, exact Git blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`,
re-read §4 (lines 350–485). No alternative manuscript edition.

Fixed toolchain: Lean `leanprover/lean4:v4.33.0-rc1`;
mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`;
native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.
Constants c=49044063/25000000, K=8452171/1250000.

## Source inputs already implemented in native project
- `FirstExitDepthSplice.lean`: literal rank-eight state producer.
- `FirstExitFrontierInvariants.lean`: joint selected-reverse and
  remaining sublist, strict smaller-prime boundary and exact
  target-deleted capped prime suffix after the last selection.
- `RoughPrimeUniverse.lean`: prime-carrier strict decrease,
  `p<cap`, `p∤N`, `w≤p<z`, and literal half-open endpoint.
- Actual old-sixth parent frontier and owner filtering in the
  pinned `P4AOriginalFull87OwnedEighthSource.lean`.
These are finite internal mathematical inputs, not analytic
distribution hypotheses. Their types were re-read, but this newly
authored source is not yet compiled.

## Registered external analytic inputs — not invoked here
1. **Ordinary Rosser exit-density** (manuscript §4 and Appendix upper):
   upper `V_N^+(R,y)/V_N(y)=F(log R/log y)+o(1)`
   for s>1, lower `V_N^-(R,y)/V_N(y)=f(s)+o(1)`
   for s≥2; uniformity over fixed positive compact parameter
   sets, target-prime deletion and the literal coefficient source
   require edition/source and hypothesis verification.
   Intended use only after genuine same-source first-exit log adapter.
   **Source edition/conditions UNVERIFIED; NOT INVOKED.**
2. **PNT/Mertens** (manuscript eq:current-mertens):
   `V_N(N^u)=2 exp(-gamma) C_N/(u log N) (1+o(1))`
   for fixed u>0 as N→∞ through even targets. Uniformity,
   presieve normalization and bibliographic version UNVERIFIED;
   NOT INVOKED.
3. **Prime progression discrepancy** (manuscript eq:current-PP):
   claimed licensed `rho_N` signed-family
   `O_{A,W}(N/(log N)^A)`; actual family, chart restrictions,
   normalization, parameter order and source edition UNVERIFIED;
   NOT INVOKED.

## Still strictly internal
First rejected pair and rank; historical/successful guard
reconstruction; source-preserving exit integral; separate arithmetic
error budgets; same signed-beta physical source; sixth filtering,
saved87 original geometry and gain; two reserve payments and
same-rho reconciliation. The present packet spends no reserve.
All newly authored proof bodies SOURCE_ONLY / UNEVALUATED.
