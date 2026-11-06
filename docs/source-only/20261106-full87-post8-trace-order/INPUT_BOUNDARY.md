# P1.4 — boundary of post-eight odd-trace carrier proof

**Manuscript:** UyNewNas/chen-imbalanced-semiprimes,
commit 9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/manuscript-body.tex,
Git blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79,
§4 lines 350–485. No manuscript switch.

**Fixed toolchain (not changed):**
Lean leanprover/lean4:v4.33.0-rc1;
mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1;
native subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958.
c=49044063/25000000, K=8452171/1250000.

## Finite inputs actually used

- Literal `FirstExitValidSelection` from project
  `ImbalancedChen/FirstExitValidSelection.lean`, with selected lists
  in descending scan order and reverse-stored history.
- Literal `post8OddTrace` and actual original87 owned `states` and
  `actualFrozenPost8Level` from preceding source-only packet
  `P4AOriginalFull87Post8GuardExtraction.lean`.
- Prior `owned87_post8_later_odd_reject_last_square` candidate, now
  corrected at its q-suffix parity contradiction, still uncompiled.

The new work derives parity and `Nodup` for real trace membership
from stated carrier ordering and boundary premises. Extracting those
premises from the true original87 producer remains IN SCOPE and OPEN.
Prospective first-rejected branch attachment and rank-nine handling
are also internal and OPEN. No new proof-result-bearing interface
fields were added.

## External analytic inputs (registered, UNVERIFIED, NOT invoked)

1. **Ordinary Rosser exit-series density.** Manuscript §4 and
   Appendix upper, raw normalization
   `V_N^+(R,y)/V_N(y)=F(log R/log y)+o(1)` for s>1;
   `V_N^-(R,y)/V_N(y)=f(s)+o(1)` for s>=2.
   Exact publication/edition of ordinary Rosser supplier, uniformity
   in the relevant fixed positive compact parameters, target-prime
   deletion applicability and source hypotheses: UNVERIFIED.
   Intended invocation: after the actual original87 terminal
   same-source exit-series/log-coordinates adapter, not in this packet.
2. **PNT/Mertens** manuscript eq:current-mertens:
   `V_N(N^u)=2 exp(-gamma) C_N/(u log N) * (1+o(1))`
   for fixed u>0, uniformly over sufficiently large even N.
   Precise source version, presieve range and normalization still
   require independent verification. NOT implemented, NOT invoked.
3. **Prime progression/discrepancy estimate**
   manuscript eq:current-PP, the licensed signed family
   `rho_N` with claimed `O_{A,W}(N/(log N)^A)`.
   Precise family, chart/parameter restrictions, norm, source edition,
   required quantifiers and proof/reference: UNVERIFIED.
   Intended primitive ledger site, NOT implemented or invoked here.

## Internal (cannot be delegated to external theorem)

Actual carrier geometry, sortedness, cross-boundary, occurrence
multiplicity and first rejection; signed full-modulus beta,
target-prime correction; same-source exit integral and compact
uniformity; primitive/modulus/centre smallness; sixth filtering and
all raw/finite/filtered signed losses; saved87 numerical source
binding; compiler and density reserves separately paid; same-rho
assembly; effective Lean/kernel/axiom and independent verification.

**Status:** all new proof terms SOURCE_ONLY / UNEVALUATED, no formal
credit and no reserve paid.
