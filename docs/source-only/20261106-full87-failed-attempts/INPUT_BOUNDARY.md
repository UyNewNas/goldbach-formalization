# P1.4 exact external-input boundary — physical failure source

Manuscript pin `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, verified blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; §4, esp. original signed first-exit equation and literal residual densities (lines 355–490).

Lean toolchain: `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.
Fixed `c=49044063/25000000`, `K=8452171/1250000`.

## Finite manuscript-internal inputs: directly checked
- `ImbalancedChen/FirstExitTree.lean`: exact `firstExitCorrection`, `firstExitRetainedLeaves` and signed coefficient; the new failure list is proved to equal this exact source correction.
- `ImbalancedChen/FirstExitValidSelection.lean`: actual retained chronology predicate, derived by traversal, not assumed in an event structure.
- `ImbalancedChen/OrdinaryRosserFirstExitPolicy.lean`: parity-upper policy and even-rank admission; used to prove all failed attempts in this physical upper continuation occur on odd selections.
- `P4AOriginalFull87ActualEighthCarrier.lean`: owned 87-domain states, exact historical eighth prefix, ordered true target-deleted remaining source, two frozen levels.
- `P4AOriginalFull87RankNineInheritedSplit.lean`: inherited, product and new-square rejection remain distinct; new enumeration does not pay any one of these modes.
- `P4AOriginalFull87FailedAttempts.lean`: five SOURCE_ONLY candidate proofs, never compiled or replayed.

## Classic external analytic input registry: all UNVERIFIED and NOT INVOKED
1. Literal ordinary Rosser density of manuscript eq:current-raw-density:
   `V_N^+(R,y)/V_N(y)=F(log R/log y)+o(1)` for `s>1`, and
   `V_N^-(R,y)/V_N(y)=f(s)+o(1)` for `s>=2`. Source: pinned manuscript §4 / Appendix upper; independent published reference edition, uniform compact-domain hypotheses, normalization and target-prime deletion still need validation. Intended only after the same-physical-event residual integral identification. **NOT IMPLEMENTED**.
2. PNT/Mertens manuscript eq:current-mertens:
   `V_N(N^u)=2 exp(-gamma) C_N/(u log N)(1+o(1))`,
   fixed `u>0`, even `N->infty`; uniformity, exact source edition, and singular-series conventions still unverified. Used only in later density scaling, **NOT IMPLEMENTED**.
3. Prime-progression discrepancy manuscript eq:current-PP:
   claimed same physical `rho_N` family `O_{A,W}(N/(log N)^A)`; provenance, family range, parameter order and applicability unverified. Intended later distribution payment, **NOT IMPLEMENTED**.

All remaining same-source source-to-integral matching, finite arithmetic error and reserve payments are INTERNAL manuscript obligations; no manuscript-internal work has been reclassified as external. No new assumed result, theorem-shaped structure field, alternative coefficient or axiom is introduced.