# P5.6 → h34 — original U3/U4 presieve/root incompatibility boundary

Status: **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

- Repository: `UyNewNas/goldbach-formalization`
- Branch: `chatgpt/p5-h34-request-admission-20261105`
- Verified preceding HEAD: `483d78d1fc50ca7eaabef4b6c1e162dc6b67c39d`
- New source commit: `53e3f430a8fdd373c08e5599681409e2cefcfa82`
- Source blob: `f4f927abc73b61964c8c0b84b2d3dbfb8ab73710`
- New file: `Part5OriginalH430OriginalRootCutoffObstruction.lean` (139 lines, 10 theorem candidate bodies).
- Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- No production source, P1.4/P3.6, existing packets, CI, dependency or toolchain changes. No CI dispatch.

## What was actually written

The original U3 and U4 selected-prime bands (not the arithmetic quotient q) both begin at the **inclusive** lower cutoff `(N : ℝ)^a`. The new source extracts this literal selector condition and traces it through `rawTagged N`, keeping U3/U4 tags and individual (p,q) occurrences.

It then writes a necessary root-admission condition:

```
z ∈ rawTagged N ∧ (arithmeticPrime z : ℝ) < z0
    → (N : ℝ)^a < z0.
```

Consequently, **conditionally on** `z0 ≤ (N : ℝ)^a`, *every* original raw selected root fails the physical strict initial-history cutoff. For any actual subfamily `S ⊆ rawTagged N`, `gateBlocked S N z0 Q lower = S`. In particular the two genuine `frozenOnly` and `rejectedFrozen` rejected sources each remain entirely in root-gate exceptions, with their exact cardinalities. The new candidate `raw_root_not_initial_carrier` also excludes such a root from the literal initial `roughPrimeUniverse N cap 0 z0` under the established `z0 ≤ cap` physical hypothesis.

**Critical mathematical interpretation:** This does NOT prove that the manuscript uses `z0 ≤ N^a`. The pinned manuscript writes the presieve as `z_0=N^ω` and fixes `a=417/5000` in the Chen weight. Before any all-receiver root-event payment, the precise presieve exponent used by the historical consumer must be checked against this bound. If `ω≤a` for `N>1`, directly choosing a U3/U4 root p as the first prime of that small-presieve historical universe cannot work; a genuinely different stage/owner bridge is then required. This is a conditional no-go certificate, NOT completion of full/selected/inherited history mapping or a signed count bound.

## Declarations

`original_band_lower_power`, `raw_root_lower_power`, `raw_strict_root_requires_large_presieve`, `raw_root_no_strict_cutoff`, `raw_root_not_licensed`, `all_raw_gate_blocked`, `frozen_all_gate_blocked`, `rejected_frozen_all_gate_blocked`, `rejected_original_count_all_blocked`, `raw_root_not_initial_carrier`.

No custom axiom, admitted hypothesis equivalent to h34, unsafe shortcut or new external distribution input. The core bound comes from the actual original selector. No c/K, root norm 7/2, row norm 12, true alpha, same-Q, original q counts or 430+11 budget changes.

## Verification boundary

New source blob and source commit have been read back from GitHub; the single-file source diff and remote branch HEAD were checked. Text-only declaration count and restricted standalone placeholder-token scan were performed. **NOT RUN:** Lean parser or elaboration, Lake compilation, kernel replay, transitive axiom audit, independent review, numerical430 and any other finite certificate. The latter remain UNEVALUATED. No green node and zero formal proof credit.

## Remaining manuscript-internal obligations

1. Check the exact fixed-manuscript `z0` used by each *actual* initial/rank-one history consumer and the exponent/threshold relation with the original U3/U4 band start. If `z0≤N^a`, do not demand impossible `p<z0` for an original selected root; identify the actual later-stage historical owner or pay the blocked source.
2. For other cutoff regimes, prove or pay all actual root cutoff, cap, singleton Rosser and subsequent full/selected/inherited retention gates; produce an exact original receiver → genuine history owner bridge and noninjective (p,q,tag) occurrence-fibre payment with signs and original root weights.
3. Pay still-outside-carrier and policy-pass/fail receiver terms, derive complete original selected-count inequalities, and connect existing request-level Buchstab/retention row results to the all-action CLOSED-CELL arithmetic induction.
4. Complete base/fixed/switched/seed/floor, feedback integral weights, same-rho/PP instances, native history, outer integral–Theta–count and a single nested 430+11 causal refinement.
5. Compile, kernel replay, audit transitive axioms, and evaluate inherited finite certifications. No further proof should be claimed before those steps.

**The complete h34 manuscript-internal proof remains OPEN.**
