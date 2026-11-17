# P5.6 → h34: physical Theta transport along actual selected history (2026-11-17)

Repository: `UyNewNas/goldbach-formalization`.
Dedicated working branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified incoming HEAD: `1ffbfaf29daf6828771020460cc879134caaffbc`.
Math source commit: `e2824ce169bac1fc301fd48e5ec44d7ca35570a0` (Git blob `a57ca822c6f4a498bc721dcc32b799d43c6feabc`).
Module: `Part5OriginalH430WeightedPhysicalTelescope.lean` (119 lines, two definitions and four theorems).
Pinned source map: `docs/CURRENT_MANUSCRIPT_MAP.md`, manuscript `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766` (2026-10-10 source); NOT the 2026-11-06 release.
Pinned Lean `v4.33.0-rc1`; pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**.

## Mathematical change beyond the incoming bank-surplus packet

The incoming `BankSurplusPhysicalSplit` separated the genuine selected-bank positive gap into ideal overshoot, applied row error and the remaining child-Theta drift. Earlier unweighted request-wave proofs also showed a parent-Theta correction and a child-Theta correction at every request node; paying them independently through the complete history loses a telescoping cancellation.

This packet uses the exact *existing* physical edgeValue rather than an abstract row or a changed action selector. Define
`weightedRequest N Q g r = thetaAtom N Q (parentProduct r.old) * iteratedRequest g r`.
Since each actual chosen edge contributes exactly `edgeWeight e * weightedRequest N Q g (nextRequest r e)`, its one-step local defect is exactly the already-defined `physicalDefectAt`. By applying the existing whole-history weighted telescope with the ORIGINAL `children` and `history` lists, the packet writes the **candidate** identity

```text
theta(root) * F_g(root)
  = waveAccount(weighted generation-zero seed)
  + waveAccount(original same-Q physical source defect).
```

The second new relation compares this result to the older *unweighted* physical wave and identifies the full parent-plus-child Theta correction with a root-minus-terminal boundary:

```text
wave(parentThetaAt) + wave(childThetaAt)
  = (1 - theta(root)) * F_g(root)
    + wave(weightedSeed) - wave(unweighted terminalSeed).
```

The final theorem instantiates the genuine fixed frozen root, its original root-specific Q, and **all 430 request generations**; no caller supplies an artificial root, stage index or owner.

**Important non-implications.** This is an exact all-history signed transport, not a bound on the separate *positive* absolute bank child-Theta gap of the preceding packet. The seed and the physical source defects are not known to be negligible, and this does not identify a generated request value with the original U3/U4 selected-count source. No P1.4 or P3.6 file, frozen c/K, root norm 7/2, row norm 12, real alpha, fixed 106 actions, Q80 decision, or 430+11 budget changed.

## Source declarations

- `weightedRequest`: exact original physical Theta-scaled request, same Q.
- `weightedSeed`: genuine generation-zero terminal charge.
- `weighted_local_defect_eq_physical`: actual weighted local defect equals pre-existing physicalDefectAt.
- `weighted_request_root_exact`: all-history seed-plus-physical-source exact telescope.
- `parent_child_theta_wave_boundary_exact`: cross-generation cancellation and nonzero boundary.
- `frozen_root_430_weighted_physical_source`: exact original 430-generation frozen-root specialization.

## Execution and verification

The GitHub repository reports push permission for the authenticated owner. The dedicated branch was verified at the incoming HEAD, and a branch-scoped query found no Actions runs. Only this new h34 source-only directory is touched. The exact source was fetched back by blob SHA after commit; that confirms only repository bytes, not proof elaboration.

The runtime environment had no `lean`, `lake` or `elan` executable on PATH; its native Git could not resolve github.com and the fixed source-only import closure was not available as compiled modules. Thus **no** Lean/Lake compilation, kernel replay, transitive-axiom audit or finite 430 certificate replay was performed. Simple source scans found no prohibited proof placeholders or custom axioms. Every candidate remains **UNEVALUATED**. No green node is added.

## Genuine remaining manuscript obligations

1. Prove a quantitative physical-defect source bound at the genuine same-Q root plus the exact weighted generation-zero seed bound, without outsourcing the manuscript's own PP/same-rho compatibility.
2. Pay actual selected Buchstab Q80 suffix versus strict-prime positive gaps, bank positive ideal overshoot and, when absolute per-position charges are required, child-Theta drift. Do not substitute the new signed telescope for those one-sided bounds.
3. Prove base/fixed/switched/seed/floor and all-action CLOSED-CELL induction at actual scalar and cell requests, plus complete original U3/U4 full/selected/inherited ownership, root 7/2, multiple q/tag and four rejection lanes.
4. Complete signed Euler, native-history, outer integral–Theta–count and one jointly nested 430+11 causal refinement; compile and kernel-audit all imported source-only dependencies.

**Complete h34 manuscript-internal proof remains OPEN.**
