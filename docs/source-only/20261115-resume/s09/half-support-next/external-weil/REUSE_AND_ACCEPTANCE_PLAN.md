# Minimal source reuse and acceptance plan

The selected source provider is LeanPool/lean-pool at `5dd712603d49049c7a5198e5dd725f768c5a510b`, entry `LeanPool.KloostermanWeil.Weil.PrimeKloosterman`. Reuse its exact 34-module import closure under `upstream/LeanPool/`, listed in `UPSTREAM_INDEX.json`; each file retains its Apache-2.0 author/license header. The upstream repository's root LICENSE must accompany any distribution. Do not import `LeanPool` or its all-modules index. No TauCeti theorem, pool linter plugin, project-wide source index, or proof rewrite is needed for this theorem closure.

The new sources install only at the corresponding `ImbalancedChen/<filename>` paths in a separate root-controlled candidate package:

| Order | Source | Exact role |
|---|---|---|
| 1 | Part3FixedMarkPrimeWeilBridge.lean | Actual physical sum equals the imported prime sum; pays zero second coefficient; exports the literal sqrt prime estimate. |
| 2 | Part3FixedMarkHalfEulerMajorant.lean | T25 factorization/CRT proof reused; good-prime local exponent 1/2 and prime price -3/2+delta. |
| 3 | Part3FixedMarkHalfEulerSummability.lean | T25 smooth-number/Euler proof reused with delta<1/2. |
| 4 | Part3OriginalHalfMarkTraceGrowth.lean | Existing positive6 geometric proof reused with the new arithmetic price. |
| 5 | Part3OriginalPositiveHalfSupport.lean | Reuses private `others` and `slot_floor` from frozen positive6; substitutes s>1/2 into the same fixed-coordinate limit argument. |
| 6 | Part3OriginalNativeJFromPrimeWeil.lean | Applies the frozen conditionalcritical5 original-range theorem to the new exact provider. |

The first module is a direct theorem import, not an hWeil/hJ input. The later modules do not add an axiom or target-shaped support hypothesis. The upstream proof is not reimplemented. Old source files/namespaces remain unchanged; the new arithmetic namespace is `FixedMarkHalfTail20261115`.

## Version boundary

Upstream: Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0). Config source copies are in `upstream-config/`.

Project: Lean 4.33.0-rc1, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. The local Mathlib checkout was not present at the tested package path, so that local absence is not evidence of missing APIs. Four relevant exact pinned Mathlib source files were fetched and are present: Minpoly.ConjRootClass, Finite.Trace, PowerSeries.Log, and Analysis.Polynomial.CauchyBound. Presence of these files does not establish compatibility of all declarations or the Lean module system.

No toolchain upgrade, source installation into the project, local Lean/Lake/LSP/helper execution, Git mutation or GitHub mutation was performed. Root should keep the current project pins for an isolated candidate acceptance first. Any compatibility edits must be a separately frozen revision with a narrow diff; no fallback to axioms or assumptions. If the pinned project cannot accept the exact external closure without substantial backporting, a separate newer-toolchain validation can diagnose the boundary but cannot validate a silent upgrade of the main project.

## Root-controlled remote acceptance

The reviewable inputs are now concrete: the exact upstream 34-file closure, six adapter files, the frozen positive6/conditionalcritical5 packages, and their existing direct project dependencies. The upstream trust evidence and s05's independent report are a separate prerequisite; this author's source audit does not impersonate that check.

At the project pins, test the external entry first, then the six modules in the order above. The fifth module's `open private others slot_floor from ImbalancedChen.Part3OriginalPositiveMarkOrder` is deliberately source-bound: the dependency must be the exact frozen positive6 module, not a renamed duplicate. The proof's right-factor cancellation follows the pinned meaning of `mul_le_mul_iff_left₀`, already independently checked in the prior positive6 review.

The acceptance report should show the actual type and transitive axioms of at least: imported `prime_bound`; new `physical_eq_prime` and `prime_physical_sqrt`; `summable_majorant_price`; `geometry`; `positive_half_support`; and `original_range`. The final two declarations must have no hidden support, hWeil, hJ or native-gap premise. Check the exact commit/file hashes of the run; successful upstream v4.35 CI alone does not compile the project v4.33rc1 adapters.

Until that remote run and the requested source reviews pass, these artifacts remain source-only/uncompiled. In particular no full-J/global-gap completion flag, no goal-count change, and no old FREEZE replacement is justified.
