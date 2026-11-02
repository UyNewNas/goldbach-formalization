# P11 — frozen-Q / finite-tau root H430 mass increment

Status: **partial source increment; broad `P5.6.eight_suppliers` and the full frozen-Q task remain OPEN**. All Lean is source-only, uncompiled, not kernel verified, and earns zero formal credit. No Lean/lake invocation, CI dispatch, finite guard evaluation, numerical table replay, Git operation, or old-file modification was performed.

## Exact new result

`Part5OriginalH430FrozenTableRootMass.lean` imports the existing O root mass implementation, without copying its residual, alpha, density, or clamp stability proofs. The new obligation discharged at source level is the **non-clamp H430-weighted U3/U4 root mass**, including changes of table atoms under the actual `frozenLevel` and the actual positive `finiteTau n = min (1/12) (1/(n+1))`.

For `q₀(t) = (sourceRoot k 0 t).physical.argument`, `qₙ(t) = (frozenRoot n k (finiteTau n) t).physical.argument`, and the literal root weights `w₀,wₙ`, define

`Dₙ(k) = ∫_[rootBand k] |H430(q₀(t)) - H430(qₙ(t))| dt`,

`Eₙ(k) = ∫_[rootBand k] |H430(q₀(t)) w₀(t) - H430(qₙ(t)) wₙ(t)| dt`.

The new source proves `Dₙ(k) → 0`, and proves the absolute bound

`0 ≤ Eₙ(k) ≤ floorBound(H430Numerators) * rootAbsoluteError n k (finiteTau n) + weightEnvelope * Dₙ(k)`.

Together with the reused O theorem `actual_root_absolute_error_tendsto`, this proves `Eₙ(k) → 0`. The difference of the two individual, integrable root table masses is bounded by `Eₙ(k)`. The last theorem chooses a **single** natural precision and its positive finite tau for both original root bands before introducing any arithmetic `N`.

The key missing geometric deduction is proved from the original formulas: for an arbitrary scalar `c`, if the ideal root query equals `c` and is not the clamp value 2, then its physical coordinate is one of

`1 - 2*a*c`, `(57/64 - a*c)*2/5`, `1/2 - a*c`.

The first two points are the actual affine branches of `v(t)-t`; the third is the actual U3 half-level tail. Thus only proper knot fibres are removed as a finite null set. The whole max-two stratum is retained exactly under lowering, and the finite lookup remains its literal `upperAtomSet` sum. In particular the existing minimum of entries 49 and 50 at 2 is untouched. No monotonicity, continuity, or replayed numerical facts about the H430 array are assumed.

## New declarations

All names below are in `ImbalancedChen.Part5OriginalH430FrozenTableRootMass`.

| Declaration | Source line | Actual role |
| --- | ---: | --- |
| `proper_root_fibre` | 44 | Computes the three-point proper root fibre from original formulas. |
| `ae_root_clamp_or_off_knots` | 87 | Removes proper knot fibres only; explicitly retains clamp. |
| `ideal_clamp_preserved` | 107 | Common two-root adapter using O tau loss and M clamp preservation. |
| `frozenQuery_tendsto` | 116 | Instantiates the existing root argument error on the explicit finite-tau sequence. |
| `eventually_upperFloor_eq` | 141 | Exact closed finite-atom lookup becomes identical away from the 201 knots. |
| `ae_frozen_H430_tendsto` | 168 | Applies the preceding facts to the original two roots. |
| `tableDiscrepancy_tendsto` | 184 | Dominated convergence of the concrete root table discrepancy. |
| `idealTableWeight_integrable`, `frozenTableWeight_integrable` | 222, 229 | Individual physical root table masses are integrable. |
| `rootTableAbsoluteError_bound` | 248 | Explicit absolute error decomposition; no normalization by a cell mass. |
| `rootTableAbsoluteError_tendsto` | 299 | Concrete root table-weighted L1 error vanishes. |
| `actual_root_table_mass_difference` | 309 | Bounds the difference of the two actual integrals. |
| `exists_common_root_table_precision` | 324 | One precision/tau for U3 and U4 before arithmetic N. |

The helper scalar convergence theorem has the usual sequence-convergence and off-knot hypotheses. These are **derived** at every original root use; they are not target mass hypotheses. Every exported original-root conclusion has only the stated parameter/range/positive-reserve hypotheses.

## Reuse and provenance

SHA256 values and intended module mapping are recorded in `REGISTRY.json`. The following existing results were read and reused rather than rewritten:

* O `h430_frozen_q/Part5OriginalH430FrozenPerturbation.lean`: `sourceResidual_tau_loss`, `root_argument_error`; also its same-coordinate `actual_descendant_residual_loss`, `actual_descendant_alpha_error`, `actual_descendant_reciprocal_error` are explicitly retained as the descendant baseline.
* O `h430_frozen_q/Part5OriginalH430PhysicalMassPerturbation.lean`: `frozenRootWeight`, `rootAbsoluteError`, root-band volume bounds; `descendant_physicalWeight_error` and the singleton/pair/Buchstab physical Jacobians remain the existing pointwise baseline.
* O `h430_frozen_q/Part5OriginalH430FrozenRootMass.lean`: root weight measurability/integrability, `weightEnvelope`, `weight_bound`, `finiteTau`, `levelError_finiteTau_tendsto`, `actual_root_absolute_error_tendsto`. Its `actual_clamp_table_error_tendsto` is not duplicated as a separate new proof.
* O smooth peer `Part5OriginalH430CellMeasurability.lean`: `measurable_frozenLevel`, transitively used by O root measurability.
* M `Part5OriginalH430FrozenRootRefinement.lean`: literal cumulative frozen level, residual bounds, clamp preservation, and same-Q descendant identity.
* M `Part5OriginalH430PhysicalRoots.lean`: literal U3/U4 roots, original bands and residuals, positive floors.
* Production `Part5UpperTableLookup.lean`: literal upper atoms, `H430`, `measurable_H430`, `norm_H430_le`, `integrableOn_upperRoot_mul`.
* Production `Part5OriginalU34H430Integrable.lean`: actual main/tail residual formulas and their original root coefficient context.

The O directory had three Lean files and no per-task report/registry at inspection time. Its batch `README.md` and P `BRIEF.md` were read. M `Part5OriginalH430AbsoluteQueries.lean` and `Part5OriginalH430GeometricWalls.lean` were also checked: their finite primitive atom/simple-function and punctured-wall integrals do **not** already prove this changed root-query result.

## What remains open

1. **Descendant moving domains.** The existing O descendant density estimate is at the same physical appended word under `Member` of the frozen graph. It does not compare the indicator of ideal `Member` against frozen `Member`, nor integrate their symmetric difference. Production `P2EnhancedLowerPhysicalTransition.LocalDomain` lines 61–85 contains moving `normalized`, `buchstabArgument`, ceiling and query gates. A complete result must handle their actual recursively composed physical pullbacks, including exact equality/inherit strata, and their native-coordinate measures. No such estimate is assumed here.
2. **Descendant closed-table crossings.** The new three-point root fibre calculation does not apply to descendant query pullbacks. M's `QueryIndex = Fin 441 × Primitive × FloorAtom` counts primitive/generation labels; it is not by itself the actual itinerary admission theorem. The O peer's `QueryOccurrence` records actual paths, but that alone supplies no mass convergence. One must combine inherited queries, genuine proper wall nullity and exact identity states with the native-coordinate physical density.
3. **Full U3/U4 coefficient.** The new integral is the literal H430 correction mass. It is not the entire `(upperAmplitude-H430) * branchWeight` expression. The continuous upper-amplitude term still needs its own frozen-query limit/compact bound if the full branch coefficient is requested. The O unweighted root mass plus this new H430 mass do not silently assert that additional step.
4. **Actual arithmetic realization and root history.** O smooth peer `Part5OriginalH430RootGateObstruction` proves `source_U3_tail_not_fullGates` and `tail_no_full_square_realization` for the existing external-mark-in-slots encoding. This is a positive-length tail, not a proper wall. The source itself explicitly classifies this as an interface obstruction, not a disproof of the manuscript's marked-count estimate. It requires the correct external-selected-root/full-history dictionary; lowering Q cannot cure it.
5. **441-generation common choice and final reserve.** The new existence statement is simultaneous for two roots only. It does not claim a common precision for all actual descendant admissions, ordinary/switched costs, or the full reserve propagated by `(12^441-1)/11`. Those remain OPEN until real suppliers are composed.
6. **Independent two-parameter limit.** The proved convergence uses the explicit admissible joint choice `tau = finiteTau n`. It establishes finite positive-tau realizability at arbitrary accuracy; it does not claim an already formalized product-filter limit for independently varying tau and precision.

## Manuscript check and classification

Pinned manuscript SHA256: `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Lines 808–892 were read, together with original completion-note lines 239–289.

* **808–817:** same total Q, residual update, and true alpha not reset to 2. The O same-coordinate algebra is reused unchanged. This P file does not replace alpha or the original physical word.
* **839–860:** actual pair domains, gates, unit surfaces, conservative envelope, closed support minima. No gate, unit surface, or minimum is relaxed by the new root-only calculation.
* **867–877:** the common approximation and positive leaf cutoff paragraph. The missing non-clamp root-table limit is a **fillable omitted deduction (class 2)**: finite piecewise-affine fibres, exact clamp, finite table, positive density bound, and dominated convergence are sufficient. It is now made explicit at source level.
* **887–892:** root H430 lookup at `max(2,L/a)` and its positive-measure clamp. The new proof preserves precisely this state. Discarding all knot preimages would have been mathematically wrong; only the proper fibres are null.
* **Expression/API difficulty (class 1):** finite-atom membership transport, a.e. restriction and Bochner dominated convergence require Lean elaboration. The source has been statically inspected but cannot be certified without the expressly prohibited compiler.
* **Possible substantive gap (class 3):** no counterexample to the original root analytic estimate was found. The unresolved actual descendant-admission/source-history composition is mathematically substantive; the manuscript paragraph asserts it but current supplied source does not yet discharge it. The explicit O U3-tail gate failure is evidence that a naive use of the current full-square root encoding cannot be the missing proof. It must not be dismissed as Lean expression difficulty or “finite depth”.

## Static checks and install status

Only static file reads, source searches, SHA256 checks and source-token scans were run. The new file has no `sorry`, `admit`, `axiom`, `native_decide`, `run_tac`, `eval`, or `unsafe` token. This scan does not establish elaboration or kernel correctness. The pinned manuscript and earlier M hashes match the task metadata.

The file imports the intended installed module `ImbalancedChen.Part5OriginalH430FrozenRootMass`. That O module and its M/O source-only dependency closure are **not installed by this task**. `REGISTRY.json` gives the exact source mapping; compilation requires a separate permitted fixture/install step. No production file or preceding batch was changed.
