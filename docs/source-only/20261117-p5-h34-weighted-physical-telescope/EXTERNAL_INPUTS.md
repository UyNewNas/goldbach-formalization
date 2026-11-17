# P5.6/h34 weighted physical telescope — external/input boundary

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`; same frozen proof mapping and c/K, root norm 7/2, row norm 12.

**New genuinely external analytic inputs: none.** No new theorem concerning PNT, Mertens, BV, a root-count licence, an h34 axiom, or an unverified final target is introduced.

Reused manuscript-local statements and exact call sites in `Part5OriginalH430WeightedPhysicalTelescope.lean`:

- `Part5OriginalH430RequestWaveTelescoping.root_eq_terminal_plus_defects`: for the **actual** `history N Q g r` with original edge-weight products and every repeated occurrence, gives a terminal plus local-defect equality for any explicitly defined request diagnostic. Consumed in `weighted_request_root_exact`, specialized to `weightedRequest`.
- `Part5OriginalH430RequestedBranches.edgeValue`: its actual edge list equals the weighted child list `edgeWeight e * thetaAtom N Q (parentProduct (nextRequest r e).old) * requestValue (iterate g) (nextRequest r e)`. Used definitionally (not as a new axiom) in `weighted_local_defect_eq_physical`.
- `Part5OriginalH430PhysicalRequestDefectBridge.physicalDefectAt`, `physicalStepDefect`, `iteratedRequest`: existing same-Q physical defect. Used in `weighted_local_defect_eq_physical`.
- `Part5OriginalH430PhysicalRequestDefectBridge.root_iterated_request_exact_physical_wave`: exact unweighted seed, parent-Theta, physical and child-Theta wave. Consumed in `parent_child_theta_wave_boundary_exact` jointly with the new weighted telescope.
- `Part5OriginalH430RequestedHistory.rootRequest` and `Part5OriginalH430PhysicalRoots.rootQ`: frozen request root and its fixed physical Q. Consumed in `frozen_root_430_weighted_physical_source`.
- Mathlib real ring arithmetic, finite-list sums and function extensionality: foundational operations only.

**Still manuscript-internal and unproved:** numerical smallness of the physical defects and seed, Buchstab/bank positive payments, original U3/U4 count-source owner and root weights, full/selected/inherited filtering, floor/base/CLOSED-CELL proof, PP/same-rho instances, native history, and joint 430+11 refinement. The all-history signed Theta cancellation CANNOT be converted to a per-occurrence positive-part or absolute-value bound by dropping signs.

All inherited and newly created source-only statements remain **UNCOMPILED / UNEVALUATED** in the pinned toolchain. No transitive axiom audit was run.
