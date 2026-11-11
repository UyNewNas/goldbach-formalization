# P5.6 / h34 — external input boundary for tagged-q physical-debt lift

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, original mapping `paper/source/manuscript-body.tex`.
Mathematical source commit: `899394ac64af40139f578f05a8f3e22807ae364c`.
Source: `Part5OriginalH430OriginalQFibrePhysicalDebt.lean`.

**New external analytic theorems / axioms: NONE.**

The packet reuses the frozen existing mathematical imports without constructing or altering proofs of PNT, Mertens, Bombieri–Vinogradov, Rosser or prime distribution estimates.

The exact existing *manuscript-local* definitions and candidate results reused are:

- `Part5OriginalH430TaggedArithmeticReceivers.originalTagged`, `originalPairs`, `originalBand`, `originalReceiver`, `TaggedReceiver` and `TaggedPair` for the original (tag,p,q) count source, through `Part5OriginalH430OriginalPrimeBandPhysicalGap`. These source counts are not external estimates.
- `Part5OriginalH430OriginalUpperOverlapCount.upperExclusiveBand` and `original_u3_band_partition` for the exact original U4 overlap; no different p endpoint or tag policy.
- `Part5OriginalH430OriginalPrimeBandPhysicalGap.actualRootPhysicalClosedCellGap` and `actual_root_physical_closedcell_gap_abs_le` at the same original root, p, and chosen `Fin 430` depth.
- `Part5OriginalH430PhysicalJointSourceDebt.actualPhysicalJointSourceResidualMass` and `actual_physical_joint_source_residual_nonneg`; the source residual and selected row error are still uncompiled candidates.

The only general library finite-algebra facts invoked directly are `Finset.sum_disjSum`, `Finset.sum_sigma`, `Finset.sum_const`, `Finset.sum_union`, `Finset.sum_add_distrib`, `Finset.abs_sum_le_sum_abs`, `Finset.sum_le_sum`, `mul_nonneg`, `mul_le_mul_of_nonneg_left`, `Nat.cast_nonneg`, `abs_mul`, and elementary commutative real algebra. These do not outsource any claimed h34 count bound.

The following remain **MANUSCRIPT INTERNAL**, and are not transferred to this list: q/tag original selected-count owner, actual history-position injection/capacity, proper/equality/inherited filters, the original root-weight 7/2 and row norm 12 transport, the real base/switched/seed/floor consumer, six rejection lanes and signed Euler suffix, PP/same-rho instantiation, native-history mass, Theta/count/integral correspondence and the 430+11 joint causal closure.

No finite430 calculation, kernel replay or transitive axiom closure was evaluated. There are no newly introduced sorry/admit/axiom/unsafe proof escapes.
