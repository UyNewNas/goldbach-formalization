import ImbalancedChen.P2OriginalSaving19Cell01Row000PrefixFloorChecks
import ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix
import ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge

/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact row000 transport through the existing HigherMomentsPrefix
representation theorem and original Q96 namespace bridge. This new owner
requires its own acceptance and imports both generic suppliers unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge

set_option maxRecDepth 1000000
set_option Elab.async false

open scoped BigOperators
open P2OriginalSaving19Cell01Row000
open P2OriginalSaving19Cell01Row000MomentFloor
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19HigherMomentsPrefix

noncomputable def originalMoments (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19HigherMoments.rationalMoment
    (fun i => gapQ (vertices i))
    (fun i => 1 - factorsQ (vertices i) j / topsOf row j) k

theorem prefixMoment_eq_original (j : Fin 10) (k : Nat) (hk : k ≤ 6) :
    prefixMoment j k = originalMoments j k := by
  exact normalizedMoment_eq_encoded gapNats (deviationNats j)
    (deviationDenominators j) gapScale k (deviationDenominators_ne j) gapScale_ne hk
    (fun i => gapQ (vertices i))
    (fun i => 1 - factorsQ (vertices i) j / topsOf row j)
    gap_encoding (deviation_encoding j)

theorem original_gap_eq (j : Fin 10) :
    gapEvaluator (originalMoments j) = gapEvaluator (prefixMoment j) := by
  unfold gapEvaluator
  apply Finset.sum_congr rfl
  intro k hk
  rw [← prefixMoment_eq_original j (k + 2)
    (by have h := Finset.mem_range.mp hk; omega),
    ← prefixMoment_eq_original j 1 (by decide)]

theorem original_first_moment (j : Fin 10) :
    originalMoments j 1 = 1 - meansOf row j / topsOf row j := by
  rw [← prefixMoment_eq_original j 1 (by decide)]
  exact all_first_moments j

theorem original_saved_Q80 (j : Fin 10) :
    momentRow.factorFloorsQ80[j.val]! =
      P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 (originalMoments j) := by
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.factorFloorQ80_eq]
  unfold factorFloorQ80
  rw [original_gap_eq]
  exact all_saved_Q80 j

theorem original_Q80_bounds (j : Fin 10) :
    ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) ≤
        P2OriginalLogMomentQ96CheckerSourceOnly.gapEvaluator (originalMoments j) * (2 : ℚ)^80 ∧
      P2OriginalLogMomentQ96CheckerSourceOnly.gapEvaluator (originalMoments j) * (2 : ℚ)^80 <
        ((momentRow.factorFloorsQ80[j.val]! : ℤ) : ℚ) + 1 := by
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.gapEvaluator_eq, original_gap_eq]
  exact all_Q80_bounds j

theorem original_total_eq :
    totalLowerQ80 originalMoments = totalLowerQ80 prefixMoment := by
  unfold totalLowerQ80 factorLowerQ80 roundDownQ
  apply Finset.sum_congr rfl
  intro j hj
  rw [original_gap_eq]

theorem original_saved_new_Q96 :
    momentRow.newFloorQ96 =
      max (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massOf row) (meansOf row))
        (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
          (massOf row) (meansOf row) originalMoments) := by
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.oldFloorQ96_eq,
    ← P2OriginalLogMomentQ96ArithmeticBridge.newFloorQ96_eq]
  change momentRow.newFloorQ96 = max (oldFloorQ96 (massOf row) (meansOf row))
    (fixedNumerator 96 (oldEvaluator (massOf row) (meansOf row) *
      cubicQ (totalLowerQ80 originalMoments)))
  rw [original_total_eq]
  exact saved_new_Q96_max

/-- The exact five original clauses, specialized to the already decoded
row0 values. The remaining 143 rows and all other cells are separate obligations. -/
theorem original_floor_formula :
    (∀ j : Fin 10, originalMoments j 1 = 1 - meansOf row j / topsOf row j) ∧
    (∀ j : Fin 10, momentRow.factorFloorsQ80[j.val]! =
      P2OriginalLogMomentQ96CheckerSourceOnly.factorFloorQ80 (originalMoments j)) ∧
    momentRow.oldFloorQ96 = row.jensenFloorQ96 ∧
    momentRow.oldFloorQ96 =
      P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massOf row) (meansOf row) ∧
    momentRow.newFloorQ96 =
      max (P2OriginalLogMomentQ96CheckerSourceOnly.oldFloorQ96 (massOf row) (meansOf row))
        (P2OriginalLogMomentQ96CheckerSourceOnly.newFloorQ96
          (massOf row) (meansOf row) originalMoments) := by
  refine ⟨original_first_moment, original_saved_Q80, moment_old_matches_geometry, ?_,
    original_saved_new_Q96⟩
  rw [← P2OriginalLogMomentQ96ArithmeticBridge.oldFloorQ96_eq]
  exact moment_old_eq_evaluator

#print axioms prefixMoment_eq_original
#print axioms original_gap_eq
#print axioms original_first_moment
#print axioms original_saved_Q80
#print axioms original_Q80_bounds
#print axioms original_total_eq
#print axioms original_saved_new_Q96
#print axioms original_floor_formula

end ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge
