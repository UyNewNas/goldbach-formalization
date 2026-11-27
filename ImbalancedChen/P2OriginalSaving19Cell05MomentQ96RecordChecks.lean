import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Complete

/-! Exact original Cell05 Q96 records from the unchanged frozen evaluator.
The 560 Q80 identities are reused; no prefix value is recomputed as a premise.
These are finite arithmetic results, without an integral or ownership claim. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05MomentQ96RecordChecks
noncomputable section
open scoped BigOperators
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19Cell05MomentQ80Pilot
open P2OriginalSaving19Cell05MomentBounds
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19RowNumericsPure

def storedTotal (r : Fin 56) : ℚ :=
  ((∑ j : Fin 10, (originalMomentRow r).factorFloorsQ80[j.val]! : ℤ) : ℚ) / (2 : ℚ)^80

theorem totalLower_eq_stored (r : Fin 56) :
    totalLowerQ80 (prefixMoment r) = storedTotal r := by
  unfold storedTotal
  rw [Int.cast_sum, Finset.sum_div]
  unfold totalLowerQ80
  apply Finset.sum_congr rfl
  intro j _
  change (computedFactor r j : ℚ) / (2 : ℚ)^80 = _
  rw [P2OriginalSaving19Cell05MomentQ80Complete.all_factors r j]

def storedEvaluator (r : Fin 56) : ℚ :=
  oldEvaluator (massOf (boundedRow05 r)) (meansOf (boundedRow05 r)) * cubicQ (storedTotal r)

theorem newEvaluator_eq_stored (r : Fin 56) :
    newEvaluator (massOf (boundedRow05 r)) (meansOf (boundedRow05 r)) (prefixMoment r) =
      storedEvaluator r := by
  unfold newEvaluator storedEvaluator
  rw [totalLower_eq_stored]

theorem all_saved_new_floors : ∀ r : Fin 56,
    fixedNumerator 96 (storedEvaluator r) = (originalMomentRow r).newFloorQ96 := by
  decide +kernel

theorem all_new_floors (r : Fin 56) :
    newFloorQ96 (massOf (boundedRow05 r)) (meansOf (boundedRow05 r)) (prefixMoment r) =
      (originalMomentRow r).newFloorQ96 := by
  unfold newFloorQ96
  rw [newEvaluator_eq_stored]
  exact all_saved_new_floors r

theorem all_old_floor_alignment : ∀ r : Fin 56,
    oldFloorQ96 (massOf (boundedRow05 r)) (meansOf (boundedRow05 r)) =
        (originalMomentRow r).oldFloorQ96 ∧
      (originalMomentRow r).oldFloorQ96 = (boundedRow05 r).jensenFloorQ96 := by
  decide +kernel

theorem all_stored_factor_nonneg : ∀ r : Fin 56, ∀ j : Fin 10,
    0 ≤ (originalMomentRow r).factorFloorsQ80[j.val]! := by
  decide +kernel

theorem all_stored_improvements : ∀ r : Fin 56,
    (originalMomentRow r).oldFloorQ96 ≤ (originalMomentRow r).newFloorQ96 := by
  decide +kernel

theorem stored_lower_eq_computed (r : Fin 56) :
    ((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 =
      simplexLowerQ96 (massOf (boundedRow05 r)) (meansOf (boundedRow05 r)) (prefixMoment r) := by
  change _ = (newFloorQ96 (massOf (boundedRow05 r))
    (meansOf (boundedRow05 r)) (prefixMoment r) : ℚ) / (2 : ℚ)^96
  rw [all_new_floors]

#print axioms all_new_floors
#print axioms all_old_floor_alignment
#print axioms stored_lower_eq_computed

end
end ImbalancedChen.P2OriginalSaving19Cell05MomentQ96RecordChecks
