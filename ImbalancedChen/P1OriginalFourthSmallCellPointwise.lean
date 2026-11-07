import ImbalancedChen.P1OriginalFourthFiniteBinBudget
import ImbalancedChen.P1OriginalSmallCutoffActualUpperTail
import ImbalancedChen.P1OriginalHistoricalSmallCoordinateGap
import ImbalancedChen.P1OriginalCoarseFourthResidualDictionary

/-!
# Pointwise signed small-last bound on the literal original fourth cell

The source and levels here are `HistoricalThirdCoarse.policy`, its raw Q3
level, and the checked original Q4 cell cap. The same target, cap, cutoff,
and reciprocal-prime tuple occur in both PLUS residuals. Source-only.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open P1OriginalCoarseContinuation
open P1OriginalFourthSmallPrimeStratification
open HistoricalThirdCoarse.P1OriginalUpperResidual

namespace P1OriginalFourthSmallCellPointwise

private theorem coarseDifference_eq_normalized
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (N cap : ℕ) (p : Fin 4 → ℕ) :
    P1OriginalCoarseFourthResidual.coarseTupleResidualDifference
        e chi m omega J4 cap4 N cap p =
      normalizedResidual N cap p (oldLevel (e : ℝ) chi m omega N p) -
        normalizedResidual N cap p (newLevel e chi m omega J4 cap4 N p) := by
  have hhist : P1OriginalCoarseFourthResidual.tupleHistory p = fourthHistory p := by
    simp [P1OriginalCoarseFourthResidual.tupleHistory, fourthHistory, List.ofFn_succ]
  unfold P1OriginalCoarseFourthResidual.coarseTupleResidualDifference
    P1OriginalCoarseFourthResidual.literalTupleResidualDifference
  rw [hhist, thirdAncestor_fourthHistory]
  unfold normalizedResidual oldLevel newLevel
  ring

/-- The original signed upper-tail theorem acts on the literal finite
small cell, including the p_last=3 case where both actual PLUS tails are
identically equal. Its coefficient C is independent of a,N,cap and cell. -/
theorem exists_original_smallCell_pointwise_linear_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ),
        0 < omega → 0 < a → 2 * a ≤ omega →
      ∀ (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ),
        h34Check e chi m omega J4 cap4 = true →
      ∀ (N cap : ℕ), 2 ≤ N → Even N →
      ∀ (j : FourthCell m), j ∈ selectedFourthCells e chi m omega J4 →
      ∀ p ∈ smallCellTuples e chi m omega a N cap j,
      ∀ L : ℝ, 2 ≤ L → L ^ 13 ≤ omega * Real.log (N : ℝ) →
        Real.exp 1 ≤ omega * Real.log (N : ℝ) →
        |fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
            fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p| ≤
          (2 * C / omega ^ 2) * actualPrimeTupleLog N p (Fin.last 3) +
            (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L) := by
  obtain ⟨C, hC, hsource⟩ :=
    P1OriginalSmallCutoffActualTail.exists_original_signed_linear_cutoff_majorant
  refine ⟨C, hC, ?_⟩
  intro e chi m omega a homega ha haomega J4 cap4 hcheck N cap hN hEven j hj p hp L hL hbudget hlog
  have hN1 : 1 < N := by omega
  obtain ⟨had, hsmall, hcell⟩ := Finset.mem_filter.mp hp
  have hprime := (admitted_log_data e chi m omega N cap hN1 p had).2.1
  have hpos : ∀ i, 0 < p i := fun i => (hprime i).pos
  have hpOriginal : p ∈ admittedTuples (e : ℝ) chi m omega (19 / 96 : ℝ) N cap := had
  have hdict := P1OriginalCoarseFourthResidual.coarseTupleResidualDifference_on_cell
    e chi m omega J4 cap4 N cap hN1 p hpos j hj hcell
  have htarget :
      fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
        fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p =
      normalizedResidual N cap p (oldLevel (e : ℝ) chi m omega N p) -
        normalizedResidual N cap p (newLevel e chi m omega J4 cap4 N p) := by
    rw [← hdict]
    exact coarseDifference_eq_normalized e chi m omega J4 cap4 N cap p
  rw [htarget]
  have hlast : 0 < actualPrimeTupleLog N p (Fin.last 3) :=
    (admitted_log_data e chi m omega N cap hN1 p had).2.2 (Fin.last 3)
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN1
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  by_cases hy4 : (4 : ℝ) ≤ p 3
  · have hanti := (admitted_log_data e chi m omega N cap hN1 p had).1
    have hactive := selected_first_three_ge_omega e chi m omega J4 j hj
      (actualPrimeTupleLog N p) hcell hanti (2 : Fin 3)
    have hcube := old_third_cube_log (e : ℝ) chi m omega (19 / 96 : ℝ)
      N cap hN1 p hpOriginal
    have hgap := HistoricalThirdCoarse.P1OriginalSmallCoordinate.fourth_numerator_gap
      omega (oldExponent (e : ℝ) chi m omega N p)
      (oldExponent (e : ℝ) chi m omega N p)
      (actualPrimeTupleLog N p) hactive hcube
      (hanti (by decide : (2 : Fin 4) < 3)) le_rfl
    have hold := HistoricalThirdCoarse.P1OriginalSmallCoordinate.actual_quotient_gt_rpow_of_gap
      hN1 p hpos (oldExponent (e : ℝ) chi m omega N p) omega hgap.2
    rw [← oldLevel_eq_rpow] at hold
    have hy1 : (1 : ℝ) < p 3 := by exact_mod_cast (hprime 3).one_lt
    have hcut : (p 3 : ℝ) ≤ (N : ℝ) ^ a :=
      (HistoricalThirdCoarse.P1OriginalSmallCoordinate.last_log_le_iff_prime_le_rpow
        hN1 p hpos a).mp hsmall.le
    have hs := P1OriginalSmallCutoffActualTail.parameter_lower_of_small_power_cutoff
      N hN (p 3 : ℝ) a omega hy1 haomega hcut
    exact hsource N cap hN hEven e chi m omega (19 / 96 : ℝ) J4 cap4 hcheck
      p hpOriginal omega L hy4 homega hL hs hbudget hlog hold.le
  · have hy3 : (p 3 : ℝ) ≤ 3 := by
      have hlt : p 3 < 4 := by exact_mod_cast (lt_of_not_ge hy4)
      exact_mod_cast (show p 3 ≤ 3 by omega)
    have hy1 : (1 : ℝ) < p 3 := by exact_mod_cast (hprime 3).one_lt
    have hcap := (admitted_last_bounds (e : ℝ) chi m omega (19 / 96 : ℝ)
      N cap hN1 p hpOriginal).2
    have hold := (old_last_lt_quotient (e : ℝ) chi m omega (19 / 96 : ℝ)
      N cap hN1 p hpOriginal).le
    have hnewLevel := oldLevel_le_newLevel e chi m omega (19 / 96 : ℝ)
      J4 cap4 hcheck N cap hN1 p hpOriginal
    have hnew : (p 3 : ℝ) ≤
        newLevel e chi m omega J4 cap4 N p / (∏ i, p i : ℕ) :=
      hold.trans (div_le_div_of_nonneg_right hnewLevel (Nat.cast_nonneg _))
    have hzero := P1OriginalSmallCutoffActualTail.actualPlus_sub_eq_zero_of_cutoff_le_three
      N cap hEven (p 3 : ℝ)
      (oldLevel (e : ℝ) chi m omega N p / (∏ i, p i : ℕ))
      (newLevel e chi m omega J4 cap4 N p / (∏ i, p i : ℕ))
      hcap hy1 hy3 hold hnew
    have heq : normalizedResidual N cap p (oldLevel (e : ℝ) chi m omega N p) -
        normalizedResidual N cap p (newLevel e chi m omega J4 cap4 N p) = 0 := by
      unfold normalizedResidual
      rw [← sub_div, ← sub_mul, hzero]
      ring
    rw [heq, abs_zero]
    positivity

end P1OriginalFourthSmallCellPointwise

end

end ImbalancedChen
