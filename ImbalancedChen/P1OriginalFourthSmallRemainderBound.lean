import ImbalancedChen.P1OriginalFourthSmallCellPointwise

/-!
# Signed original-coarse fourth small remainder from the actual first moment

The pointwise actual PLUS-tail difference and the genuine four-prime first
moment are summed on the identical original `HistoricalThirdCoarse.policy`
carrier. The remaining moving-parameter conditions are explicit arithmetic
budgets, not a signed-remainder supplier. Source-only/uncompiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open P1OriginalCoarseContinuation
open P1OriginalCoarseFourthArithmeticWall
open P1OriginalFourthSmallPrimeStratification

namespace P1OriginalFourthSmallRemainderBound

private def cellMoment (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (j : FourthCell m) : ℝ :=
  ∑ p ∈ smallCellTuples e chi m omega a N cap j,
    (∏ i, 1 / ((p i : ℝ) - 1)) * actualPrimeTupleLog N p (Fin.last 3)

private def cellMass (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (j : FourthCell m) : ℝ :=
  ∑ p ∈ smallCellTuples e chi m omega a N cap j,
    ∏ i, 1 / ((p i : ℝ) - 1)

private theorem weight_nonneg (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (hN : 1 < N) (j : FourthCell m) (p : Fin 4 → ℕ)
    (hp : p ∈ smallCellTuples e chi m omega a N cap j) :
    0 ≤ ∏ i, 1 / ((p i : ℝ) - 1) := by
  have had := (Finset.mem_filter.mp hp).1
  have hprime := (admitted_log_data e chi m omega N cap hN p had).2.1
  apply Finset.prod_nonneg
  intro i _
  have hi : (1 : ℝ) < p i := by exact_mod_cast (hprime i).one_lt
  positivity

/-- The terminal actual prime is odd, so its logarithmic coordinate is
at least `log 3/log N`. This pays the unweighted exponential-error mass
from the already controlled weighted first moment. -/
private theorem cellMass_le_log_times_moment
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (j : FourthCell m) :
    cellMass e chi m omega a N cap j ≤
      (Real.log (N : ℝ) / Real.log 3) * cellMoment e chi m omega a N cap j := by
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  unfold cellMass cellMoment
  calc
    (∑ p ∈ smallCellTuples e chi m omega a N cap j,
        ∏ i, 1 / ((p i : ℝ) - 1)) ≤
      ∑ p ∈ smallCellTuples e chi m omega a N cap j,
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          ((Real.log (N : ℝ) / Real.log 3) *
            actualPrimeTupleLog N p (Fin.last 3)) := by
      apply Finset.sum_le_sum
      intro p hp
      have had := (Finset.mem_filter.mp hp).1
      have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
        (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) p).mp had
      have hq := hd.2.1 (Fin.last 3)
      have hprime := mem_roughPrimeUniverse_prime hq
      have h2N : 2 ∣ N := by
        obtain ⟨u, hu⟩ := hEven
        exact ⟨u, by omega⟩
      have hne : p (Fin.last 3) ≠ 2 := by
        intro heq
        exact mem_roughPrimeUniverse_not_dvd hq (heq ▸ h2N)
      have hthree : 3 ≤ p (Fin.last 3) := by
        have := hprime.two_le
        omega
      have hlogp : Real.log (3 : ℝ) ≤ Real.log (p (Fin.last 3) : ℝ) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast hthree
      have hratio : 1 ≤ Real.log (p (Fin.last 3) : ℝ) / Real.log 3 :=
        (one_le_div hlog3).mpr hlogp
      have heq : (Real.log (N : ℝ) / Real.log 3) *
          actualPrimeTupleLog N p (Fin.last 3) =
          Real.log (p (Fin.last 3) : ℝ) / Real.log 3 := by
        unfold actualPrimeTupleLog
        field_simp [hlogN.ne', hlog3.ne']
      rw [heq]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio
        (weight_nonneg e chi m omega a N cap hN j p hp)
    _ = (Real.log (N : ℝ) / Real.log 3) *
        (∑ p ∈ smallCellTuples e chi m omega a N cap j,
          (∏ i, 1 / ((p i : ℝ) - 1)) *
            actualPrimeTupleLog N p (Fin.last 3)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- The same original selected-cell signed remainder is bounded by the
pointwise linear-cutoff coefficient times the true prime first moment,
plus its displayed moving exponential payment. -/
private theorem cell_remainder_le_moment_and_mass
    (C : ℝ) (hC : 0 < C)
    (hpoint : ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ),
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
            (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L))
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (homega : 0 < omega) (ha : 0 < a) (haomega : 2 * a ≤ omega)
    (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ)
    (hcheck : h34Check e chi m omega J4 cap4 = true)
    (N cap : ℕ) (hN : 2 ≤ N) (hEven : Even N)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (L : ℝ) (hL : 2 ≤ L)
    (hbudget : L ^ 13 ≤ omega * Real.log (N : ℝ))
    (hlog : Real.exp 1 ≤ omega * Real.log (N : ℝ)) :
    |P1OriginalFourthLimit.smallCellRemainder e chi m omega a J4 cap4 N cap j| ≤
      (2 * C / omega ^ 2) * cellMoment e chi m omega a N cap j +
        ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
          cellMass e chi m omega a N cap j := by
  have hN1 : 1 < N := by omega
  rw [smallCellRemainder_eq_signed_source e chi m omega a J4 cap4 N cap hN1 j]
  calc
    |∑ p ∈ smallCellTuples e chi m omega a N cap j,
        signedTupleWeight p *
          (fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
            fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p)| ≤
      ∑ p ∈ smallCellTuples e chi m omega a N cap j,
        |signedTupleWeight p *
          (fourthTuplePlusResidualP1 N cap (thirdCellExponent e m j : ℝ) p -
            fourthTuplePlusResidualP1 N cap (cap4 j : ℝ) p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ smallCellTuples e chi m omega a N cap j,
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          ((2 * C / omega ^ 2) * actualPrimeTupleLog N p (Fin.last 3) +
            (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [signedTupleWeight_eq, abs_mul,
        abs_of_nonneg (weight_nonneg e chi m omega a N cap hN1 j p hp)]
      exact mul_le_mul_of_nonneg_left
        (hpoint e chi m omega a homega ha haomega J4 cap4 hcheck
          N cap hN hEven j hj p hp L hL hbudget hlog)
        (weight_nonneg e chi m omega a N cap hN1 j p hp)
    _ = (2 * C / omega ^ 2) * cellMoment e chi m omega a N cap j +
        ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
          cellMass e chi m omega a N cap j := by
      unfold cellMoment cellMass
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro p _ <;> ring

/-- The literal signed fourth small-cell error is controlled by the genuine
terminal-prime first moment once the moving exponential error has a unit
budget. The absolute constant comes from the actual original PLUS tail. -/
theorem exists_original_smallRemainder_abs_le :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ),
        0 < omega → 0 < a → 2 * a ≤ omega →
      ∀ (J4 : Finset (FourthCell m)) (cap4 : FourthCell m → ℚ),
        h34Check e chi m omega J4 cap4 = true →
      ∀ (N cap : ℕ), 2 ≤ N → Even N →
      ∀ L : ℝ, 2 ≤ L → L ^ 13 ≤ omega * Real.log (N : ℝ) →
        Real.exp 1 ≤ omega * Real.log (N : ℝ) →
        Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤
          a * Real.log (N : ℝ) *
            (Real.log (3 : ℝ) - Real.log (2 : ℝ)) →
        ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
          (Real.log (N : ℝ) / Real.log 3) ≤ 1 →
        |P1OriginalFourthLimit.smallRemainder
            e chi m omega a J4 cap4 N cap| ≤
          ((selectedFourthCells e chi m omega J4).card : ℝ) *
            (2 * C / omega ^ 2 + 1) *
            (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
            (4 * a + 6 * K *
              (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hpoint⟩ :=
    P1OriginalFourthSmallCellPointwise.exists_original_smallCell_pointwise_linear_bound
  obtain ⟨K, hK, hmomentSource⟩ :=
    P1OriginalFourthFiniteBinBudget.exists_original_smallCell_weighted_moment_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro e chi m omega a homega ha haomega J4 cap4 hcheck
    N cap hN hEven L hL hbudget hlog hscale hExp
  have hN1 : 1 < N := by omega
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN1
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ 2 * C / omega ^ 2 := by positivity
  have hB : 0 ≤ (C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L) := by
    positivity
  have hM : 0 ≤ actualPrimeReciprocalMass N omega (19 / 96 : ℝ) := by
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  have hbudgetNonneg : 0 ≤
      (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
        (4 * a + 6 * K *
          (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
    have : 0 ≤ K := by linarith
    positivity
  have hcell : ∀ j ∈ selectedFourthCells e chi m omega J4,
      |P1OriginalFourthLimit.smallCellRemainder
        e chi m omega a J4 cap4 N cap j| ≤
        (2 * C / omega ^ 2 + 1) *
          (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
          (4 * a + 6 * K *
            (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
    intro j hj
    have hraw := cell_remainder_le_moment_and_mass C hC hpoint
      e chi m omega a homega ha haomega J4 cap4 hcheck
      N cap hN hEven j hj L hL hbudget hlog
    have hmass := cellMass_le_log_times_moment
      e chi m omega a N cap hN1 hEven j
    have hMomNonneg : 0 ≤ cellMoment e chi m omega a N cap j := by
      unfold cellMoment
      apply Finset.sum_nonneg
      intro p hp
      have had := (Finset.mem_filter.mp hp).1
      have hlast : 0 < actualPrimeTupleLog N p (Fin.last 3) :=
        (admitted_log_data e chi m omega N cap hN1 p had).2.2 (Fin.last 3)
      exact mul_nonneg (weight_nonneg e chi m omega a N cap hN1 j p hp) hlast.le
    have hfirst := mul_le_mul_of_nonneg_left hmass hB
    have hsecond := mul_le_mul_of_nonneg_right hExp hMomNonneg
    have hcombined :
        (2 * C / omega ^ 2) * cellMoment e chi m omega a N cap j +
          ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
            cellMass e chi m omega a N cap j ≤
          (2 * C / omega ^ 2 + 1) *
            cellMoment e chi m omega a N cap j := by
      calc
        _ ≤ (2 * C / omega ^ 2) * cellMoment e chi m omega a N cap j +
            ((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
              ((Real.log (N : ℝ) / Real.log 3) *
                cellMoment e chi m omega a N cap j) :=
          add_le_add_left hfirst _
        _ = (2 * C / omega ^ 2) * cellMoment e chi m omega a N cap j +
              (((C / Real.log 4) * Real.log (N : ℝ) * Real.exp (-L)) *
                (Real.log (N : ℝ) / Real.log 3)) *
                cellMoment e chi m omega a N cap j := by ring
        _ ≤ (2 * C / omega ^ 2) * cellMoment e chi m omega a N cap j +
              1 * cellMoment e chi m omega a N cap j :=
          add_le_add_left hsecond _
        _ = _ := by ring
    have hmoment := hmomentSource e chi m omega a ha
      J4 N cap hN1 hEven j hj hscale
    have hscaled := mul_le_mul_of_nonneg_left hmoment (by linarith :
      0 ≤ 2 * C / omega ^ 2 + 1)
    simpa only [mul_assoc] using (hraw.trans hcombined).trans hscaled
  unfold P1OriginalFourthLimit.smallRemainder
  calc
    |∑ j ∈ selectedFourthCells e chi m omega J4,
        P1OriginalFourthLimit.smallCellRemainder
          e chi m omega a J4 cap4 N cap j| ≤
      ∑ j ∈ selectedFourthCells e chi m omega J4,
        |P1OriginalFourthLimit.smallCellRemainder
          e chi m omega a J4 cap4 N cap j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ selectedFourthCells e chi m omega J4,
          (2 * C / omega ^ 2 + 1) *
            (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
            (4 * a + 6 * K *
              (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hcell j hj
    _ = ((selectedFourthCells e chi m omega J4).card : ℝ) *
          (2 * C / omega ^ 2 + 1) *
          (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
          (4 * a + 6 * K *
            (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end P1OriginalFourthSmallRemainderBound

end

end ImbalancedChen
