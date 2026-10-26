import ImbalancedChen.Part3IntegerDilatedEisensteinHeightJets
import ImbalancedChen.Part3FiniteCompletedOldformSpatial

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The existing actual finite completed oldform chart is separated into its
literal completed constants and actual nonconstant remainder, including
the genuine first height derivative. Both remainder means vanish and
their pointwise exponential bounds have explicit finite coefficient and
dilation masses. This proves the missing finite analytic step; no
completed jet, zero mean, norm estimate or boundary identity is an input.
The exact center remains inside completedConstant/completedFirst.
-/

noncomputable section
open Complex MeasureTheory
open ImbalancedChen.Part3.IntegerDilatedEisensteinHeightJets20261026b
open ImbalancedChen.Part3.FiniteCompletedOldformSpatial20261026a
open ImbalancedChen.Part3.ActualEisensteinHorocycleRemainder20261026b
open ImbalancedChen.Part3.CompletedEisensteinCuspTail20261025a
open ImbalancedChen.Part3.ActualEisensteinHeightDerivativeTail20261026b

namespace ImbalancedChen.Part3.FiniteOldformHeightRemainders20261026b

def constantSum (T : List (ℕ+ × ℂ)) (s : ℂ) (y : ℝ) : ℂ :=
  (T.map (fun t => t.2 * scaledConstant t.1 s y)).sum

def constantFirstSum (T : List (ℕ+ × ℂ)) (s : ℂ) (y : ℝ) : ℂ :=
  (T.map (fun t => t.2 * scaledConstantFirst t.1 s y)).sum

def remainderSum (T : List (ℕ+ × ℂ)) (s : ℂ) (y x : ℝ) : ℂ :=
  (T.map (fun t => t.2 * scaledRemainder t.1 s y x)).sum

def remainderFirstSum (T : List (ℕ+ × ℂ)) (s : ℂ) (y x : ℝ) : ℂ :=
  (T.map (fun t => t.2 * scaledRemainderY t.1 s y x)).sum

def coefficientMass (T : List (ℕ+ × ℂ)) : ℝ := (T.map (fun t => ‖t.2‖)).sum

def firstHeightMass (T : List (ℕ+ × ℂ)) : ℝ :=
  (T.map (fun t => ‖t.2‖ * (t.1 : ℝ))).sum

theorem coefficientMass_nonneg (T : List (ℕ+ × ℂ)) : 0 ≤ coefficientMass T := by
  induction T with
  | nil => simp [coefficientMass]
  | cons t T ih => simpa only [coefficientMass, List.map_cons, List.sum_cons] using
      add_nonneg (norm_nonneg t.2) ih

theorem firstHeightMass_nonneg (T : List (ℕ+ × ℂ)) : 0 ≤ firstHeightMass T := by
  induction T with
  | nil => simp [firstHeightMass]
  | cons t T ih => simpa only [firstHeightMass, List.map_cons, List.sum_cons] using
      add_nonneg (mul_nonneg (norm_nonneg t.2) (by positivity)) ih

theorem completedTermsChart_eq_constant_remainder (T : List (ℕ+ × ℂ))
    (s : ℂ) (x y : ℝ) :
    completedTermsChart T s (x, y) = constantSum T s y + remainderSum T s y x := by
  induction T with
  | nil => simp [completedTermsChart, constantSum, remainderSum]
  | cons t T ih =>
      simp only [completedTermsChart, constantSum, remainderSum, List.map_cons,
        List.sum_cons] at ih ⊢
      rw [ih]
      simp only [scaledConstant, scaledRemainder, actualRemainder]
      ring

theorem constantSum_hasDerivAt (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (constantSum T s) (constantFirstSum T s y) y := by
  induction T with
  | nil => simpa [constantSum, constantFirstSum] using hasDerivAt_const y (0 : ℂ)
  | cons t T ih =>
      simpa only [constantSum, constantFirstSum, List.map_cons, List.sum_cons] using
        ((scaledConstant_hasDerivAt t.1 s hs0 hs1 hy).const_mul t.2).add ih

theorem remainderSum_hasDerivAt_y (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun v : ℝ => remainderSum T s v x) (remainderFirstSum T s y x) y := by
  induction T with
  | nil => simpa [remainderSum, remainderFirstSum] using hasDerivAt_const y (0 : ℂ)
  | cons t T ih =>
      simpa only [remainderSum, remainderFirstSum, List.map_cons, List.sum_cons] using
        ((scaledRemainder_hasDerivAt_y t.1 s hs0 hs1 hy x).const_mul t.2).add ih

/-- Genuine first height derivative of the ORIGINAL finite completed chart. -/
theorem completedTermsChart_hasDerivAt_y (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun v : ℝ => completedTermsChart T s (x, v))
      (constantFirstSum T s y + remainderFirstSum T s y x) y := by
  simp_rw [completedTermsChart_eq_constant_remainder]
  exact (constantSum_hasDerivAt T s hs0 hs1 hy).add
    (remainderSum_hasDerivAt_y T s hs0 hs1 hy x)

theorem remainderSum_continuous_x (T : List (ℕ+ × ℂ)) (s : ℂ)
    {y : ℝ} (hy : 0 < y) : Continuous (remainderSum T s y) := by
  induction T with
  | nil => simpa [remainderSum] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  | cons t T ih => simpa only [remainderSum, List.map_cons, List.sum_cons] using
      ((scaledRemainder_continuous_x t.1 s hy).const_mul t.2).add ih

theorem remainderFirstSum_continuous_x (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    Continuous (remainderFirstSum T s y) := by
  induction T with
  | nil => simpa [remainderFirstSum] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  | cons t T ih => simpa only [remainderFirstSum, List.map_cons, List.sum_cons] using
      ((scaledRemainderY_continuous_x t.1 s hs0 hs1 hy).const_mul t.2).add ih

theorem remainderSum_mean_zero (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, remainderSum T s y x) = 0 := by
  induction T with
  | nil => simp [remainderSum]
  | cons t T ih =>
      simp only [remainderSum, List.map_cons, List.sum_cons]
      rw [intervalIntegral.integral_add
        (((scaledRemainder_continuous_x t.1 s hy).const_mul t.2).intervalIntegrable 0 1)
        ((remainderSum_continuous_x T s hy).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul, scaledRemainder_mean_zero t.1 s hs0 hs1 hy, ih]
      simp

theorem remainderFirstSum_mean_zero (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, remainderFirstSum T s y x) = 0 := by
  induction T with
  | nil => simp [remainderFirstSum]
  | cons t T ih =>
      simp only [remainderFirstSum, List.map_cons, List.sum_cons]
      rw [intervalIntegral.integral_add
        (((scaledRemainderY_continuous_x t.1 s hs0 hs1 hy).const_mul t.2).intervalIntegrable 0 1)
        ((remainderFirstSum_continuous_x T s hs0 hs1 hy).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul, scaledRemainderY_mean_zero t.1 s hs0 hs1 hy, ih]
      simp

theorem completedTermsChart_first_mean (T : List (ℕ+ × ℂ)) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, deriv (fun v : ℝ => completedTermsChart T s (x, v)) y) =
      constantFirstSum T s y := by
  simp_rw [(completedTermsChart_hasDerivAt_y T s hs0 hs1 hy _).deriv]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((remainderFirstSum_continuous_x T s hs0 hs1 hy).intervalIntegrable 0 1),
    remainderFirstSum_mean_zero T s hs0 hs1 hy]
  simp

theorem remainderSum_bound (T : List (ℕ+ × ℂ)) (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖remainderSum T s y x‖ ≤
      (coefficientMass T * cuspTailConstant M) * Real.exp (-(Real.pi / 2) * y) := by
  induction T with
  | nil => simp [remainderSum, coefficientMass]
  | cons t T ih =>
      change ‖t.2 * scaledRemainder t.1 s y x + remainderSum T s y x‖ ≤ _
      calc
        _ ≤ ‖t.2 * scaledRemainder t.1 s y x‖ + ‖remainderSum T s y x‖ := norm_add_le _ _
        _ = ‖t.2‖ * ‖scaledRemainder t.1 s y x‖ + ‖remainderSum T s y x‖ := by rw [norm_mul]
        _ ≤ ‖t.2‖ * (cuspTailConstant M * Real.exp (-(Real.pi / 2) * y)) +
            (coefficientMass T * cuspTailConstant M) * Real.exp (-(Real.pi / 2) * y) :=
          add_le_add (mul_le_mul_of_nonneg_left (scaledRemainder_bound t.1 M hs hy x)
            (norm_nonneg t.2)) ih
        _ = _ := by simp only [coefficientMass, List.map_cons, List.sum_cons]; ring

theorem remainderFirstSum_bound (T : List (ℕ+ × ℂ)) (M : ℕ) {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖remainderFirstSum T s y x‖ ≤
      (firstHeightMass T * derivativeTailConstant M) * Real.exp (-(Real.pi / 2) * y) := by
  induction T with
  | nil => simp [remainderFirstSum, firstHeightMass]
  | cons t T ih =>
      change ‖t.2 * scaledRemainderY t.1 s y x + remainderFirstSum T s y x‖ ≤ _
      calc
        _ ≤ ‖t.2 * scaledRemainderY t.1 s y x‖ + ‖remainderFirstSum T s y x‖ := norm_add_le _ _
        _ = ‖t.2‖ * ‖scaledRemainderY t.1 s y x‖ + ‖remainderFirstSum T s y x‖ := by rw [norm_mul]
        _ ≤ ‖t.2‖ * (((t.1 : ℝ) * derivativeTailConstant M) * Real.exp (-(Real.pi / 2) * y)) +
            (firstHeightMass T * derivativeTailConstant M) * Real.exp (-(Real.pi / 2) * y) :=
          add_le_add (mul_le_mul_of_nonneg_left (scaledRemainderY_bound t.1 M hs hs0 hs1 hy x)
            (norm_nonneg t.2)) ih
        _ = _ := by simp only [firstHeightMass, List.map_cons, List.sum_cons]; ring

end ImbalancedChen.Part3.FiniteOldformHeightRemainders20261026b
