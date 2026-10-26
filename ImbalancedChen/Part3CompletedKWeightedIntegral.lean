import ImbalancedChen.Part3CompletedEisensteinIntegerMean

/-! Actual weighted K-series integrals. The exchange of integral and sum is
paid by the existing norm-summability of the literal K terms, since the
integer character has norm one. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

noncomputable section
open Set MeasureTheory Complex
open scoped Topology BigOperators
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a

namespace ImbalancedChen.Part3.CompletedKWeightedIntegral20261026b

def integerPhase (j : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (j : ℝ) * x : ℝ) : ℂ) * Complex.I)

theorem integerPhase_continuous (j : ℤ) : Continuous (integerPhase j) := by
  unfold integerPhase
  fun_prop

theorem integerPhase_norm (j : ℤ) (x : ℝ) : ‖integerPhase j x‖ = 1 := by
  simp [integerPhase, Complex.norm_exp, Complex.mul_re]

theorem integerPhase_integral (j : ℤ) :
    (∫ x in (0 : ℝ)..1, integerPhase j x) = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · simp [hj, integerPhase]
  · rw [if_neg hj]
    let c : ℂ := (j : ℂ) * (2 * Real.pi * Complex.I)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (Int.cast_ne_zero.mpr hj)
        (mul_ne_zero (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    have he : integerPhase j = fun x : ℝ => Complex.exp (c * x) := by
      funext x
      unfold integerPhase c
      congr 1
      push_cast
      ring
    rw [he, integral_exp_mul_complex hc]
    simp only [mul_one, mul_zero, Complex.exp_zero]
    rw [show Complex.exp c = 1 from Complex.exp_int_mul_two_pi_mul_I j]
    simp

theorem weightedTerm_eq (n : ℕ) (s : ℂ) (y : ℝ) (k m : ℤ) (x : ℝ) :
    fourierBesselTerm n s y ((k : ℝ) * x) * integerPhase (-m) x =
      fourierBesselTerm n s y 0 * integerPhase (((n + 1 : ℕ) : ℤ) * k - m) x := by
  unfold fourierBesselTerm phase integerPhase
  simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem weightedTerm_continuous (n : ℕ) (s : ℂ) (y : ℝ) (k m : ℤ) :
    Continuous (fun x : ℝ =>
      fourierBesselTerm n s y ((k : ℝ) * x) * integerPhase (-m) x) :=
  (scaledTerm_continuous n s y k).mul (integerPhase_continuous (-m))

theorem weightedTerm_norm (n : ℕ) (s : ℂ) (y : ℝ) (k m : ℤ) (x : ℝ) :
    ‖fourierBesselTerm n s y ((k : ℝ) * x) * integerPhase (-m) x‖ =
      ‖fourierBesselTerm n s y 0‖ := by
  rw [norm_mul, integerPhase_norm, mul_one, scaledTerm_norm]

theorem weightedTerm_integral (n : ℕ) (s : ℂ) (y : ℝ) (k m : ℤ) :
    (∫ x in (0 : ℝ)..1,
      fourierBesselTerm n s y ((k : ℝ) * x) * integerPhase (-m) x) =
        if ((n + 1 : ℕ) : ℤ) * k = m then fourierBesselTerm n s y 0 else 0 := by
  simp_rw [weightedTerm_eq]
  rw [intervalIntegral.integral_const_mul, integerPhase_integral]
  by_cases h : ((n + 1 : ℕ) : ℤ) * k = m
  · simp [h]
  · simp [sub_ne_zero.mpr h, h]

/-- Termwise Fourier integration of the actual infinite K series. -/
theorem weightedSum_integral (s : ℂ) {y : ℝ} (hy : 0 < y) (k m : ℤ) :
    (∫ x in (0 : ℝ)..1,
      (∑' n, fourierBesselTerm n s y ((k : ℝ) * x)) * integerPhase (-m) x) =
        ∑' n : ℕ, if ((n + 1 : ℕ) : ℤ) * k = m then fourierBesselTerm n s y 0 else 0 := by
  let F : ℕ → ℝ → ℂ := fun n x =>
    fourierBesselTerm n s y ((k : ℝ) * x) * integerPhase (-m) x
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro n
    exact ((weightedTerm_continuous n s y k m).intervalIntegrable 0 1).1
  have hnorm (n : ℕ) : (∫ x in Ioc (0 : ℝ) 1, ‖F n x‖) =
      ‖fourierBesselTerm n s y 0‖ := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [F, weightedTerm_norm]
    simp
  have hsum : Summable (fun n => ∫ x in Ioc (0 : ℝ) 1, ‖F n x‖) := by
    simpa only [hnorm] using fourierBessel_norm_summable s hy 0
  simp_rw [← tsum_mul_right]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  apply tsum_congr
  intro n
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact weightedTerm_integral n s y k m

end ImbalancedChen.Part3.CompletedKWeightedIntegral20261026b
