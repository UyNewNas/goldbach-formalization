import ImbalancedChen.Part3CompletedKWeightedIntegral

/-! Exact frequency selection at positive integral dilation, through the
literal actual K series. Both signs of every nonzero integer frequency are
retained. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators UpperHalfPlane
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a
open ImbalancedChen.Part3.CompletedKWeightedIntegral20261026b
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly

namespace ImbalancedChen.Part3.CompletedIntegerNonzeroFourier20261026b

def selectedK (k : ℕ+) (r : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  if (k : ℕ) ∣ r then fourierBesselTerm (r / (k : ℕ) - 1) s y 0 else 0

/-- Divisibility is proved from the literal integer frequency equation. -/
theorem selector_positive (k : ℕ+) (r : ℕ) (hr : 0 < r) (s : ℂ) (y : ℝ) :
    (∑' n : ℕ, if ((n + 1 : ℕ) : ℤ) * (k : ℤ) = (r : ℤ)
      then fourierBesselTerm n s y 0 else 0) = selectedK k r s y := by
  classical
  by_cases hd : (k : ℕ) ∣ r
  · have hq : 0 < r / (k : ℕ) := Nat.div_pos (Nat.le_of_dvd hr hd) k.pos
    have hq1 : 1 ≤ r / (k : ℕ) := hq
    have hmNat : (r / (k : ℕ) - 1 + 1) * (k : ℕ) = r := by
      rw [Nat.sub_add_cancel hq1, Nat.div_mul_cancel hd]
    have hm : (((r / (k : ℕ) - 1 + 1 : ℕ) : ℤ) * (k : ℤ)) = (r : ℤ) := by
      exact_mod_cast hmNat
    rw [tsum_eq_single (r / (k : ℕ) - 1)]
    · simp [selectedK, hd, hm]
    · intro n hn
      apply if_neg
      intro he
      have hk : (k : ℤ) ≠ 0 := by exact_mod_cast k.ne_zero
      have hh := mul_right_cancel₀ hk (he.trans hm.symm)
      have hhNat : n + 1 = r / (k : ℕ) - 1 + 1 := by exact_mod_cast hh
      exact hn (by omega)
  · rw [selectedK, if_neg hd]
    apply tsum_eq_zero
    intro n
    apply if_neg
    intro he
    have heNat : (n + 1) * (k : ℕ) = r := by exact_mod_cast he
    exact hd ⟨n + 1, by simpa [mul_comm] using heNat.symm⟩

theorem selector_opposite (k : ℕ+) (r : ℕ) (hr : 0 < r) (s : ℂ) (y : ℝ) :
    (∑' n : ℕ, if ((n + 1 : ℕ) : ℤ) * (k : ℤ) = -(r : ℤ)
      then fourierBesselTerm n s y 0 else 0) = 0 := by
  apply tsum_eq_zero
  intro n
  apply if_neg
  have hp : 0 < ((n + 1 : ℕ) : ℤ) * (k : ℤ) :=
    mul_pos (by omega) (by exact_mod_cast k.pos)
  have hrZ : 0 < (r : ℤ) := by exact_mod_cast hr
  omega

theorem weightedSum_positive (k : ℕ+) (r : ℕ) (hr : 0 < r)
    (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      (∑' n, fourierBesselTerm n s y ((k : ℝ) * x)) * integerPhase (-(r : ℤ)) x) =
        selectedK k r s y := by
  simpa using (weightedSum_integral s hy (k : ℤ) (r : ℤ)).trans
    (selector_positive k r hr s y)

theorem weightedSum_negative (k : ℕ+) (r : ℕ) (hr : 0 < r)
    (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      (∑' n, fourierBesselTerm n s y ((-(k : ℝ)) * x)) * integerPhase (-(r : ℤ)) x) = 0 := by
  have h := weightedSum_integral s hy (-(k : ℤ)) (r : ℤ)
  simp only [Int.cast_neg, mul_neg] at h
  rw [h]
  have hh : ∀ n : ℕ, (-(((n + 1 : ℕ) : ℤ) * (k : ℤ)) = (r : ℤ)) ↔
      (((n + 1 : ℕ) : ℤ) * (k : ℤ) = -(r : ℤ)) := by intro n; omega
  simp_rw [hh]
  exact selector_opposite k r hr s y

theorem weightedPairSum_positive (k : ℕ+) (r : ℕ) (hr : 0 < r)
    (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      (∑' n, nonzeroFrequencyPair n s y ((k : ℝ) * x)) * integerPhase (-(r : ℤ)) x) =
        selectedK k r s y := by
  simp_rw [scaledPairSum_eq s hy (k : ℤ), add_mul]
  rw [intervalIntegral.integral_add
    (((scaledSum_continuous s hy (k : ℤ)).mul
      (integerPhase_continuous (-(r : ℤ)))).intervalIntegrable 0 1)
    (((scaledSum_continuous s hy (-(k : ℤ))).mul
      (integerPhase_continuous (-(r : ℤ)))).intervalIntegrable 0 1)]
  rw [weightedSum_positive k r hr s hy, weightedSum_negative k r hr s hy, add_zero]

theorem pairSum_even (s : ℂ) (y x : ℝ) :
    (∑' n, nonzeroFrequencyPair n s y (-x)) =
      ∑' n, nonzeroFrequencyPair n s y x := by
  apply tsum_congr
  intro n
  simp only [nonzeroFrequencyPair, neg_neg, add_comm]

/-- Negative frequency is evaluated directly by the same two selected
series; no real-valuedness or conjugation premise is needed. -/
theorem weightedPairSum_negative (k : ℕ+) (r : ℕ) (hr : 0 < r)
    (s : ℂ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      (∑' n, nonzeroFrequencyPair n s y ((k : ℝ) * x)) * integerPhase (r : ℤ) x) =
        selectedK k r s y := by
  have h := weightedSum_integral s hy (-(k : ℤ)) (-(r : ℤ))
  simp only [Int.cast_neg, neg_neg, mul_neg, neg_inj] at h
  have hmatch : (∫ x in (0 : ℝ)..1,
      (∑' n, fourierBesselTerm n s y (-(k : ℝ) * x)) * integerPhase (r : ℤ) x) =
        selectedK k r s y := h.trans (selector_positive k r hr s y)
  have hzero := weightedSum_integral s hy (k : ℤ) (-(r : ℤ))
  simp only [neg_neg] at hzero
  have hz : (∫ x in (0 : ℝ)..1,
      (∑' n, fourierBesselTerm n s y ((k : ℝ) * x)) * integerPhase (r : ℤ) x) = 0 :=
    hzero.trans (selector_opposite k r hr s y)
  simp_rw [scaledPairSum_eq s hy (k : ℤ), add_mul]
  rw [intervalIntegral.integral_add
    (((scaledSum_continuous s hy (k : ℤ)).mul
      (integerPhase_continuous (r : ℤ))).intervalIntegrable 0 1)
    (((scaledSum_continuous s hy (-(k : ℤ))).mul
      (integerPhase_continuous (r : ℤ))).intervalIntegrable 0 1), hz, hmatch, zero_add]

def integerDilationCoefficient (k : ℕ+) (r : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  2 * (Real.sqrt ((k : ℝ) * y) : ℂ) * selectedK k r s ((k : ℝ) * y)

/-- Exact regrouping: the selected K argument is 2*pi*r*y, while its
divisor coefficient uses the quotient frequency r/k. -/
theorem integerDilationCoefficient_eq (k : ℕ+) (r : ℕ) (hr : 0 < r)
    (s : ℂ) (y : ℝ) :
    integerDilationCoefficient k r s y =
      if (k : ℕ) ∣ r then
        2 * (Real.sqrt ((k : ℝ) * y) : ℂ) *
          (((r / (k : ℕ) : ℕ) : ℂ) ^ (s - 1 / 2) *
            divisorFactor (r / (k : ℕ)) (2 * s) *
              complexOrderK (s - 1 / 2) (2 * Real.pi * r * y))
      else 0 := by
  by_cases hd : (k : ℕ) ∣ r
  · have hq : 1 ≤ r / (k : ℕ) := Nat.div_pos (Nat.le_of_dvd hr hd) k.pos
    have hm : ((r / (k : ℕ) : ℕ) : ℝ) * (k : ℝ) = (r : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hd
    have harg : 2 * Real.pi * ((r / (k : ℕ) : ℕ) : ℝ) * ((k : ℝ) * y) =
        2 * Real.pi * r * y := by
      calc
        _ = 2 * Real.pi * (((r / (k : ℕ) : ℕ) : ℝ) * (k : ℝ)) * y := by ring
        _ = _ := by rw [hm]
    simp only [integerDilationCoefficient, selectedK, if_pos hd,
      fourierBesselTerm, Nat.sub_add_cancel hq, phase, mul_zero,
      Complex.ofReal_zero, Complex.exp_zero, mul_one]
    rw [harg]
  · simp [integerDilationCoefficient, selectedK, hd]

theorem completedFourier_nonzero_integral (k : ℕ+) (r : ℕ) (hr : 0 < r)
    (s : ℂ) {y : ℝ} (hy : 0 < y) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (∫ x in (0 : ℝ)..1,
      completedEisensteinFourier s y ((k : ℝ) * x) * integerPhase (ε * (r : ℤ)) x) =
        2 * (Real.sqrt y : ℂ) * selectedK k r s y := by
  have hrZ : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have hc := scaledPairSum_continuous s hy (k : ℤ)
  have hp := integerPhase_continuous (ε * (r : ℤ))
  unfold completedEisensteinFourier
  simp_rw [add_mul, mul_assoc]
  rw [intervalIntegral.integral_add
    ((continuous_const.mul hp).intervalIntegrable 0 1)
    ((continuous_const.mul (hc.mul hp)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rcases hε with rfl | rfl
  · simp only [one_mul]
    rw [integerPhase_integral, if_neg hrZ, mul_zero, zero_add,
      weightedPairSum_negative k r hr s hy]
  · simp only [neg_one_mul]
    rw [integerPhase_integral, if_neg (neg_ne_zero.mpr hrZ), mul_zero, zero_add,
      weightedPairSum_positive k r hr s hy]

/-- The genuine full-level continued family at the actual integer dilation.
All s are retained; in particular there is no central completion division. -/
theorem completed_integer_nonzero_integral (k : ℕ+) (r : ℕ) (hr : 0 < r)
    (s : ℂ) (y : ℝ) (hy : 0 < y) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (∫ x in (0 : ℝ)..1,
      completedActualEisenstein s (pnatDilate k (horizontalPoint y hy x)) *
        integerPhase (ε * (r : ℤ)) x) = integerDilationCoefficient k r s y := by
  have hky : 0 < (k : ℝ) * y := mul_pos (by exact_mod_cast k.pos) hy
  simpa [completedActualEisenstein, pnatDilate, dilate, horizontalPoint,
    Complex.mul_re, Complex.mul_im, integerDilationCoefficient] using
      completedFourier_nonzero_integral k r hr s hky ε hε

end ImbalancedChen.Part3.CompletedIntegerNonzeroFourier20261026b
