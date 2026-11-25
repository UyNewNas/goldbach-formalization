import ImbalancedChen.Part3PrimeProductChartTransfer
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Labelled prime products from von Mangoldt weights

Complete labelled coordinates preserve every original product and tuple
multiplicity. The residual is the union of tuples with a proper prime power.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

/-- The ordinary von Mangoldt coefficient divided by the logarithm of the
coordinate, with the standard total division at zero and one. -/
def vonMangoldtOverLog (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.log n

/-- Prime powers of exponent at least two. -/
def properPrimePower (n : ℕ) : Prop := IsPrimePow n ∧ ¬n.Prime

theorem properPrimePower_iff_exists (n : ℕ) :
    properPrimePower n ↔ ∃ p j : ℕ, p.Prime ∧ 2 ≤ j ∧ p ^ j = n := by
  constructor
  · rintro ⟨hpp, hnp⟩
    obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    refine ⟨p, j, hp, ?_, rfl⟩
    have hj1 : j ≠ 1 := by
      rintro rfl
      exact hnp (by simpa only [pow_one] using hp)
    omega
  · rintro ⟨p, j, hp, hj, rfl⟩
    exact ⟨hp.isPrimePow.pow (by omega), Nat.Prime.not_prime_pow hj⟩

theorem vonMangoldtOverLog_prime {p : ℕ} (hp : p.Prime) :
    vonMangoldtOverLog p = 1 := by
  rw [vonMangoldtOverLog, ArithmeticFunction.vonMangoldt_apply_prime hp]
  apply div_self
  exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'

theorem vonMangoldtOverLog_of_not_isPrimePow {n : ℕ} (hn : ¬IsPrimePow n) :
    vonMangoldtOverLog n = 0 := by
  rw [vonMangoldtOverLog, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]

theorem vonMangoldtOverLog_prime_pow {p j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    vonMangoldtOverLog (p ^ j) = (j : ℝ)⁻¹ := by
  rw [vonMangoldtOverLog, ArithmeticFunction.vonMangoldt_apply_pow hj.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  have hl : (Real.log (p : ℝ)) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp

theorem vonMangoldtOverLog_nonzero_iff (n : ℕ) :
    vonMangoldtOverLog n ≠ 0 ↔ IsPrimePow n := by
  constructor
  · intro h
    by_contra hn
    exact h (vonMangoldtOverLog_of_not_isPrimePow hn)
  · intro h
    obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff n).mp h
    rw [vonMangoldtOverLog_prime_pow hp hj]
    exact inv_ne_zero (by exact_mod_cast hj.ne')

theorem vonMangoldtOverLog_mem_Icc (n : ℕ) :
    vonMangoldtOverLog n ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : IsPrimePow n
  · obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff n).mp h
    rw [vonMangoldtOverLog_prime_pow hp hj]
    exact ⟨inv_nonneg.mpr (Nat.cast_nonneg _),
      inv_le_one_of_one_le₀ (by exact_mod_cast hj)⟩
  · rw [vonMangoldtOverLog_of_not_isPrimePow h]
    exact ⟨le_rfl, zero_le_one⟩

/-- The single-coordinate prime indicator has the exact proper-power correction. -/
theorem primeIndicator_eq_vonMangoldtOverLog_sub (n : ℕ) :
    (if n.Prime then (1 : ℝ) else 0) =
      vonMangoldtOverLog n - (if properPrimePower n then vonMangoldtOverLog n else 0) := by
  by_cases hp : n.Prime
  · simp [hp, properPrimePower, vonMangoldtOverLog_prime hp]
  · by_cases hpp : IsPrimePow n
    · simp [hp, properPrimePower, hpp]
    · simp [hp, properPrimePower, hpp, vonMangoldtOverLog_of_not_isPrimePow hpp]

/-- The product of the normalized von Mangoldt weights over the original labels. -/
def labelledVonMangoldtWeight {k P : ℕ} (t : Fin k → Fin (P + 1)) : ℝ :=
  ∏ i : Fin k, vonMangoldtOverLog (t i).val

theorem labelledVonMangoldtWeight_eq_prod_div {k P : ℕ} (t : Fin k → Fin (P + 1)) :
    labelledVonMangoldtWeight t =
      (∏ i : Fin k, ArithmeticFunction.vonMangoldt (t i).val) /
        ∏ i : Fin k, Real.log (t i).val := by
  unfold labelledVonMangoldtWeight vonMangoldtOverLog
  exact Finset.prod_div_distrib _ _

theorem labelledVonMangoldtWeight_mem_Icc {k P : ℕ} (t : Fin k → Fin (P + 1)) :
    labelledVonMangoldtWeight t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold labelledVonMangoldtWeight
  exact ⟨Finset.prod_nonneg (fun i _ => (vonMangoldtOverLog_mem_Icc (t i).val).1),
    Finset.prod_le_one (fun i _ => (vonMangoldtOverLog_mem_Icc (t i).val).1)
      (fun i _ => (vonMangoldtOverLog_mem_Icc (t i).val).2)⟩

/-- Complete-coordinate mass with the ordinary von Mangoldt weight. -/
def labelledVonMangoldtProductMass (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) : ℕ → ℂ :=
  finiteProductMass Finset.univ labelledProduct
    (fun t => ((W t * labelledVonMangoldtWeight t : ℝ) : ℂ))

/-- Each tuple with a proper-power coordinate is subtracted once, even if
several of its labels have proper powers. -/
def labelledProperPowerResidual (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) : ℕ → ℂ :=
  finiteProductMass (Finset.univ.filter
      (fun t : Fin k → Fin (P + 1) => ∃ i : Fin k, properPrimePower (t i).val))
    labelledProduct (fun t => ((W t * labelledVonMangoldtWeight t : ℝ) : ℂ))

/-- The correction is bounded by the absolute original weights of the
proper-power tuples in the same complete-product fibre. -/
theorem norm_labelledProperPowerResidual_le
    (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) (b : ℕ) :
    ‖labelledProperPowerResidual k P W b‖ ≤
      ∑ t ∈ Finset.univ.filter (fun t : Fin k → Fin (P + 1) =>
        ∃ i : Fin k, properPrimePower (t i).val),
        if labelledProduct t = b then |W t| else 0 := by
  unfold labelledProperPowerResidual finiteProductMass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t _ => ?_))
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (labelledVonMangoldtWeight_mem_Icc t).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (labelledVonMangoldtWeight_mem_Icc t).2
  · simp

/-- Exact complete-product coefficient identity for every labelled chart. -/
theorem labelledPrimeProductMass_eq_vonMangoldt_sub_properPower
    (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) (b : ℕ) :
    labelledPrimeProductMass k P W b =
      labelledVonMangoldtProductMass k P W b - labelledProperPowerResidual k P W b := by
  unfold labelledPrimeProductMass labelledVonMangoldtProductMass
    labelledProperPowerResidual finiteProductMass
  change
    (∑ t ∈ Finset.univ.filter (fun t => ∀ i : Fin k, (t i).val.Prime),
      if labelledProduct t = b then (W t : ℂ) else 0) =
    (∑ t : Fin k → Fin (P + 1), if labelledProduct t = b then
      ((W t * labelledVonMangoldtWeight t : ℝ) : ℂ) else 0) -
    ∑ t ∈ Finset.univ.filter (fun t => ∃ i : Fin k, properPrimePower (t i).val),
      if labelledProduct t = b then ((W t * labelledVonMangoldtWeight t : ℝ) : ℂ) else 0
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hp : ∀ i : Fin k, (t i).val.Prime
  · have hn : ¬ ∃ i : Fin k, properPrimePower (t i).val := by
      rintro ⟨i, _, h⟩
      exact h (hp i)
    have hw : labelledVonMangoldtWeight t = 1 := by
      unfold labelledVonMangoldtWeight
      exact Finset.prod_eq_one (fun i _ => vonMangoldtOverLog_prime (hp i))
    simp [hp, hn, hw]
  · by_cases hn : ∃ i : Fin k, properPrimePower (t i).val
    · simp [hp, hn]
    · obtain ⟨i, hi⟩ := not_forall.mp hp
      have hpp : ¬ IsPrimePow (t i).val := fun h => hn ⟨i, h, hi⟩
      have hw : labelledVonMangoldtWeight t = 0 := by
        unfold labelledVonMangoldtWeight
        exact Finset.prod_eq_zero (Finset.mem_univ i) (vonMangoldtOverLog_of_not_isPrimePow hpp)
      simp [hp, hn, hw]

/-- The same exact correction for the signed distribution error, with the
original complete-product congruence and coprime-mean kernels. -/
theorem primeProductSignedError_eq_vonMangoldt_sub_properPower
    (k P N : ℕ) (Q B : Finset ℕ) (ρ : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (hB : ∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B) :
    (primeProductSignedError k P N Q ρ W : ℂ) =
      finiteProductSignedError B Q N (fun q => (ρ q : ℂ)) (labelledVonMangoldtProductMass k P W) -
        finiteProductSignedError B Q N (fun q => (ρ q : ℂ)) (labelledProperPowerResidual k P W) := by
  rw [primeProductSignedError_eq_fibreError k P N Q B ρ W hB]
  simp only [finiteProductSignedError, labelledPrimeProductMass_eq_vonMangoldt_sub_properPower,
    sub_mul, Finset.sum_sub_distrib, mul_sub]

end

end ImbalancedChen.Part3
