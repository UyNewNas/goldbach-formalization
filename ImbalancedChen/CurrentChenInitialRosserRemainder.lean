import ImbalancedChen.CurrentChenInitialRosser
import ImbalancedChen.CurrentChenInitialSource
import MathlibNt.SieveTheory.Arithmetic.LiuLogScaleAbsorption

/-!
# Paid ordinary-BV remainder for the actual initial Rosser sieve

The active physical moduli of the same lower coefficient lie below its
literal real level. A single ordinary-BV logarithmic loss controls them
uniformly, and the complete centre-prime cost is sublinear. The resulting
sifted-count lower bound contains no distribution or density premise.
Its remaining inputs are the displayed finite covering and physical-level
inequalities; the analytic main term is the actual Rosser density.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

def currentChenInitialRosserActive (N cap : ℕ) (z L : ℝ) : Finset ℕ := by
  classical
  exact (actualSmallRosserSupport N cap z).filter
    (fun d => actualSmallRosserMinus N cap z L d ≠ 0)

theorem currentChenInitialRosserActive_subset
    (N cap Q : ℕ) (z L : ℝ) (hLQ : L ≤ (Q : ℝ) + 1) :
    currentChenInitialRosserActive N cap z L ⊆ chenInitialPrimitiveModuli N Q := by
  classical
  intro d hd
  obtain ⟨hs, ha⟩ := Finset.mem_filter.mp hd
  have hp := Nat.pos_of_mem_divisors hs
  have hl := (actualSmallRosserMinus_active ha).2.1
  have hlt : d < Q + 1 := by exact_mod_cast (hl.trans_le hLQ)
  exact mem_chenInitialPrimitiveModuli.mpr
    ⟨by omega, by omega, actualSmallRosserSupport_coprime_target N cap z hs⟩

/-- Inactive moduli contribute exactly zero for every tested function. -/
theorem currentChen_initialRosser_sum_eq_active
    (N cap : ℕ) (z L : ℝ) (f : ℕ → ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d * f d) =
      ∑ d ∈ currentChenInitialRosserActive N cap z L,
        actualSmallRosserMinus N cap z L d * f d := by
  classical
  simp only [currentChenInitialRosserActive, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : actualSmallRosserMinus N cap z L d = 0 <;> simp [h]

theorem currentChen_initialRosser_centre_le_cost (N cap : ℕ) (z L : ℝ) :
    |∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d * chenCentrePrimeAPCount N N d| ≤
      chenInitialCorrectionCost N (currentChenInitialRosserActive N cap z L) := by
  rw [currentChen_initialRosser_sum_eq_active]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg N N d)]
  calc
    _ ≤ chenCentrePrimeAPCount N N d := by
      have h := mul_le_mul_of_nonneg_right (actualSmallRosserMinus_abs_le_one N cap z L d)
        (chenCentrePrimeAPCount_nonneg N N d)
      simpa only [one_mul] using h
    _ ≤ _ := le_add_of_nonneg_left
      (div_nonneg (add_nonneg (chenPrimeDivisorCount_nonneg N N)
        (chenPrimeDivisorCount_nonneg N d)) (Nat.cast_nonneg _))

/-- Ordinary BV pays the entire real initial-source remainder. The
threshold precedes every cutoff, enumeration cap and actual lower level.
It asserts no extension beyond the displayed physical BV modulus cap. -/
theorem eventually_currentChen_initialRosser_density_lower :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
        ∀ cap : ℕ, ∀ z L : ℝ,
          z ≤ (cap : ℝ) → 1 < L → z ≤ L → L ≤ (Q : ℝ) + 1 →
          trueLogarithmicIntegral N * actualSmallRosserMinusDensity N cap z L -
            epsilon * singularNormalization N ≤
              ((chenSiftedPrimeSource N z).card : ℝ) := by
  obtain ⟨B, hB, C, _hC, hBV⟩ :=
    part3_abs_sum_mul_primeAPError_log_saving 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro epsilon hepsilon
  filter_upwards [hBV, eventually_one_le_nat_log, eventually_ge_atTop (2 : ℕ),
    MathlibNt.SieveTheory.LiuWeight.eventually_inverse_log_remainder_le_liuSingularSeries
      C (epsilon / 2) (half_pos hepsilon),
    eventually_powerLog_le_singularNormalization (17 / Real.log 2) (1 / 2) 2
      (by norm_num) (epsilon / 2) (half_pos hepsilon)]
    with N hBVN hlog hN hAPbudget hCentreBudget
  intro Q hQ cap z L hzcap hL hzL hLQ
  let S := currentChenInitialRosserActive N cap z L
  have hS := currentChenInitialRosserActive_subset N cap Q z L hLQ
  have hSI : S ⊆ Finset.Icc 1 Q :=
    hS.trans (chenInitialPrimitiveModuli_subset N Q)
  have hAP : |∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d * part3PrimeAPError N N d| ≤
        (epsilon / 2) * singularNormalization N := by
    rw [currentChen_initialRosser_sum_eq_active]
    have hdist := hBVN Q hQ S hSI N le_rfl (fun _ => N)
      (fun d hd => (mem_chenInitialPrimitiveModuli.mp (hS hd)).2.2.symm)
      (actualSmallRosserMinus N cap z L)
      (fun d _ => actualSmallRosserMinus_abs_le_one N cap z L d)
    rw [Real.rpow_ofNat] at hdist
    rw [← currentChen_singularSeries_eq_liuSingularSeries N] at hAPbudget
    exact hdist.trans (by
      simpa only [singularNormalization, mul_div_assoc, mul_assoc] using hAPbudget)
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hden : 1 ≤ Real.log (N : ℝ) ^ B := Real.one_le_rpow hlog hB
    have hfloor : (panModulusCutoff N B : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B := by
      unfold panModulusCutoff
      exact Nat.floor_le (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        (zero_le_one.trans hden))
    calc
      _ ≤ (panModulusCutoff N B : ℝ) := by exact_mod_cast hQ
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B := hfloor
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        div_le_self (Real.rpow_nonneg (Nat.cast_nonneg N) _) hden
      _ = _ := (Real.sqrt_eq_rpow _).symm
  have hCentre : |∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserMinus N cap z L d * chenCentrePrimeAPCount N N d| ≤
        (epsilon / 2) * singularNormalization N :=
    (currentChen_initialRosser_centre_le_cost N cap z L).trans
      ((chenInitialCorrectionCost_le_sqrt_log_sq (by omega) hlog hQsqrt S hSI).trans
        hCentreBudget)
  have hfinite := currentChen_initial_actualRosser_density_lower N cap z L hzcap hL hzL
  have hAPlo := (abs_le.mp hAP).1
  have hCentreHi := (abs_le.mp hCentre).2
  nlinarith only [hfinite, hAPlo, hCentreHi]

end

end ImbalancedChen
