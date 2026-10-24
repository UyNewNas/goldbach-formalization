import ImbalancedChen.HistoricalPrefixCertificate
import ImbalancedChen.ActualHistoricalFifthSavingIntegral
import ImbalancedChen.ActualPrimePresieveSplit
import ImbalancedChen.PhysicalUpperWeightBridge

/-!
The finite historical selector and its fixed physical rough coefficient.
This keeps the policy, its reciprocal-totient density and its pointwise
divisor evaluation tied to exactly one support. The original levelCheck
supplies the two comparisons in the signed telescoping identity.

This file does not identify arbitrary table data with the adopted
manuscript table, attach the small-prime sieve, or supply a mean estimate.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators

namespace HistoricalPrefixCapData

def p1FifthRetainOdd (D : HistoricalPrefixCapData) (N : ℕ) : List ℕ → Bool :=
  D.upperFifthPolicy (N : ℝ) false

def p1FifthRoughSupport (D : HistoricalPrefixCapData) (N cap : ℕ) (z : ℝ) :
    Finset ℕ :=
  fixedRoughSupport (D.p1FifthRetainOdd N) N cap 0 z

def p1FifthRoughCoefficient (D : HistoricalPrefixCapData) (N cap : ℕ) (z : ℝ) :
    ℕ → ℝ :=
  fixedRoughCoefficient (D.p1FifthRetainOdd N) N cap 0 z

theorem p1FifthRoughDensity_eq_polynomial (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) :
    physicalDensitySum (D.p1FifthRoughSupport N cap z)
        (D.p1FifthRoughCoefficient N cap z) =
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap 0 z) := by
  have h := oddFirstExitRetainedPolynomial_eq_fixedRoughDensity
    (D.p1FifthRetainOdd N) N cap 0 z
  change _ = reciprocalTotientDensity (D.p1FifthRoughSupport N cap z)
    (D.p1FifthRoughCoefficient N cap z) at h
  have hpolicy : oddFirstExitPolicy (D.p1FifthRetainOdd N) =
      D.upperFifthPolicy (N : ℝ) :=
    (D.upperFifthPolicy_eq_oddFirstExitPolicy (N : ℝ)).symm
  simpa only [oddFirstExitRetainedPolynomial, hpolicy,
    physicalDensitySum, reciprocalTotientDensity] using h.symm

/-- This is an exact signed equality. Neither saving is assumed nonnegative. -/
theorem p1FifthRoughDensity_eq_third_sub_savings
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    physicalDensitySum (D.p1FifthRoughSupport N cap z)
        (D.p1FifthRoughCoefficient N cap z) =
      firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N cap 0 z) -
        (actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z) := by
  rw [D.p1FifthRoughDensity_eq_polynomial]
  have h := D.upperThirdToFifthSaving_eq hab hcheck N cap hN z
  linarith

/-- The same support is chosen before the integer is evaluated. -/
theorem p1FifthRoughDivisorSum_eq_polynomial (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) (n : ℤ) :
    supportedDivisorSum (D.p1FifthRoughSupport N cap z)
        (D.p1FifthRoughCoefficient N cap z) n.natAbs =
      firstExitRetainedPolynomial (D.upperFifthPolicy (N : ℝ))
        (integerDivisorIndicator n) [] true 1 (roughPrimeUniverse N cap 0 z) := by
  have h := oddFirstExitRetainedPolynomial_eq_fixedRoughDivisorSum
    (D.p1FifthRetainOdd N) N cap 0 z n
  have hpolicy : oddFirstExitPolicy (D.p1FifthRetainOdd N) =
      D.upperFifthPolicy (N : ℝ) :=
    (D.upperFifthPolicy_eq_oddFirstExitPolicy (N : ℝ)).symm
  simpa only [p1FifthRoughSupport, p1FifthRoughCoefficient,
    oddFirstExitRetainedPolynomial, hpolicy] using h.symm

theorem p1FifthRoughDivisorSum_majorant (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    (if ∀ p : ℕ, (p.Prime ∧ ¬p ∣ N ∧ 0 ≤ (p : ℝ) ∧ (p : ℝ) < z) →
      ¬(p : ℤ) ∣ n then (1 : ℝ) else 0) ≤
      supportedDivisorSum (D.p1FifthRoughSupport N cap z)
        (D.p1FifthRoughCoefficient N cap z) n.natAbs := by
  exact roughIndicator_le_fixedRoughDivisorSum
    (D.p1FifthRetainOdd N) N cap 0 z hzcap n

theorem p1FifthRoughCoefficient_abs_le_one (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) (d : ℕ) :
    |D.p1FifthRoughCoefficient N cap z d| ≤ 1 := by
  exact fixedRoughCoefficient_abs_le_one (D.p1FifthRetainOdd N) N cap 0 z d

theorem p1FifthRoughSupport_squarefree (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) {d : ℕ} (hd : d ∈ D.p1FifthRoughSupport N cap z) :
    Squarefree d := by
  exact fixedRoughSupport_squarefree (D.p1FifthRetainOdd N) N cap 0 z hd

theorem p1FifthRoughSupport_coprime_target (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) {d : ℕ} (hd : d ∈ D.p1FifthRoughSupport N cap z) :
    d.Coprime N := by
  exact fixedRoughSupport_coprime_target (D.p1FifthRetainOdd N) N cap 0 z hd

/-- Both displayed divisor-sum APIs evaluate the identical fixed coefficient. -/
theorem p1FifthRough_supported_eq_physical (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) (n : ℕ) :
    supportedDivisorSum (D.p1FifthRoughSupport N cap z)
        (D.p1FifthRoughCoefficient N cap z) n =
      physicalDivisorSum (D.p1FifthRoughSupport N cap z)
        (D.p1FifthRoughCoefficient N cap z) n := by
  classical
  simp only [supportedDivisorSum, physicalDivisorSum, Finset.sum_filter]

/-- Exact counting-source algebra, retaining both signed error terms.
It does not bound the coprime correction or the distribution error. -/
theorem p1FifthRough_halfProductSource_eq_third_sub_savings_add_errors
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hcheck : D.levelCheck = true) (num den N cap : ℕ)
    (hN : 1 < (N : ℝ)) (z T : ℝ) :
    (∑ m ∈ halfProductSource num den N T,
      supportedDivisorSum (D.p1FifthRoughSupport N cap z)
        (D.p1FifthRoughCoefficient N cap z) (N - m)) =
      ((halfProductSource num den N T).card : ℝ) *
        (firstExitRetainedPolynomial (D.upperThirdPolicy (N : ℝ))
          (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N cap 0 z) -
        (actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z)) +
      physicalCoprimeCorrection num den N T
        (D.p1FifthRoughSupport N cap z) (D.p1FifthRoughCoefficient N cap z) +
      physicalDistributionError num den N T
        (D.p1FifthRoughSupport N cap z) (D.p1FifthRoughCoefficient N cap z) := by
  calc
    _ = ∑ m ∈ halfProductSource num den N T,
        physicalDivisorSum (D.p1FifthRoughSupport N cap z)
          (D.p1FifthRoughCoefficient N cap z) (N - m) := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact D.p1FifthRough_supported_eq_physical N cap z (N - m)
    _ = _ := by
      rw [sum_physicalDivisorSum_halfProductSource,
        sum_rho_mul_halfProductCongruenceMass_eq,
        D.p1FifthRoughDensity_eq_third_sub_savings hab hcheck N cap hN z]

end HistoricalPrefixCapData
end
end ImbalancedChen
