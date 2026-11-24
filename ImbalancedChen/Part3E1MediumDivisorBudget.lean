import ImbalancedChen.Part3E1MediumCaps
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-! The uniform divisor budget for the trimmed medium E1 coefficients. -/

namespace ImbalancedChen.Part3

open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry (fouvryTau_two)

/-- The divisor count budget is uniform over the split divisor and rough product
in every admissible medium atom. -/
theorem exists_medium_e1_trim_divisorBudget {σ : ℝ} (hσ : 0 < σ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ (B : ℕ) (κ c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B σ κ c0 d → 1 ≤ d.scale →
      ∀ (k : ℕ) (R : ℝ), 0 < k → 1 ≤ R → (k : ℝ) * R ≤ 4 * d.Q2 * d.Q3 →
      ∀ r ∈ factorCarrier R,
        ((k * r).divisors.card : ℝ) ≤ B₀ * d.scale ^ (σ / 10) := by
  have hε : 0 < σ / 10 := by positivity
  obtain ⟨C, hC, hτ⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) hε
  refine ⟨C * (8 : ℝ) ^ (σ / 10), by positivity, ?_⟩
  intro B κ c0 d hd hX k R hk hR hprod r hr
  have hrBounds := e1FactorCarrier_bounds (zero_le_one.trans hR) hr
  have hr0 : 0 < r := by exact_mod_cast (zero_lt_one.trans_le (hR.trans hrBounds.1))
  have hkr0 := Nat.mul_pos hk hr0
  have hX0 := zero_lt_one.trans_le hX
  have hlength := (medium_e1_factorLengths_le_scale hσ.le hX hd).2
  have hkr : ((k * r : ℕ) : ℝ) ≤ 8 * d.scale := by
    push_cast
    calc
      _ ≤ 2 * ((k : ℝ) * R) := by
        calc
          _ ≤ (k : ℝ) * (2 * R) := mul_le_mul_of_nonneg_left hrBounds.2 (by positivity)
          _ = _ := by ring
      _ ≤ 8 * (d.Q2 * d.Q3) := by linarith only [hprod]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlength (by norm_num)
  rw [← fouvryTau_two]
  calc
    _ ≤ C * ((k * r : ℕ) : ℝ) ^ (σ / 10) := hτ (k * r) hkr0
    _ ≤ C * (8 * d.scale) ^ (σ / 10) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) hkr hε.le) hC.le
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hX0.le, mul_assoc]

end ImbalancedChen.Part3
