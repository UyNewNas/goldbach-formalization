import ImbalancedChen.Part3RoughSlotDirichletSeries

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual finite small-prime correction bounds, uniform in the character
level and imaginary part, including principal characters and p|q. Only
Re(s)>=1 is used for the FINITE factors. This is not nonvanishing of the
full L-function on the boundary and not a rough-slot SW estimate.
-/

namespace ImbalancedChen.Part3.RoughFiniteEulerBounds20261026b
noncomputable section
open Classical Finset Complex
open scoped BigOperators
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b

def plusEnvelope (z : ℝ) : ℝ := ∏ p ∈ smallPrimes z, (1+1/(p : ℝ))
def inverseEnvelope (z : ℝ) : ℝ := ∏ p ∈ smallPrimes z, (1-1/(p : ℝ))⁻¹

theorem prime_twist_norm_le_inv {q p : ℕ} (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖chi p*(p : ℂ)^(-s)‖ ≤ 1/(p : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  calc
    _ ≤ 1*‖(p : ℂ)^(-s)‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (chi.norm_le_one p) (norm_nonneg _)
    _ = (p : ℝ)^(-s.re) := by
      rw [one_mul,Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
    _ ≤ (p : ℝ)^(-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = _ := by simp

theorem prime_factor_bounds {q p : ℕ} (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    (1-chi p*(p : ℂ)^(-s)) ≠ 0 ∧
      1-1/(p : ℝ) ≤ ‖1-chi p*(p : ℂ)^(-s)‖ ∧
      ‖1-chi p*(p : ℂ)^(-s)‖ ≤ 1+1/(p : ℝ) ∧
      ‖(1-chi p*(p : ℂ)^(-s))⁻¹‖ ≤ (1-1/(p : ℝ))⁻¹ := by
  have htwist := prime_twist_norm_le_inv chi hp hs
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hrec : 1/(p : ℝ) ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) hp2
  have hdelta : 0 < 1-1/(p : ℝ) := by linarith
  have hlower : 1-1/(p : ℝ) ≤ ‖1-chi p*(p : ℂ)^(-s)‖ := by
    have ht := norm_add_le (1-chi p*(p : ℂ)^(-s)) (chi p*(p : ℂ)^(-s))
    have he : (1-chi p*(p : ℂ)^(-s))+(chi p*(p : ℂ)^(-s)) = 1 := by ring
    rw [he,norm_one] at ht
    linarith
  have hnonzero : (1-chi p*(p : ℂ)^(-s)) ≠ 0 :=
    norm_pos_iff.mp (hdelta.trans_le hlower)
  refine ⟨hnonzero,hlower,?_,?_⟩
  · exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_left htwist 1)
  · rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hdelta hlower

/-- Magnitude and reciprocal bounds of the actual finite correction.
The product remains the literal p<=z product; no cutoff cap is enlarged. -/
theorem finiteCorrection_bounds {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z : ℝ) {s : ℂ} (hs : 1 ≤ s.re) :
    finiteCorrection chi z s ≠ 0 ∧
      ‖finiteCorrection chi z s‖ ≤ plusEnvelope z ∧
      ‖(finiteCorrection chi z s)⁻¹‖ ≤ inverseEnvelope z := by
  have hn : finiteCorrection chi z s ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact (prime_factor_bounds chi (smallPrimes_prime hp) hs).1
  refine ⟨hn,?_,?_⟩
  · rw [finiteCorrection,norm_prod]
    apply Finset.prod_le_prod (fun p hp => norm_nonneg _)
    intro p hp
    exact (prime_factor_bounds chi (smallPrimes_prime hp) hs).2.2.1
  · rw [finiteCorrection,← Finset.prod_inv_distrib,norm_prod]
    apply Finset.prod_le_prod (fun p hp => norm_nonneg _)
    intro p hp
    exact (prime_factor_bounds chi (smallPrimes_prime hp) hs).2.2.2

end
end ImbalancedChen.Part3.RoughFiniteEulerBounds20261026b
