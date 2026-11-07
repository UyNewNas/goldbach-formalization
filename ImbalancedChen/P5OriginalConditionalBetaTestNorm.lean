import ImbalancedChen.P5OriginalConditionalBetaNorm

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Weighted finite test bounds for the literal conditional native coefficient.
These are Cauchy--Schwarz primitives, with the original d-dependent small
energy and the actual full modulus e*d. They supply no AP distribution
estimate for the tested function and no independent beta decomposition.
-/

namespace ImbalancedChen.P5Z.OriginalConditionalBetaTestNorm

noncomputable section
open scoped BigOperators
open Classical
open OriginalOrdinaryBetaRegroup OriginalConditionalBetaNorm

/-- The test energy retains the same conditional coefficient and small
reciprocal-totient measure as its paired norm. -/
def energy (N cap : ℕ) (w Z L : ℝ) (d : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ e ∈ actualSmallRosserSupport N cap w,
    |coefficient N cap Z L d e| * (F e)^2 / (Nat.totient e : ℝ)

theorem energy_nonneg (N cap : ℕ) (w Z L : ℝ) (d : ℕ) (F : ℕ → ℝ) :
    0 ≤ energy N cap w Z L d F := by
  apply Finset.sum_nonneg
  intro e he
  exact div_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)

/-- Finite weighted Cauchy--Schwarz for the ACTUAL conditional native row.
There is no sign restriction on the test and no analytic premise. -/
theorem signed_test_sq_le_norm_energy (N cap : ℕ) (w Z L : ℝ) (d : ℕ) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      coefficient N cap Z L d e * F e / (Nat.totient e : ℝ))^2 ≤
      l1Phi N cap w Z L d * energy N cap w Z L d F := by
  unfold l1Phi energy
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro e he
    exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  · intro e he
    exact div_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg _)
  · intro e he
    apply le_of_eq
    simp only [div_eq_mul_inv]
    calc
      (coefficient N cap Z L d e * F e * (Nat.totient e : ℝ)⁻¹)^2 =
          |coefficient N cap Z L d e|^2 * (F e)^2 * ((Nat.totient e : ℝ)⁻¹)^2 := by
        rw [sq_abs]
        ring
      _ = _ := by ring

/-- The Euler product is an explicit coefficient cost for arbitrary signed
tests. The remaining energy is a genuine test-dependent obligation. -/
theorem signed_test_sq_le_euler_energy (N cap : ℕ) (w Z L : ℝ) (d : ℕ) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      coefficient N cap Z L d e * F e / (Nat.totient e : ℝ))^2 ≤
      (∏ p ∈ actualSmallPrimeFinset N cap w, (1 + 1 / ((p : ℝ) - 1))) *
        energy N cap w Z L d F :=
  (signed_test_sq_le_norm_energy N cap w Z L d F).trans
    (mul_le_mul_of_nonneg_right (l1Phi_le_eulerProduct N cap w Z L d)
      (energy_nonneg N cap w Z L d F))

/-- Alternatively the same signed test can pay the literal residual level
L/d. This bound remains valid if the conditional row is empty. -/
theorem signed_test_sq_le_residual_energy {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      coefficient N cap Z L d e * F e / (Nat.totient e : ℝ))^2 ≤
      (4 * (1 + Real.log (max 1 (Nat.ceil (L/(d:ℝ)) : ℝ)) )) *
        energy N cap w Z L d F :=
  (signed_test_sq_le_norm_energy N cap w Z L d F).trans
    (mul_le_mul_of_nonneg_right (l1Phi_le_residual_log hd)
      (energy_nonneg N cap w Z L d F))

/-- Peeling is licensed by the actual cutoff-separated carriers, including
all zero native coefficients. No beta independence is used. -/
theorem full_modulus_signed_test_eq {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      coefficient N cap Z L d e * F e / (Nat.totient (e*d) : ℝ)) =
      (∑ e ∈ actualSmallRosserSupport N cap w,
        coefficient N cap Z L d e * F e / (Nat.totient e : ℝ)) /
          (Nat.totient d : ℝ) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) (roughSupport_rough hd)
  rw [Nat.totient_mul hcop, Nat.cast_mul, div_mul_eq_div_div]

/-- Quantitative signed test bound on the actual FULL native modulus.
The squared rough reciprocal-totient factor cannot be silently discarded. -/
theorem full_modulus_signed_test_sq_le {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) (F : ℕ → ℝ) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      coefficient N cap Z L d e * F e / (Nat.totient (e*d) : ℝ))^2 ≤
      ((∏ p ∈ actualSmallPrimeFinset N cap w, (1 + 1 / ((p : ℝ) - 1))) *
        energy N cap w Z L d F) / (Nat.totient d : ℝ)^2 := by
  rw [full_modulus_signed_test_eq hd, div_pow]
  exact div_le_div_of_nonneg_right (signed_test_sq_le_euler_energy N cap w Z L d F)
    (sq_nonneg _)

end
end ImbalancedChen.P5Z.OriginalConditionalBetaTestNorm
