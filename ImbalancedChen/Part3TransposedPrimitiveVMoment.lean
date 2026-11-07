import ImbalancedChen.Part3TransposedPrimitiveV
import ImbalancedChen.Part3TransposedPrimitiveUMoment

/-!
# Divisor moment payment for the actual transposed V error

The actual complex mixed coefficient has one original-alpha coprime mass,
and the actual progression error has one coprime mass of alpha norms.
Together they cost at most 4 U squared. The unweighted gamma sum costs
cap times log(cap) squared, and its tau/totient weighted sum costs twelve
logarithms. Thus the actual V error costs U squared times cap and fourteen
logarithms. The original beta L2 factor is then paid by its proved moment.

Every displayed envelope is derived from the actual full finite sum.
No coefficient, residual-error, or logarithmic budget is assumed.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open TransposedZeroCovariance TransposedPrimitiveU TransposedPrimitiveV
open TransposedPrimitiveUMoment

namespace TransposedPrimitiveVMoment

theorem coprimeNormMass_le_twice_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (q : ℕ) :
    coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q ≤ 2 * d.U := by
  unfold coprimeMass
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n.Coprime q
      · rw [if_pos hn]
      · rw [if_neg hn]
        exact norm_nonneg _
    _ ≤ _ := alpha_l1_le_twice_U hd

theorem actualV_finite_envelope_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
      ‖mixedPairCoefficient d q r‖ *
        coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
          (r.divisors.card : ℝ)) ≤
      4 * d.U ^ 2 * d.physicalFactorCap *
        (1 + Real.log d.physicalFactorCap) ^ 14 := by
  have hU : 0 ≤ d.U := by linarith [hd.1]
  have hcap : 0 ≤ d.physicalFactorCap := zero_le_one.trans (d.one_le_physicalFactorCap hd)
  have hmass (q : ℕ) :
      0 ≤ coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q := by
    unfold coprimeMass
    apply Finset.sum_nonneg
    intro n _
    by_cases hn : n.Coprime q
    · rw [if_pos hn]
      exact norm_nonneg _
    · rw [if_neg hn]
  let w : ℕ → ℝ := fun r ↦
    ‖d.groupedFactorGamma r‖ * (r.divisors.card : ℝ) / (r.totient : ℝ)
  have hw (r : ℕ) : 0 ≤ w r := by dsimp [w]; positivity
  have hpoint (q r : ℕ) :
      ‖mixedPairCoefficient d q r‖ *
          coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
            (r.divisors.card : ℝ) ≤
        4 * d.U ^ 2 * (‖d.groupedFactorGamma q‖ * w r) := by
    have hc : ‖mixedPairCoefficient d q r‖ ≤
        ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ *
          (2 * d.U) / (r.totient : ℝ) := by
      simp only [mixedPairCoefficient, norm_div, norm_mul, norm_star,
        Complex.norm_natCast]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (coprimeMass_norm_le_twice_U hd r) (by positivity)
    calc
      _ ≤ (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ *
            (2 * d.U) / (r.totient : ℝ)) * (2 * d.U) *
              (r.divisors.card : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hc (coprimeNormMass_le_twice_U hd q) (hmass q) (by positivity))
          (Nat.cast_nonneg _)
      _ = _ := by dsimp [w]; ring
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        4 * d.U ^ 2 * (‖d.groupedFactorGamma q‖ * w r) :=
      Finset.sum_le_sum (fun q _ ↦ Finset.sum_le_sum (fun r _ ↦ hpoint q r))
    _ = 4 * d.U ^ 2 *
        ((∑ q ∈ d.physicalFactorModuli, ‖d.groupedFactorGamma q‖) *
          ∑ r ∈ d.physicalFactorModuli, w r) := by
      rw [Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
    _ ≤ 4 * d.U ^ 2 *
        ((d.physicalFactorCap * (1 + Real.log d.physicalFactorCap) ^ 2) *
          (1 + Real.log d.physicalFactorCap) ^ 12) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (sum_gamma_norm_le hd) (sum_gamma_tau_div_totient_le hd)
        (Finset.sum_nonneg (fun r _ ↦ hw r)) (by positivity)
    _ = _ := by
      rw [show 14 = 2 + 12 from rfl, pow_add]
      ring

/-- The honest global V error retains U squared and one modulus cap. -/
theorem actualV_sub_primitive_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
        d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
        C * d.U ^ 2 * d.physicalFactorCap *
          (1 + Real.log d.physicalFactorCap) ^ 14 := by
  obtain ⟨C, hC, hbound⟩ := actualV_sub_primitive_finite_bound
  refine ⟨4 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  calc
    _ ≤ C * ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        ‖mixedPairCoefficient d q r‖ *
          coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
            (r.divisors.card : ℝ) := hbound B sigma kappa c0 d hd
    _ ≤ C * (4 * d.U ^ 2 * d.physicalFactorCap *
        (1 + Real.log d.physicalFactorCap) ^ 14) :=
      mul_le_mul_of_nonneg_left (actualV_finite_envelope_le hd) hC.le
    _ = _ := by ring

/-- The full original beta divisor-square moment multiplies the actual V
error, with the true U squared and one modulus cap still visible. -/
theorem actual_betaL2_mul_V_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
        C * d.V * d.U ^ 2 * d.physicalFactorCap *
          (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
            (1 + Real.log d.physicalFactorCap) ^ 14 := by
  obtain ⟨C, hC, hbound⟩ := actualV_sub_primitive_bound
  refine ⟨2 * C, by positivity, fun B sigma kappa c0 d hd ↦ ?_⟩
  have hlogV : 0 ≤ 1 + Real.log (2 * d.V) := by
    have := Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])
    linarith
  calc
    _ ≤ (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (C * d.U ^ 2 * d.physicalFactorCap *
          (1 + Real.log d.physicalFactorCap) ^ 14) :=
      mul_le_mul (mediumAdmissible_beta_norm_sq_sum_le hd)
        (hbound B sigma kappa c0 d hd) (norm_nonneg _)
          (by have := hd.2.1; positivity)
    _ = _ := by ring

end TransposedPrimitiveVMoment

end

end ImbalancedChen.Part3
