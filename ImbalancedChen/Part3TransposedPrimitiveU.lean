import ImbalancedChen.Part3TransposedZeroCovariance
import ImbalancedChen.Part3SmoothCoprimeError

/-!
# The literal transposed primitive energy minus its actual zero main term

Every coefficient is from the original atom. The exact finite identities
first retain every factor label and every original alpha integer, and only
then use the already proved exact grouping by physical modulus. The smooth
scale is original V and the mass is the local Fourier-zero cutoffMass.

The final bound in this leaf has the explicit finite coefficient envelope.
It is a proved consequence of the uniform coprime progression error; that
envelope is not an assumption. Its divisor moment payment is separate.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open TransposedZeroCovariance

namespace TransposedPrimitiveU

theorem alpha_l1_le_twice_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖) ≤ 2 * d.U := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  have hsub : d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
    intro n hn
    obtain ⟨hn, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hceil : 1 ≤ Nat.ceil d.U := by exact_mod_cast hd.1.trans (Nat.le_ceil d.U)
    exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  calc
    _ ≤ ∑ _n ∈ d.alphaCarrier, (1 : ℝ) := Finset.sum_le_sum hAlpha
    _ = (d.alphaCarrier.card : ℝ) := by simp
    _ ≤ (Nat.floor (2 * d.U) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := Nat.floor_le (by linarith [hd.1])

theorem coprimeMass_norm_le_twice_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (q : ℕ) :
    ‖coprimeMass d.alphaCarrier d.alpha q‖ ≤ 2 * d.U := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier, ‖d.alpha n‖ := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n.Coprime q <;> simp [hn]
    _ ≤ _ := alpha_l1_le_twice_U hd

/-- Exact grouping of the literal principal row, including the original
interval restriction inside the paired coefficient. No admissibility is used. -/
theorem actual_principalRow_eq_grouped (d : MediumAtom) (m : ℕ) :
    d.transposedAtom.complexPrincipalRow m =
      ∑ q ∈ d.physicalFactorModuli,
        d.groupedFactorGamma q *
          (if m.Coprime q then coprimeMass d.alphaCarrier d.alpha q else 0) /
            (q.totient : ℂ) := by
  have hmass (q : ℕ) :
      (∑ n ∈ d.transposedAtom.betaCarrier, d.transposedAtom.beta n *
        (if (m * n).Coprime q then (1 : ℂ) else 0)) =
      if m.Coprime q then coprimeMass d.alphaCarrier d.alpha q else 0 := by
    rw [d.sum_transposedBeta_mul]
    by_cases hm : m.Coprime q
    · simp only [Nat.coprime_mul_iff_left, hm, true_and, if_true]
      unfold coprimeMass
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : n.Coprime q <;> simp [hn]
    · simp only [Nat.coprime_mul_iff_left, hm, false_and, if_false,
        mul_zero, Finset.sum_const_zero]
  calc
    _ = ∑ a ∈ d.complexFactorLabels, d.complexFactorGamma a *
        ((∑ n ∈ d.transposedAtom.betaCarrier, d.transposedAtom.beta n *
          (if (m * n).Coprime (complexFactorModulus a) then (1 : ℂ) else 0)) /
            ((complexFactorModulus a).totient : ℂ)) := by
      unfold MediumAtom.complexPrincipalRow MediumAtom.complexRowLabels
      simp only [Finset.sum_product]
      change (∑ a ∈ d.complexFactorLabels, ∑ n ∈ d.transposedAtom.betaCarrier,
        d.complexFactorGamma a * d.transposedAtom.beta n *
          (if (m * n).Coprime (complexFactorModulus a) then (1 : ℂ) else 0) /
            ((complexFactorModulus a).totient : ℂ)) = _
      simp only [Finset.mul_sum, Finset.sum_div, mul_div_assoc, mul_assoc]
    _ = ∑ q ∈ d.physicalFactorModuli, d.groupedFactorGamma q *
        ((∑ n ∈ d.transposedAtom.betaCarrier, d.transposedAtom.beta n *
          (if (m * n).Coprime q then (1 : ℂ) else 0)) / (q.totient : ℂ)) :=
      d.sum_factorLabels_eq_grouped _
    _ = _ := by simp only [hmass, mul_div_assoc]

def primitivePairCoefficient (d : MediumAtom) (q r : ℕ) : ℂ :=
  d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
    coprimeMass d.alphaCarrier d.alpha q * star (coprimeMass d.alphaCarrier d.alpha r) /
      ((q.totient : ℂ) * (r.totient : ℂ))

theorem actual_principalRow_norm_sq_eq (d : MediumAtom) (m : ℕ) :
    ((‖d.transposedAtom.complexPrincipalRow m‖ ^ 2 : ℝ) : ℂ) =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        primitivePairCoefficient d q r *
          (if m.Coprime (q * r) then (1 : ℂ) else 0) := by
  rw [actual_principalRow_eq_grouped, complex_norm_sq_sum_eq_double_star]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  by_cases hq : m.Coprime q <;> by_cases hr : m.Coprime r
  all_goals
    simp only [Nat.coprime_mul_iff_right, hq, hr, and_self, true_and, false_and,
      and_false, if_true, if_false, mul_zero, zero_div, star_zero, zero_mul,
      star_div₀, star_mul, star_natCast, primitivePairCoefficient]
    <;> simp only [div_eq_mul_inv, mul_inv_rev]
    <;> ring

/-- Exact U expansion on the actual common finite carrier and smoothing. -/
theorem actualU_eq_coprime_sum (d : MediumAtom) :
    (d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight : ℂ) =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        primitivePairCoefficient d q r *
          ((∑ m ∈ d.transposedAtom.commonSmoothCarrier,
            if m.Coprime (q * r) then d.transposedAtom.commonSmoothWeight m else 0 : ℝ) : ℂ) := by
  unfold MediumAtom.complexDispersionU
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, actual_principalRow_norm_sq_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : m.Coprime (q * r)
  · simp only [hm, if_true, mul_one]
    ring
  · simp only [hm, if_false, mul_zero, Complex.ofReal_zero, zero_mul]

theorem primitiveZeroMain_eq_grouped (d : MediumAtom) :
    primitiveZeroMain d =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        primitivePairCoefficient d q r *
          (((d.V * CommonSmoothCutoff.cutoffMass) * ((q * r).totient : ℝ) /
            (q * r : ℕ) : ℝ) : ℂ) := by
  have hgroup := factor_pair_sum_eq_grouped d (fun q r ↦
    coprimeMass d.alphaCarrier d.alpha q * star (coprimeMass d.alphaCarrier d.alpha r) *
      (((q * r).totient : ℂ) /
        ((q.totient : ℂ) * (r.totient : ℂ) * (q * r : ℕ))))
  have halign : primitiveZeroMain d =
      ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) *
        ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
          d.complexFactorGamma a * star (d.complexFactorGamma b) *
            (coprimeMass d.alphaCarrier d.alpha (complexFactorModulus a) *
              star (coprimeMass d.alphaCarrier d.alpha (complexFactorModulus b)) *
                (((complexFactorModulus a * complexFactorModulus b).totient : ℂ) /
                  (((complexFactorModulus a).totient : ℂ) *
                    ((complexFactorModulus b).totient : ℂ) *
                      (complexFactorModulus a * complexFactorModulus b : ℕ)))) := by
    unfold primitiveZeroMain
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [halign, hgroup]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  unfold primitivePairCoefficient
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual discrepancy is a finite sum of coprime counting errors.
No equality between the literal U term and its zero main term is presumed. -/
theorem actualU_sub_primitive_eq (d : MediumAtom) :
    (d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        primitivePairCoefficient d q r *
          (((∑ m ∈ d.transposedAtom.commonSmoothCarrier,
            if m.Coprime (q * r) then d.transposedAtom.commonSmoothWeight m else 0) -
            (d.V * CommonSmoothCutoff.cutoffMass) * ((q * r).totient : ℝ) /
              (q * r : ℕ) : ℝ) : ℂ) := by
  rw [actualU_eq_coprime_sum, primitiveZeroMain_eq_grouped, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [Complex.ofReal_sub, mul_sub]

/-- A proved envelope with a universal constant, before all atoms and data. -/
theorem actualU_sub_primitive_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      ‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
        d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
          C * ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
            ‖primitivePairCoefficient d q r‖ * ((q * r).divisors.card : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := CommonSmoothCutoff.scaledDyadicCutoff_finset_coprime_uniform_error
  refine ⟨C, hC, fun B sigma kappa c0 d hd ↦ ?_⟩
  rw [actualU_sub_primitive_eq]
  have hp {q : ℕ} (hq : q ∈ d.physicalFactorModuli) : q ≠ 0 :=
    (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd hq)).1.ne'
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        C * (‖primitivePairCoefficient d q r‖ * ((q * r).divisors.card : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have he := hbound d.V (lt_of_lt_of_le zero_lt_one hd.2.1)
        d.transposedAtom.commonSmoothCarrier
        (fun m hm ↦ MediumAtom.transposedSmoothWeight_support_subset hd.2.1 hm)
        (q * r) (mul_ne_zero (hp hq) (hp hr))
      calc
        _ ≤ ‖primitivePairCoefficient d q r‖ *
            (C * ((q * r).divisors.card : ℝ)) :=
          mul_le_mul_of_nonneg_left he (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by simp only [Finset.mul_sum]

end TransposedPrimitiveU

end

end ImbalancedChen.Part3
