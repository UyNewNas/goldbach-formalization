import ImbalancedChen.Part3SmoothReciprocityLogRegularity
import ImbalancedChen.Part3SchwartzFourierL1Sobolev
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
The literal logarithmic weight has a uniform Fourier L1 bound of order four
in the phase size, in every real dimension strictly below eight. The fixed
localizer support pays the square integral of the actual normalized fourth
order operator. Every constant is chosen before the real atom parameters.
-/

namespace ImbalancedChen.Part3

noncomputable section

open MeasureTheory FourierTransform Laplacian LineDeriv
open scoped SchwartzMap FourierTransform ContDiff BigOperators
open CommonSmoothCutoff SchwartzFourierL1Sobolev

/-- The actual weight bundled using its proved smoothness and compact support. -/
def CommonSmoothCutoff.smoothReciprocityLogSchwartzWeight
    {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hQc : HasCompactSupport Q) (Z u₀ rho₀ : ℝ) :
    𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  (smoothReciprocityLogWeight_hasCompactSupport a b c Q hQc Z u₀ rho₀).toSchwartzMap
    (smoothReciprocityLogWeight_contDiff a b c Q hQ Z u₀ rho₀)

@[simp] theorem CommonSmoothCutoff.smoothReciprocityLogSchwartzWeight_apply
    {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hQc : HasCompactSupport Q) (Z u₀ rho₀ : ℝ)
    (t : EuclideanSpace ℝ (Fin d)) :
    smoothReciprocityLogSchwartzWeight a b c Q hQ hQc Z u₀ rho₀ t =
      smoothReciprocityLogWeight a b c Q Z u₀ rho₀ t := rfl

namespace SmoothReciprocityLogFourierL1Proof

private def tau : ℝ := ((2 * Real.pi) ^ 2)⁻¹

private theorem tau_nonneg : 0 ≤ tau := by unfold tau; positivity

variable {d : ℕ}

private theorem word_norm_le {n : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (m : Fin n → EuclideanSpace ℝ (Fin d))
    (hm : ∀ i, ‖m i‖ ≤ 1) (x : EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (hB : ‖iteratedFDeriv ℝ n f x‖ ≤ B) : ‖∂^{m} f x‖ ≤ B := by
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  exact ((iteratedFDeriv ℝ n f x).le_opNorm_mul_prod_of_le hm).trans
    (by simpa only [Finset.prod_const_one, mul_one] using hB)

private theorem laplacian_sq_sum
    (e : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    Δ (Δ f) = ∑ i : Fin d, ∑ j : Fin d,
      ∂_{e i} (∂_{e i} (∂_{e j} (∂_{e j} f))) := by
  rw [SchwartzMap.laplacian_eq_sum e]
  simp_rw [SchwartzMap.laplacian_eq_sum e f, lineDerivOp_sum]

private theorem laplacian_norm_le
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ) (hB : ‖iteratedFDeriv ℝ 2 f x‖ ≤ B) :
    ‖Δ f x‖ ≤ (d : ℝ) * B := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hword (i : Fin d) : ‖∂_{e i} (∂_{e i} f) x‖ ≤ B := by
    change ‖∂^{![e i, e i]} f x‖ ≤ B
    exact word_norm_le f ![e i, e i]
      (by intro k; fin_cases k <;> exact (e.norm_eq_one i).le) x B hB
  rw [SchwartzMap.laplacian_eq_sum e]
  calc
    ‖(∑ i : Fin d, ∂_{e i} (∂_{e i} f)) x‖ ≤
        ∑ i : Fin d, ‖∂_{e i} (∂_{e i} f) x‖ := by
      simpa only [sum_apply] using
        (norm_sum_le (s := Finset.univ) (f := fun i : Fin d ↦ ∂_{e i} (∂_{e i} f) x))
    _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum (fun i _ ↦ hword i)
    _ = (d : ℝ) * B := by simp

private theorem laplacian_sq_norm_le
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ) (hB : ‖iteratedFDeriv ℝ 4 f x‖ ≤ B) :
    ‖Δ (Δ f) x‖ ≤ (d : ℝ) ^ 2 * B := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hword (i j : Fin d) :
      ‖∂_{e i} (∂_{e i} (∂_{e j} (∂_{e j} f))) x‖ ≤ B := by
    change ‖∂^{![e i, e i, e j, e j]} f x‖ ≤ B
    exact word_norm_le f ![e i, e i, e j, e j]
      (by intro k; fin_cases k <;> exact (e.norm_eq_one _).le) x B hB
  rw [laplacian_sq_sum e f]
  simp only [sum_apply]
  calc
    ‖∑ i : Fin d, ∑ j : Fin d,
        (∂_{e i} (∂_{e i} (∂_{e j} (∂_{e j} f)))) x‖ ≤
        ∑ i : Fin d, ‖∑ j : Fin d,
          (∂_{e i} (∂_{e i} (∂_{e j} (∂_{e j} f)))) x‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
        ‖(∂_{e i} (∂_{e i} (∂_{e j} (∂_{e j} f)))) x‖ :=
      Finset.sum_le_sum (fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, B :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hword i j))
    _ = (d : ℝ) ^ 2 * B := by simp; ring

private theorem normalizedFourth_apply
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : EuclideanSpace ℝ (Fin d)) :
    normalizedFourth f x = (f x - tau • Δ f x) -
      tau • (Δ f x - tau • Δ (Δ f) x) := by
  have hΔ : Δ (f - tau • Δ f) = Δ f - tau • Δ (Δ f) := by
    change (laplacianCLM ℝ (EuclideanSpace ℝ (Fin d))
      𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (f - tau • Δ f) = _
    rw [map_sub, map_smul]
    rfl
  change ((f - tau • Δ f) - tau • Δ (f - tau • Δ f)) x = _
  rw [hΔ]
  rfl

private theorem normalizedFourth_norm_le
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : EuclideanSpace ℝ (Fin d))
    (B : ℝ) (hjet : ∀ j : ℕ, j ≤ 4 → ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ‖normalizedFourth f x‖ ≤ (1 + tau * d) ^ 2 * B := by
  have h₀ : ‖f x‖ ≤ B := by simpa only [norm_iteratedFDeriv_zero] using hjet 0 (by norm_num)
  have h₂ := laplacian_norm_le f x B (hjet 2 (by norm_num))
  have h₄ := laplacian_sq_norm_le f x B (hjet 4 le_rfl)
  rw [normalizedFourth_apply]
  calc
    ‖(f x - tau • Δ f x) - tau • (Δ f x - tau • Δ (Δ f) x)‖ ≤
        ‖f x‖ + tau * ‖Δ f x‖ + tau * (‖Δ f x‖ + tau * ‖Δ (Δ f) x‖) := by
      calc
        _ ≤ ‖f x - tau • Δ f x‖ + ‖tau • (Δ f x - tau • Δ (Δ f) x)‖ := norm_sub_le _ _
        _ ≤ (‖f x‖ + ‖tau • Δ f x‖) +
            ‖tau‖ * (‖Δ f x‖ + ‖tau • Δ (Δ f) x‖) := by
          rw [norm_smul]
          exact add_le_add (norm_sub_le _ _)
            (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
        _ = _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg tau_nonneg]
    _ ≤ B + tau * ((d : ℝ) * B) + tau * ((d : ℝ) * B +
        tau * ((d : ℝ) ^ 2 * B)) := by
      exact add_le_add
        (add_le_add h₀ (mul_le_mul_of_nonneg_left h₂ tau_nonneg))
        (mul_le_mul_of_nonneg_left
          (add_le_add h₂ (mul_le_mul_of_nonneg_left h₄ tau_nonneg)) tau_nonneg)
    _ = (1 + tau * d) ^ 2 * B := by ring

private theorem normalizedFourth_zero_off_support
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∉ tsupport f) : normalizedFourth f x = 0 := by
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  have hf : f x = 0 := by
    by_contra hne
    exact hx (subset_closure hne)
  have hword {n : ℕ} (m : Fin n → EuclideanSpace ℝ (Fin d)) : ∂^{m} f x = 0 := by
    by_contra hne
    exact hx (SchwartzMap.tsupport_iteratedLineDerivOp_subset m f (subset_closure hne))
  have h₂ : Δ f x = 0 := by
    rw [SchwartzMap.laplacian_eq_sum e]
    simp only [sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    exact hword ![e i, e i]
  have h₄ : Δ (Δ f) x = 0 := by
    rw [laplacian_sq_sum e f]
    simp only [sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    exact hword ![e i, e i, e j, e j]
  rw [normalizedFourth_apply, hf, h₂, h₄]
  simp

private theorem normalizedFourth_sqrt_integral_le
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (hsupport : tsupport f ⊆ K) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ x, ‖normalizedFourth f x‖ ≤ B) :
    Real.sqrt (∫ x, ‖normalizedFourth f x‖ ^ 2) ≤ B * Real.sqrt (volume.real K) := by
  have hzero (x : EuclideanSpace ℝ (Fin d)) (hx : x ∉ K) :
      ‖normalizedFourth f x‖ ^ 2 = 0 := by
    rw [normalizedFourth_zero_off_support f x (fun hf ↦ hx (hsupport hf)), norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hset := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzero
  have hint : (∫ x, ‖normalizedFourth f x‖ ^ 2) ≤ B ^ 2 * volume.real K := by
    rw [← hset]
    calc
      (∫ x in K, ‖normalizedFourth f x‖ ^ 2) ≤
          ‖∫ x in K, ‖normalizedFourth f x‖ ^ 2‖ := le_abs_self _
      _ ≤ B ^ 2 * volume.real K :=
        norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun x _ ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)
  calc
    Real.sqrt (∫ x, ‖normalizedFourth f x‖ ^ 2) ≤
        Real.sqrt (B ^ 2 * volume.real K) := Real.sqrt_le_sqrt hint
    _ = B * Real.sqrt (volume.real K) := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

end SmoothReciprocityLogFourierL1Proof

open SmoothReciprocityLogFourierL1Proof in
/-- The complete actual logarithmic weight has fourth-order Fourier L1 cost.
The constant is fixed before every atom parameter, including the signed ones. -/
theorem CommonSmoothCutoff.smoothReciprocityLogWeight_fourier_integral_norm_uniform
    {d : ℕ} (hd : d < 8) (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hQc : HasCompactSupport Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z u₀ rho₀ R : ℝ, 1 ≤ Z → 0 ≤ R →
        (∀ t ∈ tsupport Q, |rho₀ * Real.exp (inner ℝ b t)| ≤ R) →
        (∫ ξ : EuclideanSpace ℝ (Fin d),
          ‖𝓕 (smoothReciprocityLogWeight a b c Q Z u₀ rho₀) ξ‖) ≤ C * (1 + R) ^ 4 := by
  obtain ⟨C₄, hC₄, hjet⟩ := smoothReciprocityProfile_logMonomial_mixed_uniform a b c Q hQ hQc 4
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 8 := by
    simpa only [finrank_euclideanSpace_fin] using hd
  obtain ⟨Cd, hCd, hSobolev⟩ :=
    fourier_integral_norm_le_normalizedFourth hdim
  let L : ℝ := (1 + tau * d) ^ 2 * C₄
  let M : ℝ := volume.real (tsupport Q)
  have hL : 0 ≤ L := mul_nonneg (sq_nonneg _) hC₄.le
  have hconstant : 0 ≤ Cd * L * Real.sqrt M := by positivity
  refine ⟨1 + Cd * L * Real.sqrt M, by positivity, ?_⟩
  intro Z u₀ rho₀ R hZ hR hrho
  let f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
    smoothReciprocityLogSchwartzWeight a b c Q hQ hQc Z u₀ rho₀
  let p : ℝ := 1 + R
  have hp : 1 ≤ p := by dsimp [p]; linarith
  have hp4 : 0 ≤ p ^ 4 := by positivity
  have hj (j : ℕ) (hj : j ≤ 4) (x : EuclideanSpace ℝ (Fin d)) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ C₄ * p ^ 4 := by
    exact (hjet Z u₀ rho₀ R hZ hR hrho j hj x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp hj) hC₄.le)
  have hbound (x : EuclideanSpace ℝ (Fin d)) :
      ‖normalizedFourth f x‖ ≤ L * p ^ 4 := by
    exact (normalizedFourth_norm_le f x (C₄ * p ^ 4) (fun j hj' ↦ hj j hj' x)).trans_eq
      (by dsimp [L]; ring)
  have hsupport : tsupport f ⊆ tsupport Q :=
    smoothReciprocityLogWeight_tsupport_subset a b c Q Z u₀ rho₀
  have hL2 := normalizedFourth_sqrt_integral_le f (tsupport Q) hQc hsupport
    (L * p ^ 4) (mul_nonneg hL hp4) hbound
  change (∫ ξ : EuclideanSpace ℝ (Fin d), ‖𝓕 f ξ‖) ≤ _
  calc
    (∫ ξ : EuclideanSpace ℝ (Fin d), ‖𝓕 f ξ‖) ≤
        Cd * Real.sqrt (∫ x, ‖normalizedFourth f x‖ ^ 2) := hSobolev f
    _ ≤ Cd * ((L * p ^ 4) * Real.sqrt M) :=
      mul_le_mul_of_nonneg_left hL2 hCd.le
    _ = (Cd * L * Real.sqrt M) * p ^ 4 := by ring
    _ ≤ (1 + Cd * L * Real.sqrt M) * (1 + R) ^ 4 :=
      mul_le_mul_of_nonneg_right (by linarith) hp4

end

end ImbalancedChen.Part3
