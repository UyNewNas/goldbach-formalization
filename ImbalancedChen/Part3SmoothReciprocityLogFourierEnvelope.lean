import ImbalancedChen.Part3SmoothReciprocityLogFourierL1

/-!
A common pointwise Fourier envelope for the literal logarithmic weight.
The fixed fourth-order jet bound pays the L1 norm of the actual normalized
fourth-order operator on the fixed localizer support. Its exact Fourier
symbol supplies one radial envelope for every signed atom parameter.
The radial kernel is integrable in real dimension strictly below four.
-/

namespace ImbalancedChen.Part3

noncomputable section

open MeasureTheory FourierTransform Laplacian LineDeriv
open scoped SchwartzMap FourierTransform ContDiff BigOperators RealInnerProductSpace
open CommonSmoothCutoff SchwartzFourierL1Sobolev

namespace SmoothReciprocityLogFourierEnvelopeProof

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

private theorem fourier_laplacian_apply (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (ξ : EuclideanSpace ℝ (Fin d)) :
    𝓕 (Δ f) ξ = (-(2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) • 𝓕 f ξ := by
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM,
    FourierTransform.fourier_smul, SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]
  change (-(2 * Real.pi) ^ 2) •
      (SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ (Fin d) ↦ ‖x‖ ^ 2) (𝓕 f) ξ) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (Function.hasTemperateGrowth_norm_sq (EuclideanSpace ℝ (Fin d))), smul_smul]

private theorem fourier_normalizedStep_apply (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (ξ : EuclideanSpace ℝ (Fin d)) :
    𝓕 (normalizedStep f) ξ = (1 + ‖ξ‖ ^ 2) • 𝓕 f ξ := by
  have hlin : 𝓕 (normalizedStep f) =
      𝓕 f - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • 𝓕 (Δ f) := by
    simp only [normalizedStep, sub_eq_add_neg, FourierTransform.fourier_add,
      FourierTransform.fourier_neg, FourierTransform.fourier_smul]
  rw [hlin]
  change 𝓕 f ξ - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • 𝓕 (Δ f) ξ = _
  rw [fourier_laplacian_apply, smul_smul]
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  have hcoef : ((2 * Real.pi) ^ 2)⁻¹ *
      (-(2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) = -(‖ξ‖ ^ 2) := by
    calc
      ((2 * Real.pi) ^ 2)⁻¹ * (-(2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) =
          -((((2 * Real.pi) ^ 2)⁻¹ * (2 * Real.pi) ^ 2) * ‖ξ‖ ^ 2) := by ring
      _ = -(‖ξ‖ ^ 2) := by rw [inv_mul_cancel₀ hpi, one_mul]
  rw [hcoef, neg_smul, sub_neg_eq_add, add_smul, one_smul]

private theorem fourier_normalizedFourth_apply (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (ξ : EuclideanSpace ℝ (Fin d)) :
    𝓕 (normalizedFourth f) ξ = (1 + ‖ξ‖ ^ 2) ^ 2 • 𝓕 f ξ := by
  rw [normalizedFourth, fourier_normalizedStep_apply,
    fourier_normalizedStep_apply, smul_smul, ← pow_two]

private theorem normalizedFourth_integral_norm_le
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K)
    (hsupport : tsupport f ⊆ K) (B : ℝ)
    (hbound : ∀ x, ‖normalizedFourth f x‖ ≤ B) :
    (∫ x, ‖normalizedFourth f x‖) ≤ B * volume.real K := by
  have hzero (x : EuclideanSpace ℝ (Fin d)) (hx : x ∉ K) :
      ‖normalizedFourth f x‖ = 0 := by
    rw [normalizedFourth_zero_off_support f x (fun hf ↦ hx (hsupport hf)), norm_zero]
  have hset := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzero
  rw [← hset]
  calc
    (∫ x in K, ‖normalizedFourth f x‖) ≤ ‖∫ x in K, ‖normalizedFourth f x‖‖ :=
      le_abs_self _
    _ ≤ B * volume.real K :=
      norm_setIntegral_le_of_norm_le_const hK.measure_lt_top (fun x _ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hbound x)

private theorem fourier_norm_le_normalizedFourth_integral
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖𝓕 f ξ‖ ≤ (∫ x, ‖normalizedFourth f x‖) * ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
  have hF : ‖𝓕 (normalizedFourth f) ξ‖ ≤ ∫ x, ‖normalizedFourth f x‖ := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (innerₗ (EuclideanSpace ℝ (Fin d)))
      (normalizedFourth f : EuclideanSpace ℝ (Fin d) → ℂ) ξ
  have hidentity : ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ * ‖𝓕 (normalizedFourth f) ξ‖ = ‖𝓕 f ξ‖ := by
    rw [fourier_normalizedFourth_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (1 + ‖ξ‖ ^ 2))]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  calc
    ‖𝓕 f ξ‖ = ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ * ‖𝓕 (normalizedFourth f) ξ‖ := hidentity.symm
    _ ≤ ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (∫ x, ‖normalizedFourth f x‖) :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    _ = _ := mul_comm _ _

end SmoothReciprocityLogFourierEnvelopeProof

open SmoothReciprocityLogFourierEnvelopeProof in
/-- One pointwise envelope works for the whole literal signed-parameter family.
The pointwise estimate itself requires no dimension bound. -/
theorem CommonSmoothCutoff.smoothReciprocityLogWeight_fourier_pointwise_envelope
    {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d))
    (Q : EuclideanSpace ℝ (Fin d) → ℂ)
    (hQ : ContDiff ℝ ∞ Q) (hQc : HasCompactSupport Q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z u₀ rho₀ R : ℝ, 1 ≤ Z → 0 ≤ R →
        (∀ t ∈ tsupport Q, |rho₀ * Real.exp (inner ℝ b t)| ≤ R) →
        ∀ ξ : EuclideanSpace ℝ (Fin d),
          ‖𝓕 (smoothReciprocityLogWeight a b c Q Z u₀ rho₀) ξ‖ ≤
            C * (1 + R) ^ 4 * ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
  obtain ⟨C₄, hC₄, hjet⟩ := smoothReciprocityProfile_logMonomial_mixed_uniform a b c Q hQ hQc 4
  let L : ℝ := (1 + tau * d) ^ 2 * C₄
  let M : ℝ := volume.real (tsupport Q)
  have hL : 0 ≤ L := mul_nonneg (sq_nonneg _) hC₄.le
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hconstant : 0 ≤ L * M := mul_nonneg hL hM
  refine ⟨1 + L * M, by positivity, ?_⟩
  intro Z u₀ rho₀ R hZ hR hrho ξ
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
  have hL1 := normalizedFourth_integral_norm_le f (tsupport Q) hQc hsupport
    (L * p ^ 4) hbound
  change ‖𝓕 f ξ‖ ≤ _
  calc
    ‖𝓕 f ξ‖ ≤ (∫ x, ‖normalizedFourth f x‖) * ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ :=
      fourier_norm_le_normalizedFourth_integral f ξ
    _ ≤ ((L * p ^ 4) * M) * ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hL1 (by positivity)
    _ = (L * M) * p ^ 4 * ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by ring
    _ ≤ (1 + L * M) * (1 + R) ^ 4 * ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hp4) (by positivity)

/-- The fixed radial kernel of the common envelope is integrable for d<4. -/
theorem CommonSmoothCutoff.smoothReciprocityLogWeight_fourier_envelope_kernel_integrable
    {d : ℕ} (hd : d < 4) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) ↦ ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < 4 := by
    simpa only [finrank_euclideanSpace_fin] using (show (d : ℝ) < 4 by exact_mod_cast hd)
  have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) hdim
  have heq (ξ : EuclideanSpace ℝ (Fin d)) :
      (1 + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
    norm_num only [show -(4 : ℝ) / 2 = -(2 : ℝ) by norm_num,
      Real.rpow_neg_ofNat, zpow_neg, zpow_natCast]
  simpa only [heq] using h

end

end ImbalancedChen.Part3
