import ImbalancedChen.Part3E1GevreyTailEnvelope
import ImbalancedChen.Part3E1PhysicalTail

/-!
# The physical medium S2 estimate

The common Fourier cutoff is large enough for every supported modulus.
The complete physical sum, with its exact zero mode subtracted, satisfies
the same normalized power saving as the retained Fourier model.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter E1Finite
open scoped BigOperators FourierTransform SchwartzMap

private theorem physicalSameCutoffS2FixedD_eq_filter_qWeight_ne_zero
    (Q R N : Finset ℕ) (k : ℕ) (a : ℤ) (V : ℝ) (qWeight : ℕ → ℝ)
    (lambdaTrim alpha : ℕ → ℂ) :
    physicalSameCutoffS2FixedD Q R N k a V qWeight lambdaTrim alpha =
      physicalSameCutoffS2FixedD (Q.filter fun q => qWeight q ≠ 0)
        R N k a V qWeight lambdaTrim alpha := by
  simp only [physicalSameCutoffS2FixedD, primitive_eq_filter, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  by_cases hqw : qWeight q = 0
  · simp [hqw, physicalSameCutoffS2Fibre]
  · simp [hqw]

private theorem physicalSameCutoffS2ZeroFixedD_eq_filter_qWeight_ne_zero
    (Q R N : Finset ℕ) (k : ℕ) (a : ℤ) (V : ℝ) (qWeight : ℕ → ℝ)
    (lambdaTrim alpha : ℕ → ℂ) :
    physicalSameCutoffS2ZeroFixedD Q R N k a V qWeight lambdaTrim alpha =
      physicalSameCutoffS2ZeroFixedD (Q.filter fun q => qWeight q ≠ 0)
        R N k a V qWeight lambdaTrim alpha := by
  simp only [physicalSameCutoffS2ZeroFixedD, primitive_eq_filter, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  by_cases hqw : qWeight q = 0
  · simp [hqw]
  · simp [hqw]

private theorem mediumS2_tail_payment {X U D Q₁ V σ : ℝ}
    (hX : 1 ≤ X) (hU : 1 ≤ U) (hD : 1 ≤ D) (hDX : D ≤ X)
    (hQ₁ : 1 ≤ Q₁) (hQ₁X : Q₁ ≤ X) (hV : 1 ≤ V) (hσ : σ ≤ 2) :
    X ^ (-12 : ℝ) * X ^ 8 / V ≤ (U ^ 2 / (D * Q₁)) * X ^ (-σ / 2) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hQ₀ : 0 < Q₁ := zero_lt_one.trans_le hQ₁
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hbound : D * Q₁ ≤ X ^ 2 := by rw [pow_two]; gcongr
  have hscale : 1 / X ^ 2 ≤ U ^ 2 / (D * Q₁) := by
    apply div_le_div_iff₀ (by positivity) (by positivity) |>.mpr
    rw [one_mul]
    exact hbound.trans (le_mul_of_one_le_left (sq_nonneg X) (one_le_pow₀ hU))
  calc
    _ ≤ X ^ (-12 : ℝ) * X ^ 8 := div_le_self (by positivity) hV
    _ = X ^ (-4 : ℝ) := by rw [← Real.rpow_natCast X 8, ← Real.rpow_add hX0]; norm_num
    _ ≤ X ^ (-2 - σ / 2) := Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = (1 / X ^ 2) * X ^ (-σ / 2) := by
      rw [sub_eq_add_neg, Real.rpow_add hX0, Real.rpow_neg hX0.le, one_div, neg_div]
      simp only [Real.rpow_two]
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)


/-- The physical S2 estimate with the exact zero coefficient removed.
Both the q weight and the sampled progression use the same Gevrey profile. -/
theorem exists_physicalS2_medium_gevreyWindow {σ c0 Ccut : ℝ}
    (hσ : 0 < σ) (hσHi : σ ≤ 2) (hc0 : 0 < c0) (hCcut : 0 ≤ Ccut) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ (B : ℕ) (κ : ℝ) (d : MediumAtom),
      MediumAdmissible B σ κ c0 d → X₀ ≤ d.scale →
      ∀ (D : ℝ), 1 ≤ D → D ≤ (d.scale ^ (1 / Real.log (Real.log d.scale)))^2 →
      ∀ (Q : Finset ℕ) (R H : ℕ → ℝ) (Rs : ℕ → Finset ℕ) (lambdaTrim : ℕ → ℕ → ℂ),
        (∀ k ∈ factorCarrier D, (Rs k).Nonempty →
          1 ≤ R k ∧ (k : ℝ) * R k ≤ 4 * d.Q2 * d.Q3 ∧ Rs k ⊆ factorCarrier (R k)) →
        (∀ k ∈ factorCarrier D, 0 ≤ H k ∧
          10 * Real.log d.scale ^ 5 * (D * d.Q1 * R k / d.V) ≤ H k ∧
          H k ≤ Ccut * Real.log d.scale ^ 5 * (D * d.Q1 * R k / d.V)) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, ‖lambdaTrim k r‖ ≤ ((k * r).divisors.card : ℝ)) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, lambdaTrim k r ≠ 0 → (k * r).Coprime d.residue.natAbs) →
        ‖(∑ k ∈ factorCarrier D,
            physicalSameCutoffS2FixedD Q (Rs k) d.alphaCarrier k d.residue d.V
              (fun q => GevreyCutoff.cutoff ((q : ℝ) / d.Q1)) (lambdaTrim k) d.alpha) -
          ∑ k ∈ factorCarrier D,
            physicalSameCutoffS2ZeroFixedD Q (Rs k) d.alphaCarrier k d.residue d.V
              (fun q => GevreyCutoff.cutoff ((q : ℝ) / d.Q1)) (lambdaTrim k) d.alpha‖ / d.V ≤
          C * (d.U ^ 2 / (D * d.Q1)) * d.scale ^ (-σ / 2) := by
  obtain ⟨C₁, hC₁, X₁, hretained⟩ := exists_retainedS2_medium_gevreyWindow hσ hc0 hCcut
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1 : ℝ)).and
      (eventually_mediumGevreyS2_splitScale_le_scale.and
        (physicalSameCutoffS2Block_sub_retained_le 12)))
  refine ⟨C₁ + 655360, by positivity, max X₁ X₂, ?_⟩
  intro B κ d hd hX D hD hDsmall Q R H Rs lambdaTrim hR hH hτ hprimitive
  obtain ⟨hX1, hDsub, htail⟩ := hX₂ d.scale ((le_max_right _ _).trans hX)
  have hDX : D ≤ d.scale := hDsmall.trans hDsub
  have hdData := hd
  obtain ⟨hU, hV1, hQ₁, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hdData
  have hV : 0 < d.V := zero_lt_one.trans_le hV1
  let qWeight := fun q : ℕ => GevreyCutoff.cutoff ((q : ℝ) / d.Q1)
  let Q' := mediumGevreyS2SupportedQ d Q
  let K := factorCarrier D
  have hq' (q : ℕ) (hq : q ∈ Q') : 0 < q ∧ (q : ℝ) ≤ 5 * d.Q1 / 2 := by
    obtain ⟨hpos, _, hhi⟩ := mediumGevreyS2_supportedQ_bounds hQ₁ hq
    exact ⟨hpos, hhi⟩
  have hK (k : ℕ) (hk : k ∈ K) : 0 < k ∧ (k : ℝ) ≤ 2 * D := by
    obtain ⟨hlo, hhi⟩ := e1FactorCarrier_bounds (zero_le_one.trans hD) hk
    exact ⟨by exact_mod_cast (zero_lt_one.trans_le (hD.trans hlo)), hhi⟩
  have hr (k : ℕ) (hk : k ∈ K) (r : ℕ) (hrk : r ∈ Rs k) :
      0 < r ∧ (r : ℝ) ≤ 2 * R k := by
    obtain ⟨hRk, _, hsub⟩ := hR k hk ⟨r, hrk⟩
    exact (mediumGevreyS2_rough_bounds hD hRk hk (hsub hrk)).2
  have hData : ∀ k ∈ K, 0 < k ∧ 0 ≤ H k ∧ ∀ r ∈ Rs k, 0 < r :=
    fun k hk => ⟨(hK k hk).1, (hH k hk).1, fun r hrk => (hr k hk r hrk).1⟩
  have hmesh : ∀ k ∈ K, ∀ q ∈ Q', ∀ r ∈ Rs k,
      Real.log d.scale ^ 5 ≤ d.V / ((q * k * r : ℕ) : ℝ) * H k :=
    fun k hk q hq r hrk =>
      (sameCutoffMode_medium_mesh hX1 hV (hq' q hq).1 (hK k hk).1 (hr k hk r hrk).1
        (hq' q hq).2 (hK k hk).2 (hr k hk r hrk).2 (hH k hk).2.1).2
  have hNorm (k : ℕ) (hk : k ∈ K) (r : ℕ) (hrk : r ∈ Rs k) :
      ‖lambdaTrim k r‖ ≤ 8 * d.scale := by
    obtain ⟨hRk, hprod, hsub⟩ := hR k hk ⟨r, hrk⟩
    exact mediumGevreyS2_trim_le hσ.le hX1 hd hRk hprod (hsub hrk) (hτ k hk r hrk)
  have hEnvelope : (8 * d.scale)^2 * (Q'.card : ℝ) * (d.alphaCarrier.card : ℝ)^2 *
      (∑ k ∈ K, ((Rs k).card : ℝ)^2) ≤ 81920 * d.scale^8 := by
    exact mediumGevreyS2_card_envelope hσ.le hX1 hd hD hDX Q R Rs hR
  let S := ∑ k ∈ K, physicalSameCutoffS2FixedD Q' (Rs k) d.alphaCarrier k d.residue d.V
    qWeight (lambdaTrim k) d.alpha
  let Z := ∑ k ∈ K, physicalSameCutoffS2ZeroFixedD Q' (Rs k) d.alphaCarrier k d.residue d.V
    qWeight (lambdaTrim k) d.alpha
  let T := ∑ k ∈ K, retainedS2FixedD Q' (Rs k) d.alphaCarrier ⌊H k⌋₊ k d.residue d.V
    (⇑(𝓕 GevreyCutoff.cutoffSchwartz : 𝓢(ℝ, ℂ))) qWeight (lambdaTrim k) d.alpha
  let Y := (d.U ^ 2 / (D * d.Q1)) * d.scale ^ (-σ / 2)
  have hT : ‖T‖ / d.V ≤ C₁ * Y := by
    simpa only [T, Y, qWeight, K, mul_assoc] using
      hretained B κ d hd ((le_max_left _ _).trans hX) D hD hDsmall Q' R H Rs lambdaTrim
        hR (fun k hk => ⟨(hH k hk).1, (hH k hk).2.2⟩) hτ hprimitive
  have hTailNorm : ‖S - Z - T‖ ≤ 655360 * (d.scale ^ (-12 : ℝ) * d.scale ^ 8) := by
    calc
      _ ≤ ((8 * d.scale)^2 * (8 * d.scale ^ (-12 : ℝ)) *
          (Q'.card : ℝ) * (d.alphaCarrier.card : ℝ)^2) *
          (∑ k ∈ K, ((Rs k).card : ℝ)^2) := by
        simpa only [S, Z, T, Nat.cast_ofNat] using htail Q' d.alphaCarrier K Rs H d.residue d.V
          qWeight lambdaTrim d.alpha (8 * d.scale) hV (by positivity) (fun q hq => (hq' q hq).1)
          hData hmesh (fun q _ => GevreyCutoff.cutoff_mem_Icc ((q : ℝ) / d.Q1))
          hNorm hAlpha
      _ = (8 * d.scale ^ (-12 : ℝ)) * ((8 * d.scale)^2 * (Q'.card : ℝ) *
          (d.alphaCarrier.card : ℝ)^2 * (∑ k ∈ K, ((Rs k).card : ℝ)^2)) := by ring
      _ ≤ (8 * d.scale ^ (-12 : ℝ)) * (81920 * d.scale^8) :=
        mul_le_mul_of_nonneg_left hEnvelope (by positivity)
      _ = _ := by ring
  have hTailPaid : ‖S - Z - T‖ / d.V ≤ 655360 * Y := by
    calc
      _ ≤ (655360 * (d.scale ^ (-12 : ℝ) * d.scale ^ 8)) / d.V :=
        div_le_div_of_nonneg_right hTailNorm hV.le
      _ = 655360 * (d.scale ^ (-12 : ℝ) * d.scale ^ 8 / d.V) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mediumS2_tail_payment hX1 hU hD hDX hQ₁
          (medium_e1_factorLengths_le_scale hσ.le hX1 hd).1 hV1 hσHi) (by norm_num)
  change ‖(∑ k ∈ K, physicalSameCutoffS2FixedD Q (Rs k) d.alphaCarrier k d.residue d.V
      qWeight (lambdaTrim k) d.alpha) - ∑ k ∈ K,
        physicalSameCutoffS2ZeroFixedD Q (Rs k) d.alphaCarrier k d.residue d.V
          qWeight (lambdaTrim k) d.alpha‖ / d.V ≤ _
  simp_rw [physicalSameCutoffS2FixedD_eq_filter_qWeight_ne_zero Q,
    physicalSameCutoffS2ZeroFixedD_eq_filter_qWeight_ne_zero Q]
  change ‖S - Z‖ / d.V ≤ _
  calc
    _ = ‖(S - Z - T) + T‖ / d.V := by rw [sub_add_cancel]
    _ ≤ (‖S - Z - T‖ + ‖T‖) / d.V :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hV.le
    _ = ‖S - Z - T‖ / d.V + ‖T‖ / d.V := add_div _ _ _
    _ ≤ 655360 * Y + C₁ * Y := add_le_add hTailPaid hT
    _ = _ := by dsimp only [Y]; ring

end

end ImbalancedChen.Part3
