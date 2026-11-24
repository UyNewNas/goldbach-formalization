import ImbalancedChen.Part3E1SameCutoffTail

/-!
# The whole finite fixed-d S2 tail

The complete and retained nonzero-mode sums have identical primitive
gates, modulus weight, short and long coefficients, and totient
denominator. The common one-cell tail bound is summed over the original
finite carriers.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset Filter GevreyCutoff
open scoped BigOperators FourierTransform SchwartzMap

/-- The full zero-deleted S2 Fourier fibre for the common Gevrey profile. -/
def sameCutoffFullS2Fibre (d : ℕ) (a : ℤ) (V : ℝ)
    (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ)
    (q r s n n' : ℕ) : ℂ :=
  if n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s) then
    ((qWeight q : ℂ) * lambdaTrim r * star (lambdaTrim s) * alpha n * star (alpha n')) *
      (∑' h : ℤ, retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h) /
        ((q * d * s).totient : ℂ)
  else 0

/-- The full zero-deleted S2 sum on the original fixed-d carriers. -/
def sameCutoffFullS2FixedD (Q R N : Finset ℕ) (d : ℕ) (a : ℤ) (V : ℝ)
    (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) : ℂ :=
  ∑ q ∈ primitive a Q, ∑ n ∈ N, ∑ s ∈ R, ∑ n' ∈ N, ∑ r ∈ R,
    sameCutoffFullS2Fibre d a V qWeight lambdaTrim alpha q r s n n'

private theorem retainedS2_sameCutoff_window_erase (H d : ℕ) (a : ℤ) (V : ℝ) (q r n : ℕ) :
    (∑ h ∈ Icc (-(H : ℤ)) (H : ℤ),
      retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h) =
     ∑ h ∈ e1NonzeroFrequencies H,
       retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h := by
  have h0 : (0 : ℤ) ∈ Icc (-(H : ℤ)) (H : ℤ) := mem_Icc.mpr ⟨by omega, by omega⟩
  rw [e1NonzeroFrequencies, ← sum_erase_add _ _ h0]
  simp [retainedS2Mode]

private theorem sameCutoffFullS2Fibre_tail_le
    (H : ℝ) (d : ℕ) (a : ℤ) (V : ℝ) (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ)
    (q r s n n' : ℕ) {B err : ℝ} (hB : 0 ≤ B) (herr : 0 ≤ err)
    (hq : 0 < q) (hd : 0 < d) (hs : 0 < s)
    (hqWeight : qWeight q ∈ Set.Icc 0 1)
    (hrWeight : ‖lambdaTrim r‖ ≤ B) (hsWeight : ‖lambdaTrim s‖ ≤ B)
    (hnWeight : ‖alpha n‖ ≤ 1) (hn'Weight : ‖alpha n'‖ ≤ 1)
    (htail : ‖(∑' h : ℤ, retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h) -
      ∑ h ∈ e1NonzeroFrequencies ⌊H⌋₊,
        retainedS2Mode (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) V a (q * d * r) n h‖ ≤ err) :
    ‖sameCutoffFullS2Fibre d a V qWeight lambdaTrim alpha q r s n n' -
      retainedS2Fibre ⌊H⌋₊ d a V (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) qWeight lambdaTrim alpha q r s n n'‖ ≤
      B^2 * err := by
  by_cases hgate : n.Coprime (q * d * r) ∧ n'.Coprime (q * d * s)
  · let z : ℂ := (qWeight q : ℂ) * lambdaTrim r * star (lambdaTrim s) * alpha n * star (alpha n')
    have hz : ‖z‖ ≤ B^2 := by
      dsimp only [z]
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hqWeight.1]
      calc
        _ ≤ 1 * B * B * 1 * 1 := by gcongr; exact hqWeight.2
        _ = _ := by ring
    have hφ : (1 : ℝ) ≤ (q * d * s).totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.mul_pos (Nat.mul_pos hq hd) hs)
    simp only [sameCutoffFullS2Fibre, if_pos hgate, retainedS2Fibre, retainedS2_sameCutoff_window_erase]
    change ‖z * _ / _ - z * _ / _‖ ≤ _
    rw [← sub_div, ← mul_sub, norm_div, Complex.norm_natCast, norm_mul]
    calc
      _ ≤ (B^2 * err) / (q * d * s).totient :=
        div_le_div_of_nonneg_right (mul_le_mul hz htail (norm_nonneg _) (by positivity)) (by positivity)
      _ ≤ _ := div_le_self (by positivity) hφ
  · simp only [sameCutoffFullS2Fibre, retainedS2Fibre, if_neg hgate, sub_zero, norm_zero]
    positivity

/-- The common tail costs the product of the original carrier
cardinalities and the square of the rough coefficient bound. -/
theorem sameCutoffFullS2FixedD_sub_retained_le (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (Q R N : Finset ℕ) (H : ℝ) (d : ℕ) (a : ℤ) (V : ℝ)
      (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) (B : ℝ),
      0 < V → 0 ≤ H → 0 < d → 0 ≤ B →
      (∀ q ∈ Q, 0 < q) → (∀ r ∈ R, 0 < r) →
      (∀ q ∈ Q, ∀ r ∈ R, Real.log X^5 ≤ V / ((q * d * r : ℕ) : ℝ) * H) →
      (∀ q ∈ Q, qWeight q ∈ Set.Icc 0 1) →
      (∀ r ∈ R, ‖lambdaTrim r‖ ≤ B) → (∀ n ∈ N, ‖alpha n‖ ≤ 1) →
      ‖sameCutoffFullS2FixedD Q R N d a V qWeight lambdaTrim alpha -
        retainedS2FixedD Q R N ⌊H⌋₊ d a V (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ)))
          qWeight lambdaTrim alpha‖ ≤
        B^2 * (8 * X ^ (-(K : ℝ))) * (Q.card : ℝ) * (R.card : ℝ)^2 * (N.card : ℝ)^2 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), retainedS2Mode_sameCutoff_tail K]
    with X hX hTail Q R N H d a V qWeight lambdaTrim alpha B hV hH hd hB hQ hR hmesh hW hLambda hAlpha
  let C := B^2 * (8 * X ^ (-(K : ℝ)))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  unfold sameCutoffFullS2FixedD retainedS2FixedD
  simp only [← sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ primitive a Q, ∑ _n ∈ N, ∑ _s ∈ R, ∑ _n' ∈ N, ∑ _r ∈ R, C := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun s hs => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun n' hn' => ?_)
      refine (norm_sum_le _ _).trans (sum_le_sum fun r hr => ?_)
      have hq' : q ∈ Q := (mem_filter.mp hq).1
      exact sameCutoffFullS2Fibre_tail_le H d a V qWeight lambdaTrim alpha q r s n n'
        hB (by positivity) (hQ q hq') hd (hR s hs) (hW q hq')
        (hLambda r hr) (hLambda s hs) (hAlpha n hn) (hAlpha n' hn')
        (hTail V H a q d r n hV (hQ q hq') hd (hR r hr) hH (hmesh q hq' r hr)).2
    _ ≤ ∑ _q ∈ Q, ∑ _n ∈ N, ∑ _s ∈ R, ∑ _n' ∈ N, ∑ _r ∈ R, C :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, C]; ring

/-- Summation over the original small-factor carrier preserves the
individual rough-carrier sizes and pays the common cutoff once per term. -/
theorem sameCutoffFullS2Block_sub_retained_le (K : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ (Q N D : Finset ℕ) (R : ℕ → Finset ℕ) (H : ℕ → ℝ)
      (a : ℤ) (V : ℝ) (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℕ → ℂ)
      (alpha : ℕ → ℂ) (B : ℝ),
      0 < V → 0 ≤ B → (∀ q ∈ Q, 0 < q) →
      (∀ d ∈ D, 0 < d ∧ 0 ≤ H d ∧ ∀ r ∈ R d, 0 < r) →
      (∀ d ∈ D, ∀ q ∈ Q, ∀ r ∈ R d, Real.log X^5 ≤
        V / ((q * d * r : ℕ) : ℝ) * H d) →
      (∀ q ∈ Q, qWeight q ∈ Set.Icc 0 1) →
      (∀ d ∈ D, ∀ r ∈ R d, ‖lambdaTrim d r‖ ≤ B) → (∀ n ∈ N, ‖alpha n‖ ≤ 1) →
      ‖(∑ d ∈ D, sameCutoffFullS2FixedD Q (R d) N d a V qWeight (lambdaTrim d) alpha) -
        ∑ d ∈ D, retainedS2FixedD Q (R d) N ⌊H d⌋₊ d a V
          (⇑(𝓕 cutoffSchwartz : 𝓢(ℝ, ℂ))) qWeight (lambdaTrim d) alpha‖ ≤
        (B^2 * (8 * X ^ (-(K : ℝ))) * (Q.card : ℝ) * (N.card : ℝ)^2) *
          ∑ d ∈ D, ((R d).card : ℝ)^2 := by
  filter_upwards [sameCutoffFullS2FixedD_sub_retained_le K]
    with X hTail Q N D R H a V qWeight lambdaTrim alpha B hV hB hQ hD hmesh hW hLambda hAlpha
  rw [← sum_sub_distrib, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun d hd => ?_)
  obtain ⟨hdpos, hH, hR⟩ := hD d hd
  refine (hTail Q (R d) N (H d) d a V qWeight (lambdaTrim d) alpha B hV hH hdpos hB
    hQ hR (hmesh d hd) hW (hLambda d hd) hAlpha).trans_eq ?_
  ring

end

end ImbalancedChen.Part3.E1Finite
