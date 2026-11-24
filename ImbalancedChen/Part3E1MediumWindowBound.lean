import ImbalancedChen.Part3E1MediumDivisorBudget
import ImbalancedChen.Part3E1MediumQCover
import ImbalancedChen.Part3E1MediumRetained

/-! Equation (20) with the physical smooth q window and elementary trim bound. -/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset
open scoped BigOperators SchwartzMap FourierTransform

private theorem retainedS2FixedD_eq_filter_qWeight_ne_zero
    (Q R N : Finset ℕ) (H k : ℕ) (a : ℤ) (V : ℝ)
    (ψhat : ℝ → ℂ) (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) :
    retainedS2FixedD Q R N H k a V ψhat qWeight lambdaTrim alpha =
      retainedS2FixedD (Q.filter fun q => qWeight q ≠ 0) R N H k a V ψhat qWeight lambdaTrim alpha := by
  simp only [retainedS2FixedD, primitive_eq_filter, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  by_cases hqw : qWeight q = 0
  · simp [hqw, retainedS2Fibre]
  · simp [hqw]

/-- The retained original S2 source on a full smooth window and closed dyadic
split-divisor block. The q occupancy and trim subpower constant are supplied
uniformly by the window support and the elementary divisor count. -/
theorem exists_retainedS2_medium_smoothWindow {σ c0 Ccut : ℝ}
    (hσ : 0 < σ) (hc0 : 0 < c0) (hCcut : 0 ≤ Ccut) (ψ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (κ : ℝ) (d : MediumAtom),
      MediumAdmissible B σ κ c0 d → 2 ≤ d.scale →
      (4 * Ccut) * Real.log d.scale ^ 5 ≤ d.scale →
      ∀ (D : ℝ), 1 ≤ D → D ≤ d.scale ^ (σ / 2) → 2 ≤ d.scale ^ (σ / 2) →
      ∀ (Q : Finset ℕ) (R H : ℕ → ℝ) (Rs : ℕ → Finset ℕ)
        (qWeight : ℕ → ℝ) (lambdaTrim : ℕ → ℕ → ℂ),
        (∀ q ∈ Q, qWeight q ≠ 0 →
          d.Q1 / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 5 * d.Q1 / 2) →
        (∀ k ∈ factorCarrier D, (Rs k).Nonempty →
          1 ≤ R k ∧ (k : ℝ) * R k ≤ 4 * d.Q2 * d.Q3 ∧ Rs k ⊆ factorCarrier (R k)) →
        (∀ k ∈ factorCarrier D, 0 ≤ H k ∧
          H k ≤ (Ccut * Real.log d.scale ^ 5) * ((D * d.Q1) * R k / d.V)) →
        (∀ q ∈ Q, qWeight q ∈ Set.Icc 0 1) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, ‖lambdaTrim k r‖ ≤ ((k * r).divisors.card : ℝ)) →
        (∀ k ∈ factorCarrier D, ∀ r ∈ Rs k, lambdaTrim k r ≠ 0 → (k * r).Coprime d.residue.natAbs) →
        ‖∑ k ∈ factorCarrier D,
          retainedS2FixedD Q (Rs k) d.alphaCarrier ⌊H k⌋₊ k d.residue d.V
            (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) qWeight (lambdaTrim k) d.alpha‖ / d.V ≤
          C * (d.U ^ 2 / (D * d.Q1)) * d.scale ^ (-σ / 2) := by
  obtain ⟨B₀, hB₀, hBudget⟩ := exists_medium_e1_trim_divisorBudget hσ
  obtain ⟨C, hC, hBound⟩ := exists_retainedS2_medium_dyadicBlock hσ hc0 hCcut hB₀ ψ
  refine ⟨C * 3, by positivity, ?_⟩
  intro B κ d hd hX hlog D hD hDsub hXlarge Q R H Rs qWeight lambdaTrim
    hSupport hR hH hqWeight htau hprimitive
  let Q' := Q.filter fun q => qWeight q ≠ 0
  have hQ' (q : ℕ) (hq : q ∈ Q') : d.Q1 / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 5 * d.Q1 / 2 :=
    hSupport q (mem_filter.mp hq).1 (mem_filter.mp hq).2
  obtain ⟨Qs, q₀, hcover, hdis, hCells⟩ :=
    e1SmoothWindow_exists_three_qCells d.Q1 hd.2.2.1 Q' hQ'
  have hlambda (k : ℕ) (hk : k ∈ factorCarrier D) (r : ℕ) (hr : r ∈ Rs k) :
      ‖lambdaTrim k r‖ ≤ B₀ * d.scale ^ (σ / 10) := by
    have hX1 : 1 ≤ d.scale := (by norm_num : (1 : ℝ) ≤ 2).trans hX
    have hX0 := zero_lt_one.trans_le hX1
    obtain ⟨hk0, _, _⟩ := e1DyadicSplitDivisor_bounds hX0 hD hDsub hXlarge hk
    obtain ⟨hRk, hprod, hRsub⟩ := hR k hk ⟨r, hr⟩
    exact (htau k hk r hr).trans (hBudget B κ c0 d hd hX1 k (R k) hk0 hRk hprod r (hRsub hr))
  simp_rw [retainedS2FixedD_eq_filter_qWeight_ne_zero Q]
  exact hBound B κ d hd hX hlog D hD hDsub hXlarge univ 3 (by simp) Q' Qs q₀
    hcover hdis (fun i _ => hCells i) R H Rs qWeight lambdaTrim hR hH
    (fun q hq => hqWeight q (mem_filter.mp hq).1) hlambda hprimitive

end

end ImbalancedChen.Part3.E1Finite
