import ImbalancedChen.Part3E1FixedDSource
import ImbalancedChen.Part3E1RealScales

/-!
# The equation (18) estimate for one fixed-d retained S2 cell

The outer modulus image and the exact rough and alpha supports are embedded
into closed real dyadic carriers by zero extension. Normalizing the rough
coefficient costs its fourth power in the squared bound, while the physical
Poisson prefactor is retained as `V^2`.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset
open scoped BigOperators SchwartzMap FourierTransform

private theorem factorCarrier_pos {L : ℝ} (hL : 1 ≤ L) {n : ℕ}
    (hn : n ∈ factorCarrier L) : 0 < n :=
  (Nat.ceil_pos.mpr (zero_lt_one.trans_le hL)).trans_le (mem_Icc.mp hn).1

private theorem retainedS2FixedD_scale_trim (Q R N : Finset ℕ) (H d : ℕ) (a : ℤ) (V : ℝ)
    (ψhat : ℝ → ℂ) (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ) (B : ℝ) :
    retainedS2FixedD Q R N H d a V ψhat qWeight (fun r => (B : ℂ) * lambdaTrim r) alpha =
      (B : ℂ)^2 * retainedS2FixedD Q R N H d a V ψhat qWeight lambdaTrim alpha := by
  unfold retainedS2FixedD
  simp_rw [mul_sum]
  refine sum_congr rfl (fun q _ => sum_congr rfl (fun n _ => sum_congr rfl (fun s _ =>
    sum_congr rfl (fun n' _ => sum_congr rfl (fun r _ => ?_)))))
  unfold retainedS2Fibre
  split_ifs
  · simp only [star_mul, Complex.star_def, Complex.conj_ofReal, div_eq_mul_inv]
    ring
  · simp only [mul_zero]

/-- Equation (18) for the exact fixed-d retained S2 source in one outer
cell. The constant is fixed before all scales, residues, and coefficients. -/
theorem exists_retainedS2FixedD_norm_sq_le {κ ε Ccut : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hCcut : 0 ≤ Ccut) (ψ : 𝓢(ℝ, ℂ)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (X V Q R N H : ℝ), 2 ≤ X → 0 < V → 1 ≤ Q → 1 ≤ R → 1 ≤ N → 0 ≤ H →
        X = V * N → 8 * Q * R^2 ≤ X ^ κ → 4 * H * R ≤ X ^ κ →
        H ≤ (Ccut * (Real.log X)^5) * (Q * R / V) →
        ∀ (d : ℕ) (Qs Rs Ns : Finset ℕ) (B : ℝ) (a : ℤ)
          (qWeight : ℕ → ℝ) (lambdaTrim alpha : ℕ → ℂ),
          0 < d → 0 < B → fixedDModuli d Qs ⊆ factorCarrier Q →
          Rs ⊆ factorCarrier R → Ns ⊆ factorCarrier N →
          (∀ q ∈ Qs, qWeight q ∈ Set.Icc 0 1) →
          (∀ r ∈ Rs, ‖lambdaTrim r‖ ≤ B) →
          (∀ r ∈ Rs, lambdaTrim r ≠ 0 → (d * r).Coprime a.natAbs) →
          (∀ n ∈ Ns, ‖alpha n‖ ≤ 1) →
          ‖retainedS2FixedD Qs Rs Ns ⌊H⌋₊ d a V
            (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) qWeight lambdaTrim alpha‖ ^ 2 ≤
            V^2 * B^4 * (A * X ^ ε * (N^4 / Q^2) *
              (N * Q / X + N * Q ^ (5/2 : ℝ) * R^3 / X^2 + N^2 * Q * R / X^2)) := by
  obtain ⟨A, hA, hbound⟩ := exists_source_realDyadic_equation18 hκ hε hCcut ψ
  refine ⟨A, hA, ?_⟩
  intro X V Q R N H hX hV hQ hR hN hH hXeq hQR hHR hcut
    d Qs Rs Ns B a qWeight lambdaTrim alpha hd hB hQimg hRs hNs hw htrim hprimitive halpha
  let ψhat : ℝ → ℂ := ⇑(𝓕 ψ : 𝓢(ℝ, ℂ))
  let trimUnit (r : ℕ) : ℂ := (B⁻¹ : ℝ) * lambdaTrim r
  let lambdaExt (q r : ℕ) : ℂ :=
    if q ∈ fixedDModuli d Qs ∧ r ∈ Rs then fixedDLambda d qWeight trimUnit q r else 0
  let alphaExt (n : ℕ) : ℂ := if n ∈ Ns then alpha n else 0
  have hqPos (q : ℕ) (hq : q ∈ Qs) : 0 < q :=
    Nat.pos_of_mul_pos_left (factorCarrier_pos hQ (hQimg (mem_image_of_mem (fun m => d * m) hq)))
  have hUnit (r : ℕ) (hr : r ∈ Rs) : ‖trimUnit r‖ ≤ 1 := by
    have hBinv : 0 < B⁻¹ := inv_pos.mpr hB
    simp only [trimUnit, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hBinv]
    exact (mul_le_mul_of_nonneg_left (htrim r hr) hBinv.le).trans_eq (inv_mul_cancel₀ hB.ne')
  have hnormLambda (q : ℕ) (_ : q ∈ factorCarrier Q) (r : ℕ) (_ : r ∈ factorCarrier R) :
      ‖lambdaExt q r‖ ≤ 1 := by
    by_cases hqr : q ∈ fixedDModuli d Qs ∧ r ∈ Rs
    · obtain ⟨q₀, hq₀, hq⟩ := mem_image.mp hqr.1
      have hroot : Real.sqrt (qWeight q₀) ≤ 1 := Real.sqrt_le_one.mpr (hw q₀ hq₀).2
      dsimp only [lambdaExt]
      rw [if_pos hqr]
      simp only [fixedDLambda, ← hq, Nat.mul_div_cancel_left _ hd,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      simpa only [mul_one] using mul_le_mul hroot (hUnit r hqr.2) (norm_nonneg _) zero_le_one
    · simp [lambdaExt, hqr]
  have hnormAlpha (n : ℕ) (_ : n ∈ factorCarrier N) : ‖alphaExt n‖ ≤ 1 := by
    by_cases hn : n ∈ Ns
    · simpa only [alphaExt, if_pos hn] using halpha n hn
    · simp [alphaExt, hn]
  have hunitPrim (r : ℕ) (hr : r ∈ Rs) (hne : trimUnit r ≠ 0) : (d * r).Coprime a.natAbs :=
    hprimitive r hr (fun hz => hne (by simp [trimUnit, hz]))
  have hrescale (r : ℕ) : (B : ℂ) * trimUnit r = lambdaTrim r := by
    change (B : ℂ) * ((B⁻¹ : ℝ) * lambdaTrim r) = lambdaTrim r
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hB.ne', Complex.ofReal_one, one_mul]
  have heq : retainedS2FixedD Qs Rs Ns ⌊H⌋₊ d a V ψhat qWeight lambdaTrim alpha =
      (B : ℂ)^2 * (V : ℂ) * source (factorCarrier Q) (factorCarrier R) (factorCarrier N)
        (e1NonzeroFrequencies ⌊H⌋₊) a V ψhat lambdaExt alphaExt := by
    calc
      _ = retainedS2FixedD Qs Rs Ns ⌊H⌋₊ d a V ψhat qWeight
          (fun r => (B : ℂ) * trimUnit r) alpha := by simp only [hrescale]
      _ = (B : ℂ)^2 * retainedS2FixedD Qs Rs Ns ⌊H⌋₊ d a V ψhat qWeight trimUnit alpha :=
        retainedS2FixedD_scale_trim Qs Rs Ns ⌊H⌋₊ d a V ψhat qWeight trimUnit alpha B
      _ = _ := by
        rw [retainedS2FixedD_eq_source Qs Rs Ns ⌊H⌋₊ d a V ψhat qWeight trimUnit alpha
          hd hqPos (fun _ hr => factorCarrier_pos hR (hRs hr)) (fun q hq => (hw q hq).1) hunitPrim,
          source_subsets_eq_zero_extend (fixedDModuli d Qs) (factorCarrier Q) Rs (factorCarrier R)
            Ns (factorCarrier N) hQimg hRs hNs]
        exact (mul_assoc _ _ _).symm
  have hmain := hbound X V Q R N H hX hV hQ hR hN hH hXeq hQR hHR hcut
    a lambdaExt alphaExt hnormLambda hnormAlpha
  rw [show (⇑(𝓕 ψ : 𝓢(ℝ, ℂ))) = ψhat from rfl, heq]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hV.le,
    abs_of_nonneg hB.le, mul_pow]
  calc
    _ = V^2 * B^4 * ‖source (factorCarrier Q) (factorCarrier R) (factorCarrier N)
        (e1NonzeroFrequencies ⌊H⌋₊) a V ψhat lambdaExt alphaExt‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (by positivity)

end

end ImbalancedChen.Part3.E1Finite
