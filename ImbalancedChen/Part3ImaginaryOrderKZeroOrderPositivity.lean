import ImbalancedChen.Part3ImaginaryOrderKPositiveAxis
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
Elementary positivity and domination for the actual integral realization of
K_{2it}(q). These statements hold for every q>0 and every real t, including
t=0. They neither identify another Bessel implementation nor assert
positivity when t is nonzero.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKZeroOrderPositivitySourceOnly
noncomputable section
open Set MeasureTheory Filter
open ImaginaryOrderKBesselSourceOnly

private lemma zero_integrand (q : ℝ) :
    kIntegrand 0 q = fun u : ℝ => Real.exp (-q * Real.cosh u) := by
  funext u
  simp [kIntegrand]

/-- The zero-order K integral is strictly positive on the positive q-axis. -/
theorem imaginaryOrderK_zero_pos {q : ℝ} (hq : 0 < q) :
    0 < imaginaryOrderK 0 q := by
  have hpos :
      0 < ∫ u in Ioi (0 : ℝ), Real.exp (-q * Real.cosh u) := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
    · exact Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)
    · simpa only [zero_integrand q] using
        (kIntegrand_integrable (0 : ℝ) hq)
    · have hs :
          Function.support (fun u : ℝ => Real.exp (-q * Real.cosh u)) ∩
              Ioi (0 : ℝ) = Ioi 0 := by
        rw [Set.inter_eq_right]
        intro u hu
        rw [Function.mem_support]
        exact (Real.exp_pos _).ne'
      rw [hs, volume_Ioi, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_lt_top
  simpa only [imaginaryOrderK, zero_integrand] using hpos

/-- Every real-order oscillatory integral is dominated by the zero-order one. -/
theorem imaginaryOrderK_abs_le_zero (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |imaginaryOrderK t q| ≤ imaginaryOrderK 0 q := by
  have hmajor : IntegrableOn
      (fun u : ℝ => Real.exp (-q * Real.cosh u)) (Ioi 0) := by
    simpa only [zero_integrand q] using
      (kIntegrand_integrable (0 : ℝ) hq)
  have hpoint : ∀ u : ℝ,
      ‖kIntegrand t q u‖ ≤ Real.exp (-q * Real.cosh u) := by
    intro u
    calc
      ‖kIntegrand t q u‖ =
          Real.exp (-q * Real.cosh u) * |Real.cos (2*t*u)| := by
        simp only [kIntegrand, Real.norm_eq_abs, abs_mul,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-q * Real.cosh u) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ = Real.exp (-q * Real.cosh u) := mul_one _
  calc
    |imaginaryOrderK t q| =
        ‖∫ u in Ioi (0 : ℝ), kIntegrand t q u‖ := by
      rw [Real.norm_eq_abs]
      rfl
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-q * Real.cosh u) :=
      norm_integral_le_of_norm_le hmajor
        (Filter.Eventually.of_forall hpoint)
    _ = imaginaryOrderK 0 q := by
      simp only [imaginaryOrderK, zero_integrand]

/-- Increasing the positive argument decreases the zero-order integral. -/
theorem imaginaryOrderK_zero_antitone {q₁ q₂ : ℝ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (h12 : q₁ ≤ q₂) :
    imaginaryOrderK 0 q₂ ≤ imaginaryOrderK 0 q₁ := by
  have hpoint : ∀ u : ℝ,
      Real.exp (-q₂ * Real.cosh u) ≤
        Real.exp (-q₁ * Real.cosh u) := by
    intro u
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right h12 (Real.cosh_pos u).le
    nlinarith
  have hmono :
      (∫ u in Ioi (0 : ℝ), Real.exp (-q₂ * Real.cosh u)) ≤
        ∫ u in Ioi (0 : ℝ), Real.exp (-q₁ * Real.cosh u) := by
    apply integral_mono
    · simpa only [zero_integrand q₂] using
        (kIntegrand_integrable (0 : ℝ) hq₂)
    · simpa only [zero_integrand q₁] using
        (kIntegrand_integrable (0 : ℝ) hq₁)
    · exact hpoint
  simpa only [imaginaryOrderK, zero_integrand] using hmono

end
end ImbalancedChen.Part3.ImaginaryOrderKZeroOrderPositivitySourceOnly
