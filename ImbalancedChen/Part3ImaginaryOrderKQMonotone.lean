import ImbalancedChen.Part3ImaginaryOrderKZeroOrderPositivity
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
Strengthen zero-order antitonicity to strict monotonicity, and use the
nonnegative difference of the actual exponential weights to control q
perturbations uniformly in the real order t. The predecessor import names
the future installed module from this draft directory.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKQMonotoneSourceOnly
noncomputable section
open Set MeasureTheory Filter
open ImaginaryOrderKBesselSourceOnly

private def zeroWeight (q u : ℝ) : ℝ := Real.exp (-q * Real.cosh u)
private def weightGap (q₁ q₂ u : ℝ) : ℝ := zeroWeight q₁ u - zeroWeight q₂ u

private lemma zeroWeight_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (zeroWeight q) (Ioi (0 : ℝ)) := by
  simpa [zeroWeight, kIntegrand] using
    (kIntegrand_integrable (0 : ℝ) hq)

private lemma zeroWeight_integral (q : ℝ) :
    (∫ u in Ioi (0 : ℝ), zeroWeight q u) = imaginaryOrderK 0 q := by
  simp [zeroWeight, imaginaryOrderK, kIntegrand]

private lemma weightGap_integrable {q₁ q₂ : ℝ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    IntegrableOn (weightGap q₁ q₂) (Ioi (0 : ℝ)) :=
  (zeroWeight_integrable hq₁).sub (zeroWeight_integrable hq₂)

private lemma weightGap_pos {q₁ q₂ : ℝ} (h12 : q₁ < q₂) (u : ℝ) :
    0 < weightGap q₁ q₂ u := by
  have hm : q₁ * Real.cosh u < q₂ * Real.cosh u :=
    mul_lt_mul_of_pos_right h12 (Real.cosh_pos u)
  exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith :
    -q₂ * Real.cosh u < -q₁ * Real.cosh u))

private lemma weightGap_integral {q₁ q₂ : ℝ}
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (∫ u in Ioi (0 : ℝ), weightGap q₁ q₂ u) =
      imaginaryOrderK 0 q₁ - imaginaryOrderK 0 q₂ := by
  calc
    (∫ u in Ioi (0 : ℝ), weightGap q₁ q₂ u) =
        (∫ u in Ioi (0 : ℝ), zeroWeight q₁ u) -
          ∫ u in Ioi (0 : ℝ), zeroWeight q₂ u := by
      exact integral_sub (zeroWeight_integrable hq₁)
        (zeroWeight_integrable hq₂)
    _ = imaginaryOrderK 0 q₁ - imaginaryOrderK 0 q₂ := by
      rw [zeroWeight_integral, zeroWeight_integral]

/-- Strict decrease of the actual zero-order integral on the positive axis. -/
theorem imaginaryOrderK_zero_strictAnti {q₁ q₂ : ℝ}
    (hq₁ : 0 < q₁) (h12 : q₁ < q₂) :
    imaginaryOrderK 0 q₂ < imaginaryOrderK 0 q₁ := by
  have hq₂ : 0 < q₂ := lt_trans hq₁ h12
  have hpos : 0 < ∫ u in Ioi (0 : ℝ), weightGap q₁ q₂ u := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).2 ?_
    · exact Filter.Eventually.of_forall
        (fun u => (weightGap_pos h12 u).le)
    · exact weightGap_integrable hq₁ hq₂
    · have hs : Function.support (weightGap q₁ q₂) ∩ Ioi (0 : ℝ) = Ioi 0 := by
        rw [Set.inter_eq_right]
        intro u hu
        rw [Function.mem_support]
        exact (weightGap_pos h12 u).ne'
      rw [hs, volume_Ioi, ← ENNReal.ofReal_zero]
      exact ENNReal.ofReal_lt_top
  rw [weightGap_integral hq₁ hq₂] at hpos
  exact sub_pos.mp hpos

/-- A q perturbation is bounded by the zero-order loss, uniformly in t. -/
theorem imaginaryOrderK_q_diff_abs_le_zero_gap (t : ℝ)
    {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (h12 : q₁ < q₂) :
    |imaginaryOrderK t q₁ - imaginaryOrderK t q₂| ≤
      imaginaryOrderK 0 q₁ - imaginaryOrderK 0 q₂ := by
  have hq₂ : 0 < q₂ := lt_trans hq₁ h12
  have hpoint : ∀ u : ℝ,
      ‖kIntegrand t q₁ u - kIntegrand t q₂ u‖ ≤
        weightGap q₁ q₂ u := by
    intro u
    have hfactor : kIntegrand t q₁ u - kIntegrand t q₂ u =
        weightGap q₁ q₂ u * Real.cos (2*t*u) := by
      unfold kIntegrand weightGap zeroWeight
      ring
    calc
      ‖kIntegrand t q₁ u - kIntegrand t q₂ u‖ =
          weightGap q₁ q₂ u * |Real.cos (2*t*u)| := by
        rw [hfactor, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (weightGap_pos h12 u).le]
      _ ≤ weightGap q₁ q₂ u * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
          (weightGap_pos h12 u).le
      _ = weightGap q₁ q₂ u := mul_one _
  have hdiff :
      (∫ u in Ioi (0 : ℝ),
          (kIntegrand t q₁ u - kIntegrand t q₂ u)) =
        imaginaryOrderK t q₁ - imaginaryOrderK t q₂ := by
    rw [integral_sub (kIntegrand_integrable t hq₁)
      (kIntegrand_integrable t hq₂)]
    rfl
  calc
    |imaginaryOrderK t q₁ - imaginaryOrderK t q₂| =
        ‖∫ u in Ioi (0 : ℝ),
          (kIntegrand t q₁ u - kIntegrand t q₂ u)‖ := by
      rw [hdiff, Real.norm_eq_abs]
    _ ≤ ∫ u in Ioi (0 : ℝ), weightGap q₁ q₂ u :=
      norm_integral_le_of_norm_le (weightGap_integrable hq₁ hq₂)
        (Filter.Eventually.of_forall hpoint)
    _ = imaginaryOrderK 0 q₁ - imaginaryOrderK 0 q₂ :=
      weightGap_integral hq₁ hq₂

/-- The explicit right-side bound tends to zero at each positive q. -/
theorem imaginaryOrderK_zero_right_gap_tendsto (q : ℝ) (hq : 0 < q) :
    Tendsto
      (fun r : Ici q => imaginaryOrderK 0 q - imaginaryOrderK 0 (r : ℝ))
      (𝓝 (⟨q, le_rfl⟩ : Ici q)) (𝓝 0) := by
  have hpair : Continuous (fun r : Ici q => ((0 : ℝ), r)) := by fun_prop
  have hc : Continuous (fun r : Ici q => imaginaryOrderK 0 (r : ℝ)) :=
    (imaginaryOrderK_joint_continuous q hq).comp hpair
  have hgap : Continuous
      (fun r : Ici q => imaginaryOrderK 0 q - imaginaryOrderK 0 (r : ℝ)) :=
    continuous_const.sub hc
  simpa using
    (hgap.continuousAt (x := (⟨q, le_rfl⟩ : Ici q))).tendsto

end
end ImbalancedChen.Part3.ImaginaryOrderKQMonotoneSourceOnly
