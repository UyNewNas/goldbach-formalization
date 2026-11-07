import ImbalancedChen.Part3ActualComplexMacdonaldCombinedL1
import ImbalancedChen.Part3ActualComplexMacdonaldQuarterHolomorphic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual parameter derivatives of the Macdonald double integral on the
combined-damping domain. The already computed polynomial exponent
derivative is dominated using the NEW combined joint bound, rather than
individual square positivity. Absorbing the extra (1+cosh(v))/t factor
uses half of that positive damping. A compact closed parameter disc
supplies the floor and a norm bound; dominated complex differentiation
then proves the actual derivative and separate holomorphy. No analytic
continuation identity or larger-sector asymptotic estimate is assumed.
-/

namespace ImbalancedChen.Part3.ActualComplexMacdonaldCombinedHolomorphic20261026b

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualComplexMacdonaldQuarterL120261026b
open ActualComplexMacdonaldQuarterHolomorphic20261026b
open ActualComplexMacdonaldCombinedL120261026b

/-- The derivative majorant depends on the combined A/B floor, even
when the real part of an individual squared argument is negative. -/
theorem jointZDerivative_norm_le_combined (nu : ℂ) {z w : ℂ} {delta M t : ℝ}
    (hd : 0 < delta) (hM : 0 ≤ M) (hA : delta ≤ ((z + w) ^ 2).re)
    (hB : delta ≤ (z * w).re) (hzM : ‖z‖ ≤ M) (hwM : ‖w‖ ≤ M)
    (ht : 0 < t) (v : ℝ) :
    ‖jointZDerivative nu z w v t‖ ≤
      (M * (8 / delta)) * positiveMacdonaldMajorant nu (delta / 8) v t := by
  have hcoef : ‖z + w * (Real.cosh v : ℂ)‖ ≤ M * (1 + Real.cosh v) := by
    calc
      _ ≤ ‖z‖ + ‖w * (Real.cosh v : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + ‖w‖ * Real.cosh v := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos v)]
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_right hwM (Real.cosh_pos v).le
        nlinarith
  have hJ := complexMacdonaldJoint_norm_le_combined nu hd hA hB ht v
  have hnonneg : 0 ≤ positiveMacdonaldMajorant nu (delta / 4) v t := by
    unfold positiveMacdonaldMajorant
    positivity
  have hhalf : (delta / 4) / 2 = delta / 8 := by ring
  have hfactor : 2 / (delta / 4) = 8 / delta := by field_simp [hd.ne'] <;> ring
  have habsorb := positiveMacdonaldMajorant_linear_bound nu
    (by positivity : 0 < delta / 4) ht v
  rw [hhalf, hfactor] at habsorb
  unfold jointZDerivative
  rw [norm_mul, exponentZDerivative_eq z w ht v, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc
    _ ≤ (M * (1 + Real.cosh v)) * t⁻¹ * positiveMacdonaldMajorant nu (delta / 4) v t :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoef (inv_pos.mpr ht).le) hJ
        (norm_nonneg _) (by positivity)
    _ = M * (((1 + Real.cosh v) / t) * positiveMacdonaldMajorant nu (delta / 4) v t) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ M * ((8 / delta) * positiveMacdonaldMajorant nu (delta / 8) v t) :=
      mul_le_mul_of_nonneg_left habsorb hM
    _ = _ := by ring

theorem complexMacdonaldValue_hasDerivAt_left_combined (nu : ℂ) {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) :
    HasDerivAt (fun x : ℂ => complexMacdonaldValue nu x w)
      ((1 / 2 : ℂ) * ∫ p : ℝ × ℝ, jointZDerivative nu z w p.1 p.2
        ∂positiveMeasure.prod positiveMeasure) z := by
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp (combinedMacdonaldSlice_isOpen w) z h
  let r : ℝ := epsilon / 2
  have hr : 0 < r := half_pos hepsilon
  let S : Set (ℂ × ℂ) := (fun x : ℂ => (x, w)) '' closedBall z r
  have hS : IsCompact S := (isCompact_closedBall z r).image
    (continuous_id.prodMk continuous_const)
  have hcombined : S ⊆ combinedMacdonaldDomain := by
    rintro p ⟨x, hx, rfl⟩
    apply hball
    apply mem_ball.mpr
    have hx' := mem_closedBall.mp hx
    dsimp [r] at hx'
    linarith
  obtain ⟨delta, hd, hfloor⟩ := compact_combined_coefficient_floor hS hcombined
  let M : ℝ := ‖z‖ + ‖w‖ + epsilon + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hwM : ‖w‖ ≤ M := by dsimp [M]; linarith [norm_nonneg z]
  have hxM : ∀ x ∈ ball z r, ‖x‖ ≤ M := by
    intro x hx
    have hdistance : ‖x - z‖ < r := by
      simpa only [dist_eq_norm] using mem_ball.mp hx
    have hnorm : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - z) z
    dsimp [M, r] at *
    linarith [norm_nonneg w]
  have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun p : ℝ × ℝ => complexMacdonaldJoint nu x w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
    apply Eventually.of_forall
    intro x
    have hm : Measurable (fun p : ℝ × ℝ => complexMacdonaldJoint nu x w p.1 p.2) := by
      unfold complexMacdonaldJoint complexMacdonaldExponent
      fun_prop
    exact hm.aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (fun p : ℝ × ℝ => jointZDerivative nu z w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
    have hm : Measurable (fun p : ℝ × ℝ => jointZDerivative nu z w p.1 p.2) := by
      unfold jointZDerivative exponentZDerivative complexMacdonaldJoint complexMacdonaldExponent
      fun_prop
    exact hm.aestronglyMeasurable
  have hbound : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure, ∀ x ∈ ball z r,
      ‖jointZDerivative nu x w p.1 p.2‖ ≤
        (M * (8 / delta)) * positiveMacdonaldMajorant nu (delta / 8) p.1 p.2 := by
    filter_upwards [positive_snd_ae] with p hp
    intro x hx
    rcases hfloor (x, w) ⟨x, mem_closedBall.mpr (mem_ball.mp hx).le, rfl⟩ with ⟨hA, hB⟩
    exact jointZDerivative_norm_le_combined nu hd hM hA hB (hxM x hx) hwM hp p.1
  have hdiff : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure, ∀ x ∈ ball z r,
      HasDerivAt (fun y : ℂ => complexMacdonaldJoint nu y w p.1 p.2)
        (jointZDerivative nu x w p.1 p.2) x :=
    Eventually.of_forall fun p x _ => complexMacdonaldJoint_hasDerivAt nu x w p.1 p.2
  have hdifferentiation := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := positiveMeasure.prod positiveMeasure)
    (F := fun x p => complexMacdonaldJoint nu x w p.1 p.2)
    (F' := fun x p => jointZDerivative nu x w p.1 p.2)
    (bound := fun p => (M * (8 / delta)) * positiveMacdonaldMajorant nu (delta / 8) p.1 p.2)
    (ball_mem_nhds z hr) hFmeas (complexMacdonaldJoint_integrable_combined nu h)
    hF'meas hbound ((positiveMacdonaldMajorant_integrable nu
      (by positivity : 0 < delta / 8)).const_mul _) hdiff).2
  exact hdifferentiation.const_mul (1 / 2 : ℂ)

theorem complexMacdonaldValue_hasDerivAt_right_combined (nu : ℂ) {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) :
    HasDerivAt (fun x : ℂ => complexMacdonaldValue nu z x)
      ((1 / 2 : ℂ) * ∫ p : ℝ × ℝ, jointZDerivative nu w z p.1 p.2
        ∂positiveMeasure.prod positiveMeasure) w := by
  have he : (fun x => complexMacdonaldValue nu z x) =
      (fun x => complexMacdonaldValue nu x z) :=
    funext (fun x => complexMacdonaldValue_symm nu z x)
  rw [he]
  exact complexMacdonaldValue_hasDerivAt_left_combined nu (combinedMacdonaldDomain_swap h)

theorem complexMacdonaldValue_analyticOnNhd_left_combined (nu w : ℂ) :
    AnalyticOnNhd ℂ (fun z => complexMacdonaldValue nu z w) (combinedMacdonaldSlice w) := by
  apply DifferentiableOn.analyticOnNhd _ (combinedMacdonaldSlice_isOpen w)
  intro z hz
  exact (complexMacdonaldValue_hasDerivAt_left_combined nu hz).differentiableAt.differentiableWithinAt

theorem complexMacdonaldValue_analyticOnNhd_right_combined (nu z : ℂ) :
    AnalyticOnNhd ℂ (fun w => complexMacdonaldValue nu z w) (combinedMacdonaldSlice z) := by
  have he : (fun w => complexMacdonaldValue nu z w) =
      (fun w => complexMacdonaldValue nu w z) :=
    funext (fun w => complexMacdonaldValue_symm nu z w)
  rw [he]
  exact complexMacdonaldValue_analyticOnNhd_left_combined nu z

end
end ImbalancedChen.Part3.ActualComplexMacdonaldCombinedHolomorphic20261026b
