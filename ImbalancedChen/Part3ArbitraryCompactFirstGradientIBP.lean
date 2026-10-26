import ImbalancedChen.Part3OneCompactFirstGradientIBP
import ImbalancedChen.Part3CompactC2ProductMollifier
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

First-order integration by parts for EVERY compact smooth positive-height
plane test against a noncompact function smooth only on the positive chart.
The derivative is the actual real Frechet derivative in either coordinate.
Every product is independently integrable, using compact support inside
the chart. Native real integration by parts requires differentiability of
the noncompact function only on the test's support. Canonical hyperbolic
volume is then transported with its exact y-squared cancellation.
-/

namespace ImbalancedChen.Part3.ArbitraryCompactFirstGradientIBP20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactGreenProductL120261025a
open OneCompactFirstGradientIBP20261025a
open CompactC2ProductMollifier20261026a
open CanonicalTensorHyperbolicLaplacianForm20261024z

def coordinateDirection (vertical : Bool) : Plane := if vertical then ey else ex

theorem compact_chart_product_integrable {ψ : Plane → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) {G : Plane → ℂ}
    (hG : ContinuousOn G positiveChart) :
    Integrable (fun p => star (ψ p) * G p) (volume : Measure Plane) := by
  have hcont : ContinuousOn (fun p => star (ψ p) * G p) (tsupport ψ) :=
    hψ.star.continuousOn.mul (hG.mono hs)
  have hsupport : Function.support (fun p => star (ψ p) * G p) ⊆ tsupport ψ := by
    intro p hp
    by_contra hn
    exact hp (by simp only [image_eq_zero_of_notMem_tsupport hn, star_zero, zero_mul])
  exact (integrableOn_iff_integrable_of_support_subset hsupport).mp
    (ContinuousOn.integrableOn_compact hc hcont)

theorem directional_continuousOn (v : Plane) {G : Plane → ℂ}
    (hG : ContDiffOn ℝ 2 G positiveChart) :
    ContinuousOn (directional v G) positiveChart := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ G) positiveChart :=
    hG.fderiv_of_isOpen positiveChart_isOpen (by norm_num)
  exact (hd.clm_apply contDiffOn_const).continuousOn

theorem arbitrary_compact_first_products_integrable (v : Plane)
    {ψ G : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hG : ContDiffOn ℝ 2 G positiveChart) :
    Integrable (fun p => star (directional v ψ p) * G p) volume ∧
    Integrable (fun p => star (ψ p) * directional v G p) volume ∧
    Integrable (fun p => star (ψ p) * G p) volume := by
  refine ⟨?_, ?_, compact_chart_product_integrable hψ.continuous hc hs hG.continuousOn⟩
  · exact compact_chart_product_integrable (directional_smooth v hψ).continuous
      (directional_compact v hc) ((tsupport_fderiv_apply_subset ℝ v).trans hs)
      hG.continuousOn
  · exact compact_chart_product_integrable hψ.continuous hc hs
      (directional_continuousOn v hG)

theorem plane_arbitrary_compact_first (v : Plane) {ψ G : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ p : Plane, star (directional v ψ p) * G p) =
      -(∫ p : Plane, star (ψ p) * directional v G p) := by
  obtain ⟨h₁, h₂, h₀⟩ := arbitrary_compact_first_products_integrable v hψ hc hs hG
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hdG : DifferentiableOn ℝ G positiveChart := hG.differentiableOn (by norm_num)
  have hstar : tsupport (fun p => star (ψ p)) ⊆ tsupport ψ :=
    tsupport_comp_subset rfl ψ
  have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Plane)) (f := fun p => star (ψ p)) (g := G) (v := v)
    (by simpa [directional] using h₁) (by simpa only [directional] using h₂) h₀
    (fun p _ => (hdψ p).star)
    (fun p hp => (hdG p (hs (hstar hp))).differentiableAt
      (positiveChart_isOpen.mem_nhds (hs (hstar hp))))
  have hb' : (∫ p : Plane, star (ψ p) * directional v G p) =
      -(∫ p : Plane, star (directional v ψ p) * G p) := by
    simpa [directional] using hb
  simpa only [neg_neg] using congrArg Neg.neg hb'.symm

theorem sliceFirst_eq_directional (vertical : Bool) {G : Plane → ℂ}
    (hG : DifferentiableOn ℝ G positiveChart) {p : Plane} (hp : p ∈ positiveChart) :
    sliceFirst vertical G p = directional (coordinateDirection vertical) G p := by
  cases vertical
  · exact sliceDx_eq_fderiv G hG hp
  · exact sliceDy_eq_fderiv G hG hp

/-- Genuine real-coordinate integration by parts for an arbitrary compact
test, with the literal canonical y^-2 volume and exactly the y² weights. -/
theorem canonical_arbitrary_compact_first (vertical : Bool) {ψ G : Plane → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hG : ContDiffOn ℝ 2 G positiveChart) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^2 *
      (star (directional (coordinateDirection vertical) ψ (z.re,z.im)) * G (z.re,z.im))) =
      -(∫ z : UpperHalfPlane, (z.im : ℂ)^2 *
        (star (ψ (z.re,z.im)) * sliceFirst vertical G (z.re,z.im))) := by
  have hψzero (p : Plane) (hp : p ∉ upperChart) : ψ p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht))
  have hdzero (p : Plane) (hp : p ∉ upperChart) :
      directional (coordinateDirection vertical) ψ p = 0 := by
    have hn : p ∉ tsupport ψ := fun ht => hp (hs ht)
    simp only [directional, fderiv_of_notMem_tsupport ℝ hn,
      ContinuousLinearMap.zero_apply]
  calc
    _ = ∫ p : Plane, star (directional (coordinateDirection vertical) ψ p) * G p :=
      canonical_ySq_integral _ (fun p hp => by rw [hdzero p hp, star_zero, zero_mul])
    _ = -(∫ p : Plane, star (ψ p) * directional (coordinateDirection vertical) G p) :=
      plane_arbitrary_compact_first _ hψ hc hs hG
    _ = -(∫ z : UpperHalfPlane, (z.im : ℂ)^2 *
        (star (ψ (z.re,z.im)) * directional (coordinateDirection vertical) G (z.re,z.im))) := by
      rw [canonical_ySq_integral _ (fun p hp => by rw [hψzero p hp, star_zero, zero_mul])]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        rw [sliceFirst_eq_directional vertical (hG.differentiableOn (by norm_num)) z.im_pos])

end
end ImbalancedChen.Part3.ArbitraryCompactFirstGradientIBP20261026b
