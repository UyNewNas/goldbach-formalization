import ImbalancedChen.Part3ActualMacdonaldPrintedCompactL1
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual separate parameter holomorphy of the inherited-sheet Macdonald
t-integral on the printed slit/sum-quarter domain in the small order
strip. The literal cover/log chain gives the actual kernel derivative.
Its integration-variable measurability follows from the entire cover
and its actual analytic derivative. A common compact L1 bound on a
larger parameter disc, together with the genuine Cauchy derivative
estimate on smaller discs, dominates these actual derivatives by g/a.
Dominated complex differentiation proves the integral derivative. No
parameter holomorphy or continuation identity is a supplied hypothesis.
-/

namespace ImbalancedChen.Part3.ActualMacdonaldPrintedHolomorphic20261026b

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualLogCoverKModel20261026b ActualMacdonaldProductDetermination20261026b
open ActualMacdonaldPositiveProductSheet20261026b ActualMacdonaldPrintedCompactL120261026b

def printedMacdonaldSlice (w : ℂ) : Set ℂ := {z | (z, w) ∈ printedMacdonaldDomain}

def inheritedMacdonaldValue (nu z w : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), inheritedMacdonaldKernel nu z w t

def inheritedMacdonaldZDerivative (nu z w : ℂ) (t : ℝ) : ℂ :=
  ((t⁻¹ : ℝ) : ℂ) *
    Complex.exp (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ)) *
      ((-(2 * z) * ((1 / (2 * t) : ℝ) : ℂ)) * determinedProductK nu z w t +
        deriv (logCoverK nu) (productHalfLog z w t) * z⁻¹)

theorem printedMacdonaldSlice_isOpen (w : ℂ) : IsOpen (printedMacdonaldSlice w) :=
  printedMacdonaldDomain_isOpen.preimage (continuous_id.prodMk continuous_const)

theorem printedMacdonaldDomain_swap {z w : ℂ} (h : (z, w) ∈ printedMacdonaldDomain) :
    (w, z) ∈ printedMacdonaldDomain := by
  refine ⟨h.2.1, h.1, ?_⟩
  simpa only [add_comm] using h.2.2

theorem inheritedMacdonaldKernel_hasDerivAt_left {nu z : ℂ}
    (hL : -1 < nu.re) (hU : nu.re < 1) (hz : z ∈ Complex.slitPlane) (w : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℂ => inheritedMacdonaldKernel nu x w t)
      (inheritedMacdonaldZDerivative nu z w t) z := by
  have hs : HasDerivAt (fun x : ℂ => x ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_id z).pow 2
  have he := (hasDerivAt_const z (((-t / 2 : ℝ) : ℂ))).sub
    ((hs.add_const (w ^ 2)).mul_const ((1 / (2 * t) : ℝ) : ℂ))
  have hlog : HasDerivAt (fun x : ℂ => productHalfLog x w t) z⁻¹ z :=
    ((Complex.hasDerivAt_log hz).add_const (Complex.log w)).sub_const (Real.log (2 * t) : ℂ)
  have hk := (((logCoverK_analyticOnNhd hL hU) (productHalfLog z w t) (mem_univ _)).differentiableAt.hasDerivAt).comp z hlog
  convert ((he.cexp).const_mul ((t⁻¹ : ℝ) : ℂ)).mul hk using 1 <;>
    unfold inheritedMacdonaldKernel inheritedMacdonaldZDerivative determinedProductK <;> ring

theorem inheritedMacdonaldZDerivative_measurable {nu : ℂ}
    (hL : -1 < nu.re) (hU : nu.re < 1) (z w : ℂ) :
    Measurable (inheritedMacdonaldZDerivative nu z w) := by
  have hcover := logCoverK_analyticOnNhd hL hU
  have hc : Continuous (logCoverK nu) := continuous_iff_continuousAt.mpr
    (fun L => (hcover L (mem_univ _)).continuousAt)
  have hd : Continuous (deriv (logCoverK nu)) := continuous_iff_continuousAt.mpr
    (fun L => (hcover.deriv L (mem_univ _)).continuousAt)
  have hlog : Measurable (fun t : ℝ => productHalfLog z w t) := by
    unfold productHalfLog
    fun_prop
  have hK : Measurable (fun t : ℝ => determinedProductK nu z w t) := hc.measurable.comp hlog
  have hD : Measurable (fun t : ℝ => deriv (logCoverK nu) (productHalfLog z w t)) :=
    hd.measurable.comp hlog
  have hfactor : Measurable (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) *
      Complex.exp (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ))) := by
    fun_prop
  have hcoef : Measurable (fun t : ℝ => -(2 * z) * ((1 / (2 * t) : ℝ) : ℂ)) := by fun_prop
  exact hfactor.mul ((hcoef.mul hK).add (hD.mul_const z⁻¹))

/-- The actual derivative of the original inherited t-integral. Cauchy
domination is proved on a larger compact parameter family, rather than
being supplied as an analytic-envelope input. -/
theorem inheritedMacdonaldValue_hasDerivAt_left {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2)
    {z w : ℂ} (h : (z, w) ∈ printedMacdonaldDomain) :
    HasDerivAt (fun x : ℂ => inheritedMacdonaldValue nu x w)
      ((1 / 2 : ℂ) * ∫ t in Ioi (0 : ℝ), inheritedMacdonaldZDerivative nu z w t) z := by
  have hL : -1 < nu.re := by have hh := (abs_lt.mp horder).1; linarith
  have hU : nu.re < 1 := by have hh := (abs_lt.mp horder).2; linarith
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp (printedMacdonaldSlice_isOpen w) z h
  let a : ℝ := epsilon / 4
  have ha : 0 < a := by dsimp [a]; positivity
  let S : Set (ℂ × ℂ) := (fun x : ℂ => (x, w)) '' closedBall z (2 * a)
  have hS : IsCompact S := (isCompact_closedBall z (2 * a)).image
    (continuous_id.prodMk continuous_const)
  have hlarge : ∀ x ∈ closedBall z (2 * a), (x, w) ∈ printedMacdonaldDomain := by
    intro x hx
    apply hball
    apply mem_ball.mpr
    have hx' := mem_closedBall.mp hx
    dsimp [a] at hx'
    linarith
  have hprinted : S ⊆ printedMacdonaldDomain := by
    rintro p ⟨x, hx, rfl⟩
    exact hlarge x hx
  obtain ⟨g, hg, hdom⟩ := compact_inheritedMacdonaldKernel_majorant horder hr hrhalf hS hprinted
  have hsmall : ∀ x ∈ ball z a, x ∈ closedBall z (2 * a) := by
    intro x hx
    apply mem_closedBall.mpr
    have hx' := mem_ball.mp hx
    linarith
  have hderivBound : ∀ᵐ t : ℝ ∂positiveMeasure, ∀ x ∈ ball z a,
      ‖inheritedMacdonaldZDerivative nu x w t‖ ≤ g t / a := by
    filter_upwards [hdom] with t ht
    intro x hx
    have hsub : closedBall x a ⊆ closedBall z (2 * a) := by
      intro y hy
      apply mem_closedBall.mpr
      have hyx := mem_closedBall.mp hy
      have hxz := mem_ball.mp hx
      have htriangle := dist_triangle y x z
      linarith
    have hd : DifferentiableOn ℂ (fun y : ℂ => inheritedMacdonaldKernel nu y w t)
        (closedBall x a) := by
      intro y hy
      exact (inheritedMacdonaldKernel_hasDerivAt_left hL hU
        (hlarge y (hsub hy)).1 w t).differentiableAt.differentiableWithinAt
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ha
      (hd.diffContOnCl_ball (Subset.refl _))
      (fun y hy => ht (y, w) ⟨y, hsub (sphere_subset_closedBall hy), rfl⟩)
    rw [(inheritedMacdonaldKernel_hasDerivAt_left hL hU (hlarge x (hsmall x hx)).1 w t).deriv]
      at hcauchy
    exact hcauchy
  have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (inheritedMacdonaldKernel nu x w)
      positiveMeasure := Eventually.of_forall fun x =>
    (inheritedMacdonaldKernel_measurable hL hU x w).aestronglyMeasurable
  have hF'meas := (inheritedMacdonaldZDerivative_measurable hL hU z w).aestronglyMeasurable
    (μ := positiveMeasure)
  have hdiff : ∀ᵐ t : ℝ ∂positiveMeasure, ∀ x ∈ ball z a,
      HasDerivAt (fun y : ℂ => inheritedMacdonaldKernel nu y w t)
        (inheritedMacdonaldZDerivative nu x w t) x :=
    Eventually.of_forall fun t x hx =>
      inheritedMacdonaldKernel_hasDerivAt_left hL hU (hlarge x (hsmall x hx)).1 w t
  have hdifferentiation := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := positiveMeasure) (F := fun x t => inheritedMacdonaldKernel nu x w t)
    (F' := fun x t => inheritedMacdonaldZDerivative nu x w t) (bound := fun t => g t / a)
    (ball_mem_nhds z ha) hFmeas (inheritedMacdonaldKernel_integrable horder hr hrhalf h)
    hF'meas hderivBound (hg.div_const a) hdiff).2
  exact hdifferentiation.const_mul (1 / 2 : ℂ)

theorem inheritedMacdonaldKernel_symm (nu z w : ℂ) (t : ℝ) :
    inheritedMacdonaldKernel nu z w t = inheritedMacdonaldKernel nu w z t := by
  have hlog : productHalfLog z w t = productHalfLog w z t := by
    unfold productHalfLog
    ring
  have he : z ^ 2 + w ^ 2 = w ^ 2 + z ^ 2 := add_comm _ _
  simp only [inheritedMacdonaldKernel, determinedProductK, hlog, he]

theorem inheritedMacdonaldValue_symm (nu z w : ℂ) :
    inheritedMacdonaldValue nu z w = inheritedMacdonaldValue nu w z := by
  unfold inheritedMacdonaldValue
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => inheritedMacdonaldKernel_symm nu z w t

theorem inheritedMacdonaldValue_analyticOnNhd_left {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => inheritedMacdonaldValue nu z w) (printedMacdonaldSlice w) := by
  apply DifferentiableOn.analyticOnNhd _ (printedMacdonaldSlice_isOpen w)
  intro z hz
  exact (inheritedMacdonaldValue_hasDerivAt_left horder hr hrhalf hz).differentiableAt.differentiableWithinAt

theorem inheritedMacdonaldValue_analyticOnNhd_right {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w => inheritedMacdonaldValue nu z w) (printedMacdonaldSlice z) := by
  have he : (fun w => inheritedMacdonaldValue nu z w) =
      (fun w => inheritedMacdonaldValue nu w z) := funext (fun w => inheritedMacdonaldValue_symm nu z w)
  rw [he]
  exact inheritedMacdonaldValue_analyticOnNhd_left horder hr hrhalf z

end
end ImbalancedChen.Part3.ActualMacdonaldPrintedHolomorphic20261026b
