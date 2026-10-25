import ImbalancedChen.Part3ActualGreenCompactOrderMajorant
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Liouville

/-!
# Interior holomorphy of the literal compact-forcing I/K Green pairing

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The derivative majorant is obtained from the actual compact-order majorant
by the Cauchy estimate on a smaller disc. Measurability of the parameter
derivative is derived from measurable nonzero difference quotients.
Differentiation under the product-measure integral then proves holomorphy.
The final actual theorem assumes only continuous compact forcing; it has
no hNormal, hAnalytic, inverse-equality, boundary-limit or spectral premise.
-/

namespace ImbalancedChen.Part3.ActualGreenPairingHolomorphy20261025a

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology BigOperators
open GeneralActualRadialGreenSourceOnly ActualGreenCompactForcing20261025a
open ActualGreenCompactOrderMajorant20261025a

/-- A derivative section is a genuine measurable limit of difference
quotients, so no derivative-measurability supplier is assumed. -/
private theorem derivative_section_aestronglyMeasurable
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (F : ℂ → X → ℂ) (nu0 : ℂ) (r : ℝ) (hr : 0 < r)
    (hmeas : ∀ nu ∈ closedBall nu0 (2 * r), AEStronglyMeasurable (F nu) mu)
    (hdiff : ∀ x : X, DifferentiableAt ℂ (fun nu => F nu x) nu0) :
    AEStronglyMeasurable (fun x => deriv (fun nu => F nu x) nu0) mu := by
  let delta : ℕ → ℂ := fun n => ((r / ((n : ℝ) + 2) : ℝ) : ℂ)
  have hden (n : ℕ) : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hdeltaPos (n : ℕ) : 0 < r / ((n : ℝ) + 2) := div_pos hr (hden n)
  have hdeltaLe (n : ℕ) : r / ((n : ℝ) + 2) ≤ r := by
    apply (div_le_iff₀ (hden n)).mpr
    nlinarith only [Nat.cast_nonneg n, hr]
  have hpoint (n : ℕ) : nu0 + delta n ∈ closedBall nu0 (2 * r) := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    have heq : ‖delta n‖ = r / ((n : ℝ) + 2) := by
      simp only [delta, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hdeltaPos n)]
    rw [heq]
    linarith only [hdeltaLe n, hr]
  have hzero : nu0 ∈ closedBall nu0 (2 * r) := mem_closedBall_self (by positivity)
  have hreal : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.add_const 2).const_div_atTop r
  have hdelta : Tendsto delta atTop (nhds (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hdeltaNE : Tendsto delta atTop (nhdsWithin (0 : ℂ) {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hdelta, Eventually.of_forall (fun n => ?_)⟩
    change delta n ≠ 0
    exact Complex.ofReal_ne_zero.mpr (hdeltaPos n).ne'
  let Q : ℕ → X → ℂ := fun n x => (delta n)⁻¹ * (F (nu0 + delta n) x - F nu0 x)
  have hQ (n : ℕ) : AEStronglyMeasurable (Q n) mu :=
    aestronglyMeasurable_const.mul ((hmeas _ (hpoint n)).sub (hmeas _ hzero))
  have hlim : ∀ᵐ x ∂mu, Tendsto (fun n => Q n x) atTop
      (nhds (deriv (fun nu => F nu x) nu0)) := by
    apply Eventually.of_forall
    intro x
    simpa only [Q, smul_eq_mul, Function.comp_def] using
      (hdiff x).hasDerivAt.tendsto_slope_zero.comp hdeltaNE
  exact aestronglyMeasurable_of_tendsto_ae atTop hQ hlim

/-- Compact local domination of a pointwise analytic integrand implies
complex differentiability of its actual integral. The Cauchy derivative
bound and derivative measurability are both proved inside this lemma. -/
private theorem differentiableAt_integral_of_compact_order_majorant
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (F : ℂ → X → ℂ) (nu0 : ℂ) (r : ℝ) (hr : 0 < r)
    (hmeas : ∀ nu ∈ closedBall nu0 (2 * r), AEStronglyMeasurable (F nu) mu)
    (hanalytic : ∀ x : X, ∀ nu ∈ closedBall nu0 (2 * r),
      AnalyticAt ℂ (fun z => F z x) nu)
    (bound : X → ℝ) (hboundInt : Integrable bound mu)
    (hbound : ∀ nu ∈ closedBall nu0 (2 * r), ∀ x : X, ‖F nu x‖ ≤ bound x) :
    DifferentiableAt ℂ (fun nu => ∫ x, F nu x ∂mu) nu0 := by
  have hzero : nu0 ∈ closedBall nu0 (2 * r) := mem_closedBall_self (by positivity)
  have hsmall : ball nu0 r ⊆ closedBall nu0 (2 * r) := by
    intro z hz
    apply mem_closedBall.mpr
    exact (mem_ball.mp hz).le.trans (by linarith only [hr])
  have hFint : Integrable (F nu0) mu :=
    hboundInt.mono' (hmeas nu0 hzero) (Eventually.of_forall (hbound nu0 hzero))
  have hFmeas : ∀ᶠ nu in nhds nu0, AEStronglyMeasurable (F nu) mu := by
    filter_upwards [ball_mem_nhds nu0 hr] with nu hnu
    exact hmeas nu (hsmall hnu)
  have hderivMeas : AEStronglyMeasurable (fun x => deriv (fun nu => F nu x) nu0) mu :=
    derivative_section_aestronglyMeasurable mu F nu0 r hr hmeas
      (fun x => (hanalytic x nu0 hzero).differentiableAt)
  have hderivBound : ∀ᵐ x ∂mu, ∀ nu ∈ ball nu0 r,
      ‖deriv (fun z => F z x) nu‖ ≤ bound x / r := by
    apply Eventually.of_forall
    intro x nu hnu
    have hdisc : closedBall nu r ⊆ closedBall nu0 (2 * r) := by
      intro z hz
      apply mem_closedBall.mpr
      have hdist := dist_triangle z nu nu0
      have hz' := mem_closedBall.mp hz
      have hnu' := mem_ball.mp hnu
      linarith only [hdist, hz', hnu']
    have hDiff : DifferentiableOn ℂ (fun z => F z x) (closedBall nu0 (2 * r)) :=
      fun z hz => (hanalytic x z hz).differentiableAt.differentiableWithinAt
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hDiff.diffContOnCl_ball hdisc)
      (fun z hz => hbound z (hdisc (sphere_subset_closedBall hz)) x)
  have hderivInt : Integrable (fun x => bound x / r) mu := hboundInt.div_const r
  have hdiff : ∀ᵐ x ∂mu, ∀ nu ∈ ball nu0 r,
      HasDerivAt (fun z => F z x) (deriv (fun z => F z x) nu) nu := by
    exact Eventually.of_forall (fun x nu hnu =>
      (hanalytic x nu (hsmall hnu)).differentiableAt.hasDerivAt)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun nu x => deriv (fun z => F z x) nu)
    (bound := fun x => bound x / r) (ball_mem_nhds nu0 hr)
    hFmeas hFint hderivMeas hderivBound hderivInt hdiff).2.differentiableAt

/-- Literal product-measure Green pairing. The two spatial integrations
and the full actual I/K kernel are retained in its definition. -/
def actualGreenPairing (f g : ℝ → ℂ) (nu : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, actualRadialGreen nu p.1 p.2 * f p.1 * g p.2
    ∂((volume : Measure ℝ).prod volume)

theorem actualGreenPairing_eq_greenForcing {nu : ℂ} (hnu : -1 < nu.re)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    actualGreenPairing f g nu = ∫ r : ℝ, greenForcing nu f r * g r := by
  unfold actualGreenPairing
  rw [integral_prod_symm _ (jointGreen_integrable hnu hf hg hfc hgc)]
  simp only [greenForcing, integral_mul_const]

/-- Actual compact-forcing Green holomorphy on the full open interior strip.
All domination and pointwise analyticity inputs are supplied by the literal
I-series/K-integral sources. No such input is a caller premise. -/
theorem analyticOnNhd_actualGreenPairing
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    AnalyticOnNhd ℂ (actualGreenPairing f g) interiorOrderStrip := by
  have hdiff : DifferentiableOn ℂ (actualGreenPairing f g) interiorOrderStrip := by
    intro nu0 hnu0
    obtain ⟨delta, hdelta, hdeltaSub⟩ :=
      Metric.mem_nhds_iff.mp (isOpen_interiorOrderStrip.mem_nhds hnu0)
    let r : ℝ := delta / 4
    have hr : 0 < r := by dsimp only [r]; positivity
    have hS : closedBall nu0 (2 * r) ⊆ interiorOrderStrip := by
      intro z hz
      apply hdeltaSub
      apply mem_ball.mpr
      have hh := mem_closedBall.mp hz
      dsimp only [r] at hh
      linarith only [hh, hdelta]
    obtain ⟨bound, hboundInt, hbound⟩ :=
      exists_actualGreen_forcing_integrable_majorant
        (closedBall nu0 (2 * r)) (isCompact_closedBall _ _) hS hf hg hfc hgc
    have hmeas : ∀ nu ∈ closedBall nu0 (2 * r),
        AEStronglyMeasurable (fun p : ℝ × ℝ =>
          actualRadialGreen nu p.1 p.2 * f p.1 * g p.2)
          ((volume : Measure ℝ).prod volume) := by
      intro nu hnu
      have hi : -1 < nu.re := by have := (hS hnu).1; linarith
      exact (jointGreen_integrable hi hf hg hfc hgc).aestronglyMeasurable
    have hpoint : ∀ p : ℝ × ℝ, ∀ nu ∈ closedBall nu0 (2 * r),
        AnalyticAt ℂ (fun z => actualRadialGreen z p.1 p.2 * f p.1 * g p.2) nu := by
      intro p nu hnu
      have hi : -1 < nu.re := by have := (hS hnu).1; linarith
      exact ((actualGreen_analyticAt_order hi p.1 p.2).mul analyticAt_const).mul analyticAt_const
    exact (differentiableAt_integral_of_compact_order_majorant
      ((volume : Measure ℝ).prod volume)
      (fun nu p => actualRadialGreen nu p.1 p.2 * f p.1 * g p.2)
      nu0 r hr hmeas hpoint bound hboundInt hbound).differentiableWithinAt
  intro nu hnu
  exact hdiff.analyticAt (isOpen_interiorOrderStrip.mem_nhds hnu)

/-- The iterated forcing/test pairing has the same proved holomorphy. -/
theorem analyticOnNhd_greenForcing_pairing
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    AnalyticOnNhd ℂ (fun nu => ∫ r : ℝ, greenForcing nu f r * g r) interiorOrderStrip := by
  apply AnalyticOnNhd.congr isOpen_interiorOrderStrip
    (analyticOnNhd_actualGreenPairing hf hg hfc hgc)
  intro nu hnu
  have hi : -1 < nu.re := by have := hnu.1; linarith
  exact actualGreenPairing_eq_greenForcing hi hf hg hfc hgc

end
end ImbalancedChen.Part3.ActualGreenPairingHolomorphy20261025a
