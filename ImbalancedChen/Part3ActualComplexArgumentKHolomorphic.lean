import ImbalancedChen.Part3ActualComplexArgumentKLaplace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual differentiation in the new complex argument z. A half-plane
neighborhood Re(w)>Re(z)/2 and the proved integrable derivative-moment
envelope justify differentiation under the literal K integral. Every
argument moment has derivative the next moment. Complex holomorphy on
Re(z)>0 follows from those proved derivatives, not from a continuation
assumption. The first K derivative is displayed as its actual integral.

No continuation beyond the right half-plane or large-sector Macdonald
formula is claimed here.
-/

namespace ImbalancedChen.Part3.ActualComplexArgumentKHolomorphic20261026b

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ActualComplexArgumentKLaplace20261026b
open RealOrderKPositiveLaplace (tiltedCoshDensity)

/-- The actual pointwise complex derivative in the argument, for every
complex order and every hyperbolic integration variable. -/
theorem argumentMomentIntegrand_hasDerivAt (k : ℕ) (nu z : ℂ) (u : ℝ) :
    HasDerivAt (fun w : ℂ => argumentMomentIntegrand k nu w u)
      (argumentMomentIntegrand (k + 1) nu z u) z := by
  have hm : HasDerivAt (fun w : ℂ => -w * (Real.cosh u : ℂ))
      (-(Real.cosh u : ℂ)) z := by
    simpa using ((hasDerivAt_id z).neg.mul_const (Real.cosh u : ℂ))
  have hd := hm.cexp
  convert (hd.const_mul ((-(Real.cosh u : ℂ)) ^ k)).mul_const
    (Complex.cosh (nu * (u : ℂ))) using 1 <;>
    dsimp only [argumentMomentIntegrand] <;> simp only [pow_succ] <;> ring

/-- Dominated complex differentiation of every actual moment throughout
Re(z)>0, using an actual integrable envelope on a neighborhood of z. -/
theorem argumentMoment_hasDerivAt (k : ℕ) (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (argumentMoment k nu) (argumentMoment (k + 1) nu z) z := by
  let a : ℝ := z.re / 2
  let S : Set ℂ := {w | a < w.re}
  let bound : ℝ → ℝ := tiltedCoshDensity (((k + 1 : ℕ) : ℝ) + |nu.re|) a
  have ha : 0 < a := by dsimp [a]; linarith
  have hSopen : IsOpen S := isOpen_lt continuous_const Complex.continuous_re
  have hS : S ∈ 𝓝 z := hSopen.mem_nhds (by dsimp [S, a]; linarith)
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (argumentMomentIntegrand k nu w)
      (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun w => (argumentMomentIntegrand_continuous k nu w).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (argumentMomentIntegrand (k + 1) nu z)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (argumentMoment_integrable (k + 1) nu hz).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ S,
      ‖argumentMomentIntegrand (k + 1) nu w u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    exact argumentMomentIntegrand_norm_le (k + 1) hw.le le_rfl hu.le
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ S,
      HasDerivAt (fun x : ℂ => argumentMomentIntegrand k nu x u)
        (argumentMomentIntegrand (k + 1) nu w u) w :=
    Eventually.of_forall fun u w _ => argumentMomentIntegrand_hasDerivAt k nu w u
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w u => argumentMomentIntegrand k nu w u)
    (F' := fun w u => argumentMomentIntegrand (k + 1) nu w u)
    (bound := bound) hS hFmeas (argumentMoment_integrable k nu hz) hF'meas
    hbound (argumentMomentEnvelope_integrable (k + 1) |nu.re| ha) hdiff).2

theorem rightHalfPlane_isOpen : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem argumentMoment_differentiableOn (k : ℕ) (nu : ℂ) :
    DifferentiableOn ℂ (argumentMoment k nu) rightHalfPlane := by
  intro z hz
  exact (argumentMoment_hasDerivAt k nu hz).differentiableAt.differentiableWithinAt

/-- Actual holomorphy, obtained from the dominated complex derivatives. -/
theorem argumentMoment_analyticOnNhd (k : ℕ) (nu : ℂ) :
    AnalyticOnNhd ℂ (argumentMoment k nu) rightHalfPlane :=
  (argumentMoment_differentiableOn k nu).analyticOnNhd rightHalfPlane_isOpen

theorem complexArgumentK_analyticOnNhd (nu : ℂ) :
    AnalyticOnNhd ℂ (complexArgumentK nu) rightHalfPlane :=
  argumentMoment_analyticOnNhd 0 nu

theorem complexArgumentK_hasDerivAt (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (complexArgumentK nu) (argumentMoment 1 nu z) z := by
  exact argumentMoment_hasDerivAt 0 nu hz

/-- The first derivative is a proved actual hyperbolic integral. -/
theorem complexArgumentK_derivative_integral (nu : ℂ) {z : ℂ} (hz : 0 < z.re) :
    deriv (complexArgumentK nu) z = ∫ u in Ioi (0 : ℝ),
      (-(Real.cosh u : ℂ)) * Complex.exp (-z * (Real.cosh u : ℂ)) *
        Complex.cosh (nu * (u : ℂ)) := by
  rw [(complexArgumentK_hasDerivAt nu hz).deriv]
  simp only [argumentMoment, argumentMomentIntegrand, pow_one]

end
end ImbalancedChen.Part3.ActualComplexArgumentKHolomorphic20261026b
