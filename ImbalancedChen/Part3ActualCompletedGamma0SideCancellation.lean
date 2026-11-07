import ImbalancedChen.Part3Gamma0PairedEdgeGreenCancellation
import ImbalancedChen.Part3AllLevelContinuedMaass
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual completed all-level Eisenstein fields instantiate the produced
Gamma0 paired-edge cancellation. Their genuine spatial smoothness and
Gamma0 invariance are proved suppliers, not side-current assumptions.
Every C1 compact parameter edge has a continuous, hence integrable,
Green density. Its literal reversed Gamma0 mate has the transported
continuous negative-reverse density. Thus the paired cancellation here
applies to honest integrable actual fields. Fundamental polygon assembly,
quotient Stokes, and spectral completeness remain separate OPEN steps.
-/

noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.Gamma0PairedEdgeGreen20261026b
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo

namespace ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b

/-- A literal complex coordinate extension of the shared actual family. -/
def completedComplexField (N : ℕ) (s : ℂ) (w : ℂ) : ℂ :=
  completedLevelChart N s (w.re, w.im)

theorem completedComplexField_eq_native (N : ℕ) (s : ℂ) (z : UpperHalfPlane) :
    completedComplexField N s z = completedLevelOldform N s z :=
  completedLevelChart_eq_native N s z

theorem completedComplexField_contDiffAt (N : ℕ) (s : ℂ) (z : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (completedComplexField N s) (z : ℂ) := by
  have hp : ContDiffAt ℝ ∞ (completedLevelChart N s) (z.re, z.im) :=
    (completedLevelChart_smooth N s).contDiffAt (upperChart_isOpen.mem_nhds z.im_pos)
  have hcoord : ContDiff ℝ ∞ (fun w : ℂ => (w.re, w.im)) :=
    Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
  exact hp.comp (z : ℂ) hcoord.contDiffAt

theorem completedComplexField_Gamma0_invariant (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : s ∈ completedRegularDomain N)
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    completedComplexField N s ((γ • z : UpperHalfPlane) : ℂ) = completedComplexField N s z := by
  rw [completedComplexField_eq_native, completedComplexField_eq_native]
  exact completedLevelOldform_Gamma0_invariant N hN s hs γ z

/-- Local C1 is sufficient for continuity of the genuine one-form on a
C1 edge; no line-integrability supplier is hidden in the statement. -/
theorem greenOneForm_edge_continuous (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, ContDiffAt ℝ ∞ G (z : ℂ))
    (c : ℝ → UpperHalfPlane) (hc : ContDiff ℝ 1 (fun t : ℝ => (c t : ℂ))) :
    Continuous (fun t : ℝ => greenOneForm F G (c t)
      (deriv (fun r : ℝ => (c r : ℂ)) t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hct : ContinuousAt (fun r : ℝ => (c r : ℂ)) t := hc.continuous.continuousAt
  have hnormal : ContinuousAt (fun r : ℝ => -I * deriv (fun q : ℝ => (c q : ℂ)) r) t :=
    (continuous_const.mul hc.continuous_deriv_one).continuousAt
  have hFv := (hF (c t)).continuousAt.comp t hct
  have hGv := (hG (c t)).continuousAt.comp t hct
  have hFD := ((hF (c t)).continuousAt_fderiv (by simp)).comp t hct
  have hGD := ((hG (c t)).continuousAt_fderiv (by simp)).comp t hct
  have hFn := hFD.clm_apply hnormal
  have hGn := hGD.clm_apply hnormal
  simpa only [greenOneForm, Complex.star_def] using
    (hFv.star.mul hGn).sub (hFn.star.mul hGv)

theorem completedGreen_edge_intervalIntegrable (N : ℕ) (s u : ℂ)
    (c : ℝ → UpperHalfPlane) (hc : ContDiff ℝ 1 (fun t : ℝ => (c t : ℂ))) :
    IntervalIntegrable (fun t : ℝ => greenOneForm (completedComplexField N s)
      (completedComplexField N u) (c t) (deriv (fun r : ℝ => (c r : ℂ)) t)) volume 0 1 :=
  (greenOneForm_edge_continuous _ _ (completedComplexField_contDiffAt N s)
    (completedComplexField_contDiffAt N u) c hc).intervalIntegrable 0 1

theorem completedGreen_paired_density (N : ℕ) (hN : 0 < N)
    (s u : ℂ) (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (γ : CongruenceSubgroup.Gamma0 N) (c : ℝ → UpperHalfPlane)
    (hc : ContDiff ℝ 1 (fun t : ℝ => (c t : ℂ))) (t : ℝ) :
    greenOneForm (completedComplexField N s) (completedComplexField N u) (pairedEdge N γ c t)
      (deriv (fun r : ℝ => (pairedEdge N γ c r : ℂ)) t) =
      -greenOneForm (completedComplexField N s) (completedComplexField N u) (c (1 - t))
        (deriv (fun r : ℝ => (c r : ℂ)) (1 - t)) := by
  let v : ℝ → ℂ := deriv (fun r : ℝ => (c r : ℂ))
  have hcd : ∀ r, HasDerivAt (fun q : ℝ => (c q : ℂ)) (v r) r :=
    fun r => (hc.differentiable_one r).hasDerivAt
  rw [(pairedEdge_hasDerivAt N γ c v hcd t).deriv, greenOneForm_neg_tangent]
  change -greenOneForm _ _ ((γ • c (1 - t) : UpperHalfPlane) : ℂ)
      (_ * v (1 - t)) = _
  rw [greenOneForm_gamma0_transport N γ _ _
    (fun z => (completedComplexField_contDiffAt N s z).differentiableAt (by simp))
    (fun z => (completedComplexField_contDiffAt N u z).differentiableAt (by simp))
    (completedComplexField_Gamma0_invariant N hN s hs)
    (completedComplexField_Gamma0_invariant N hN u hu)]
  rfl

theorem completedGreen_paired_edge_intervalIntegrable (N : ℕ) (hN : 0 < N)
    (s u : ℂ) (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (γ : CongruenceSubgroup.Gamma0 N) (c : ℝ → UpperHalfPlane)
    (hc : ContDiff ℝ 1 (fun t : ℝ => (c t : ℂ))) :
    IntervalIntegrable (fun t : ℝ => greenOneForm (completedComplexField N s)
      (completedComplexField N u) (pairedEdge N γ c t)
      (deriv (fun r : ℝ => (pairedEdge N γ c r : ℂ)) t)) volume 0 1 := by
  simp_rw [completedGreen_paired_density N hN s u hs hu γ c hc]
  exact ((greenOneForm_edge_continuous _ _ (completedComplexField_contDiffAt N s)
    (completedComplexField_contDiffAt N u) c hc).comp
      (continuous_const.sub continuous_id)).neg.intervalIntegrable 0 1

/-- Actual, integrable completed Eisenstein side cancellation. Smoothness
and invariance are supplied by the genuine all-level continuation. -/
theorem actualCompleted_Gamma0_paired_side_cancel (N : ℕ) (hN : 0 < N)
    (s u : ℂ) (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (γ : CongruenceSubgroup.Gamma0 N) (c : ℝ → UpperHalfPlane)
    (hc : ContDiff ℝ 1 (fun t : ℝ => (c t : ℂ))) :
    edgeGreenIntegral (completedComplexField N s) (completedComplexField N u) c +
      edgeGreenIntegral (completedComplexField N s) (completedComplexField N u) (pairedEdge N γ c) = 0 :=
  gamma0_paired_edge_integral_cancel N γ _ _
    (fun z => (completedComplexField_contDiffAt N s z).differentiableAt (by simp))
    (fun z => (completedComplexField_contDiffAt N u z).differentiableAt (by simp))
    (completedComplexField_Gamma0_invariant N hN s hs)
    (completedComplexField_Gamma0_invariant N hN u hu) c _
    (fun t => (hc.differentiable_one t).hasDerivAt)

end ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
