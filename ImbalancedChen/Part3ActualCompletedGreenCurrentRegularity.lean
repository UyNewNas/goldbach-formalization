import ImbalancedChen.Part3ActualCompletedEisensteinGreenInterior
import ImbalancedChen.Part3CompletedActualEisensteinIdentity
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The ACTUAL Green vector/one-form is C1 on the positive chart. This follows
from genuine two-variable C2 of the completed Fourier family through the
Frechet derivative, not merely from existence of separate partials. The
Frechet-coordinate divergence is identified with the proved literal slice
divergence and hence with its actual signed eigenvalue expression.
Horizontal periodicity of the actual current is deduced from genuine
modular T invariance and differentiation of the translated actual trace.
These are the concrete interior and side hypotheses required by strip
Stokes; neither Green regularity nor periodicity is a caller premise.
-/

namespace ImbalancedChen.Part3.ActualCompletedGreenCurrentRegularity20261026b
noncomputable section
open Set Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open CompletedEisensteinReflection20261025a CompletedEisensteinSpatialMaass
open CompletedActualEisensteinIdentity20261025a
open ContinuedFourierSpatialContDiffTwo
open ActualEisensteinHorocycleGreenFlux20261026b
open ActualCompletedEisensteinGreenInterior20261026b
open PrimitiveEisensteinFourierParameterAnalytic PrimitiveEisensteinHorizontalContinuity

theorem slice_deriv_x_eq_fderiv {F : ℝ × ℝ → ℂ} {x y : ℝ}
    (hF : DifferentiableAt ℝ F (x, y)) :
    deriv (fun t : ℝ => F (t, y)) x = fderiv ℝ F (x, y) (1, 0) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv

theorem slice_deriv_y_eq_fderiv {F : ℝ × ℝ → ℂ} {x y : ℝ}
    (hF : DifferentiableAt ℝ F (x, y)) :
    deriv (fun t : ℝ => F (x, t)) y = fderiv ℝ F (x, y) (0, 1) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv

private theorem partial_x_contDiffOn_one {F : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ 2 F upperChart) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (t, p.2)) p.1) upperChart := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ F) upperChart :=
    hF.fderiv_of_isOpen upperChart_isOpen (by norm_num)
  apply (hD.clm_apply (contDiffOn_const (c := (1, 0)))).congr
  intro p hp
  have hAt : DifferentiableAt ℝ F p :=
    ((hF p hp).contDiffAt (upperChart_isOpen.mem_nhds hp)).differentiableAt (by norm_num)
  exact slice_deriv_x_eq_fderiv hAt

private theorem partial_y_contDiffOn_one {F : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ 2 F upperChart) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) upperChart := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ F) upperChart :=
    hF.fderiv_of_isOpen upperChart_isOpen (by norm_num)
  apply (hD.clm_apply (contDiffOn_const (c := (0, 1)))).congr
  intro p hp
  have hAt : DifferentiableAt ℝ F p :=
    ((hF p hp).contDiffAt (upperChart_isOpen.mem_nhds hp)).differentiableAt (by norm_num)
  exact slice_deriv_y_eq_fderiv hAt

/-- Genuine C1 of the horizontal actual Green component on the full open
positive chart. No spectral regularity hypothesis is passed by a caller. -/
theorem actualGreenCurrentX_contDiffOn_one (s u : ℂ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => actualGreenCurrentX s u p.2 p.1) upperChart := by
  have hs := completedEisensteinFourier_contDiffOn_two s
  have hu := completedEisensteinFourier_contDiffOn_two u
  have hxs := partial_x_contDiffOn_one hs
  have hxu := partial_x_contDiffOn_one hu
  simpa only [actualGreenCurrentX] using
    (((hs.of_le (by norm_num)).star.mul hxu).sub (hxs.star.mul (hu.of_le (by norm_num))))

/-- Genuine C1 of the PREEXISTING vertical boundary current, with the same
definition used by all actual horocycle flux theorems. -/
theorem actualGreenCurrent_contDiffOn_one (s u : ℂ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => actualGreenCurrent s u p.2 p.1) upperChart := by
  have hs := completedEisensteinFourier_contDiffOn_two s
  have hu := completedEisensteinFourier_contDiffOn_two u
  have hys := partial_y_contDiffOn_one hs
  have hyu := partial_y_contDiffOn_one hu
  simpa only [actualGreenCurrent] using
    (((hs.of_le (by norm_num)).star.mul hyu).sub (hys.star.mul (hu.of_le (by norm_num))))

theorem actualGreenVector_contDiffOn_one (s u : ℂ) :
    ContDiffOn ℝ 1 (actualGreenVector s u) upperChart :=
  (actualGreenCurrentX_contDiffOn_one s u).prodMk (actualGreenCurrent_contDiffOn_one s u)

theorem actualGreenOneForm_contDiffOn_one (s u : ℂ) :
    ContDiffOn ℝ 1 (actualGreenOneForm s u) upperChart := by
  have hx := actualGreenCurrentX_contDiffOn_one s u
  have hy := actualGreenCurrent_contDiffOn_one s u
  simpa only [actualGreenOneForm, coordinateLinear] using
    ((firstLift.contDiff.comp_contDiffOn hy.neg).add (secondLift.contDiff.comp_contDiffOn hx))

/-- Coordinates in the pinned Frechet divergence theorem are exactly the
literal slice divergence already computed for the actual Eisenstein pair. -/
theorem actualGreen_fderiv_divergence (s u : ℂ) (x y : ℝ) (hy : 0 < y) :
    fderiv ℝ (fun p : ℝ × ℝ => actualGreenCurrentX s u p.2 p.1) (x, y) (1, 0) +
      fderiv ℝ (fun p : ℝ × ℝ => actualGreenCurrent s u p.2 p.1) (x, y) (0, 1) =
        actualGreenDivergence s u y x := by
  have hx := ((actualGreenCurrentX_contDiffOn_one s u) (x, y) hy).contDiffAt
    (upperChart_isOpen.mem_nhds hy)
  have hv := ((actualGreenCurrent_contDiffOn_one s u) (x, y) hy).contDiffAt
    (upperChart_isOpen.mem_nhds hy)
  rw [← slice_deriv_x_eq_fderiv (hx.differentiableAt (by norm_num)),
    ← slice_deriv_y_eq_fderiv (hv.differentiableAt (by norm_num))]
  rfl

theorem actualGreen_fderiv_divergence_eq (s u : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) (x y : ℝ) (hy : 0 < y) :
    fderiv ℝ (fun p : ℝ × ℝ => actualGreenCurrentX s u p.2 p.1) (x, y) (1, 0) +
      fderiv ℝ (fun p : ℝ × ℝ => actualGreenCurrent s u p.2 p.1) (x, y) (0, 1) =
      (star (s * (1 - s)) - u * (1 - u)) * star (completedEisensteinFourier s y x) *
        completedEisensteinFourier u y x / (y : ℂ) ^ 2 := by
  rw [actualGreen_fderiv_divergence s u x y hy,
    actualGreenDivergence_eq s u hs0 hs1 hu0 hu1 y x hy]

theorem completedFourier_horizontal_periodic (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y : ℝ) (hy : 0 < y) : Function.Periodic (fun x : ℝ => completedEisensteinFourier s y x) 1 := by
  intro x
  have h := completedActualEisenstein_SL2_invariant s hs0 hs1 ModularGroup.T (horizontalPoint y hy x)
  rw [← horizontalPoint_add_one y hy x] at h
  exact h

private theorem periodic_deriv (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hper : Function.Periodic f 1) : Function.Periodic (deriv f) 1 := by
  intro x
  have he : (fun t : ℝ => f (t + 1)) = f := funext hper
  have h := (hf (x + 1)).hasDerivAt.comp x ((hasDerivAt_id x).add_const 1)
  simp only [mul_one, one_mul, one_smul] at h
  rw [he] at h
  exact h.unique (hf x).hasDerivAt

/-- Actual horizontal current periodicity comes from genuine completed
modular T invariance and the derivative of the translated physical trace. -/
theorem actualGreenCurrentX_periodic (s u : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) (y : ℝ) (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => actualGreenCurrentX s u y x) 1 := by
  have hsPer := completedFourier_horizontal_periodic s hs0 hs1 y hy
  have huPer := completedFourier_horizontal_periodic u hu0 hu1 y hy
  have hsDiff : Differentiable ℝ (fun x : ℝ => completedEisensteinFourier s y x) :=
    ((completedEisensteinFourier_contDiffOn_two s).comp_contDiff (by fun_prop) (fun _ => hy))
      .differentiable (by norm_num)
  have huDiff : Differentiable ℝ (fun x : ℝ => completedEisensteinFourier u y x) :=
    ((completedEisensteinFourier_contDiffOn_two u).comp_contDiff (by fun_prop) (fun _ => hy))
      .differentiable (by norm_num)
  have hdsPer := periodic_deriv _ hsDiff hsPer
  have hduPer := periodic_deriv _ huDiff huPer
  intro x
  unfold actualGreenCurrentX
  rw [hsPer x, huPer x, hdsPer x, hduPer x]

end
end ImbalancedChen.Part3.ActualCompletedGreenCurrentRegularity20261026b
