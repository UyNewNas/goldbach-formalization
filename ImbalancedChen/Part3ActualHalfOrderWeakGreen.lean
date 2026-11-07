import ImbalancedChen.Part3ActualHalfOrderRadialGreen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Weak Green identity for the actual half-order kernel

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
For every real C2 compactly supported test phi, the actual kernel satisfies
  integral G_s(r) (-phi''(r)+(exp(2r)+1/4)phi(r)) dr = phi(s).
Both integrations by parts are encoded by differentiating the actual flux
F'phi-F phi'. Its compact support follows from that of phi and phi'.
The native compact-support FTC on the two half-lines supplies the vanishing
endpoints, and the previously proved actual derivative jump supplies phi(s).
No boundary, Green identity, ODE or spectral supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualHalfOrderWeakGreenSourceOnly

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ModifiedHalfOrderISourceOnly ActualHalfOrderKWronskianSourceOnly
open ActualHalfOrderRadialGreenSourceOnly ActualKRadialLogConjugation20261025a

theorem contDiff_radialHalfI : ContDiff ℝ ∞ radialHalfI := by
  have heq : radialHalfI = fun r =>
      halfINormalization * (Real.exp r) ^ (-1 / 2 : ℝ) * Real.sinh (Real.exp r) := by
    funext r
    exact modifiedHalfI_eq_closedForm (Real.exp r)
  rw [heq]
  have hpow : ContDiff ℝ ∞ (fun r : ℝ => (Real.exp r) ^ (-1 / 2 : ℝ)) :=
    Real.contDiff_exp.rpow_const_of_ne (fun r => Real.exp_ne_zero r)
  exact (contDiff_const.mul hpow).mul Real.contDiff_exp.sinh

theorem contDiff_radialHalfK : ContDiff ℝ ∞ radialHalfK := by
  have heq : radialHalfK = fun r =>
      halfKNormalization * (Real.exp r) ^ (-1 / 2 : ℝ) * Real.exp (-Real.exp r) := by
    funext r
    exact realOrderK_half_eq_rpow (Real.exp_pos r)
  rw [heq]
  have hpow : ContDiff ℝ ∞ (fun r : ℝ => (Real.exp r) ^ (-1 / 2 : ℝ)) :=
    Real.contDiff_exp.rpow_const_of_ne (fun r => Real.exp_ne_zero r)
  exact (contDiff_const.mul hpow).mul Real.contDiff_exp.neg.exp

def compactGreenFlux (F phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv F r * phi r - F r * deriv phi r

private theorem contDiff_one_deriv_of_two {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (deriv F) := by
  have hFs : ContDiff ℝ ((1 : ℕ∞ω) + 1) F := by simpa using hF
  exact (contDiff_succ_iff_deriv.mp hFs).2.2

theorem compactGreenFlux_contDiff (F phi : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hphi : ContDiff ℝ 2 phi) :
    ContDiff ℝ 1 (compactGreenFlux F phi) := by
  exact ((contDiff_one_deriv_of_two hF).mul (hphi.of_le (by norm_num))).sub
    ((hF.of_le (by norm_num)).mul (contDiff_one_deriv_of_two hphi))

theorem compactGreenFlux_hasCompactSupport (F phi : ℝ → ℝ)
    (hphi : HasCompactSupport phi) : HasCompactSupport (compactGreenFlux F phi) := by
  exact hphi.mul_left.sub hphi.deriv.mul_left

/-- Actual product differentiation: the two middle first-derivative
terms cancel, leaving the twice-integrated Green expression. -/
theorem compactGreenFlux_hasDerivAt (F phi : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hphi : ContDiff ℝ 2 phi) (r : ℝ) :
    HasDerivAt (compactGreenFlux F phi)
      (deriv (deriv F) r * phi r - F r * deriv (deriv phi) r) r := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hphid : Differentiable ℝ phi := hphi.differentiable (by norm_num)
  have hDFd : Differentiable ℝ (deriv F) :=
    (contDiff_one_deriv_of_two hF).differentiable_one
  have hDphid : Differentiable ℝ (deriv phi) :=
    (contDiff_one_deriv_of_two hphi).differentiable_one
  have h := ((hDFd r).hasDerivAt.mul (hphid r).hasDerivAt).sub
    ((hFd r).hasDerivAt.mul (hDphid r).hasDerivAt)
  convert h using 1 <;> dsimp [compactGreenFlux] <;> ring

theorem radialHalfI_flux_deriv (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi) (r : ℝ) :
    deriv (compactGreenFlux radialHalfI phi) r =
      radialHalfI r * halfRadialOperator phi r := by
  rw [(compactGreenFlux_hasDerivAt radialHalfI phi
    (contDiff_radialHalfI.of_le (by simp)) hphi r).deriv]
  have h := halfRadialOperator_radialHalfI r
  unfold halfRadialOperator at h ⊢
  linear_combination -(phi r) * h

theorem radialHalfK_flux_deriv (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi) (r : ℝ) :
    deriv (compactGreenFlux radialHalfK phi) r =
      radialHalfK r * halfRadialOperator phi r := by
  rw [(compactGreenFlux_hasDerivAt radialHalfK phi
    (contDiff_radialHalfK.of_le (by simp)) hphi r).deriv]
  have h := halfRadialOperator_radialHalfK r
  unfold halfRadialOperator at h ⊢
  linear_combination -(phi r) * h

theorem halfRadialOperator_continuous (phi : ℝ → ℝ) (hphi : ContDiff ℝ 2 phi) :
    Continuous (halfRadialOperator phi) := by
  have hsecond : Continuous (deriv (deriv phi)) :=
    (contDiff_one_deriv_of_two hphi).continuous_deriv_one
  have hV : Continuous (fun r : ℝ => Real.exp (2 * r) + (1 / 4 : ℝ)) := by fun_prop
  exact hsecond.neg.add (hV.mul hphi.continuous)

theorem halfRadialOperator_hasCompactSupport (phi : ℝ → ℝ)
    (hphi : HasCompactSupport phi) : HasCompactSupport (halfRadialOperator phi) := by
  exact hphi.deriv.deriv.neg.add hphi.mul_left

theorem actualHalfRadialGreen_test_integrable (s : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    Integrable (fun r => actualHalfRadialGreen s r * halfRadialOperator phi r) := by
  exact ((actualHalfRadialGreen_continuous s).mul
    (halfRadialOperator_continuous phi hphi)).integrable_of_hasCompactSupport
      (halfRadialOperator_hasCompactSupport phi hc).mul_left

/-- The left half-line flux is derived by compact-support FTC, including
the vanishing endpoint at minus infinity. -/
theorem actualHalfRadialGreen_left_integral (s : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ r in Iic s, actualHalfRadialGreen s r * halfRadialOperator phi r) =
      radialHalfK s * compactGreenFlux radialHalfI phi s := by
  calc
    (∫ r in Iic s, actualHalfRadialGreen s r * halfRadialOperator phi r) =
        ∫ r in Iic s, radialHalfK s * deriv (compactGreenFlux radialHalfI phi) r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with r hr
      rw [actualHalfRadialGreen_eq_left hr, radialHalfI_flux_deriv phi hphi]
      ring
    _ = radialHalfK s * ∫ r in Iic s, deriv (compactGreenFlux radialHalfI phi) r :=
      integral_const_mul _ _
    _ = radialHalfK s * compactGreenFlux radialHalfI phi s := by
      rw [HasCompactSupport.integral_Iic_deriv_eq
        (compactGreenFlux_contDiff radialHalfI phi (contDiff_radialHalfI.of_le (by simp)) hphi)
        (compactGreenFlux_hasCompactSupport radialHalfI phi hc) s]

/-- The right half-line flux includes the opposite sign from its source endpoint. -/
theorem actualHalfRadialGreen_right_integral (s : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ r in Ioi s, actualHalfRadialGreen s r * halfRadialOperator phi r) =
      -(radialHalfI s * compactGreenFlux radialHalfK phi s) := by
  calc
    (∫ r in Ioi s, actualHalfRadialGreen s r * halfRadialOperator phi r) =
        ∫ r in Ioi s, radialHalfI s * deriv (compactGreenFlux radialHalfK phi) r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [actualHalfRadialGreen_eq_right hr.le, radialHalfK_flux_deriv phi hphi]
      ring
    _ = radialHalfI s * ∫ r in Ioi s, deriv (compactGreenFlux radialHalfK phi) r :=
      integral_const_mul _ _
    _ = -(radialHalfI s * compactGreenFlux radialHalfK phi s) := by
      rw [HasCompactSupport.integral_Ioi_deriv_eq
        (compactGreenFlux_contDiff radialHalfK phi (contDiff_radialHalfK.of_le (by simp)) hphi)
        (compactGreenFlux_hasCompactSupport radialHalfK phi hc) s]
      ring

/-- The literal radial Wronskian is extracted from the already proved
one-sided derivative jump of the actual kernel. -/
theorem radialHalf_IK_wronskian (s : ℝ) :
    radialHalfI s * deriv radialHalfK s - deriv radialHalfI s * radialHalfK s = -1 := by
  rw [(radialHalfI_hasDerivAt s).deriv, (radialHalfK_hasDerivAt s).deriv]
  have h := actualHalfRadialGreen_derivative_jump s
  rw [(actualHalfRadialGreen_hasDerivWithinAt_right s).derivWithin (uniqueDiffWithinAt_Ici s),
    (actualHalfRadialGreen_hasDerivWithinAt_left s).derivWithin (uniqueDiffWithinAt_Iic s)] at h
  exact h

/-- Actual weak Green identity for every real C2 compact test, hence in
particular every real C-infinity compact test. All boundary and derivative
inputs have been derived from the actual functions and compact support. -/
theorem actualHalfRadialGreen_weak_identity (s : ℝ) (phi : ℝ → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ r : ℝ, actualHalfRadialGreen s r *
      (-deriv (deriv phi) r + (Real.exp (2 * r) + (1 / 4 : ℝ)) * phi r)) = phi s := by
  change (∫ r : ℝ, actualHalfRadialGreen s r * halfRadialOperator phi r) = _
  have hint := actualHalfRadialGreen_test_integrable s phi hphi hc
  rw [← integral_add_compl (s := Iic s) measurableSet_Iic hint, compl_Iic,
    actualHalfRadialGreen_left_integral s phi hphi hc,
    actualHalfRadialGreen_right_integral s phi hphi hc]
  calc
    radialHalfK s * compactGreenFlux radialHalfI phi s +
        -(radialHalfI s * compactGreenFlux radialHalfK phi s) =
        -(radialHalfI s * deriv radialHalfK s - deriv radialHalfI s * radialHalfK s) * phi s := by
      dsimp only [compactGreenFlux]
      ring
    _ = phi s := by rw [radialHalf_IK_wronskian]; ring

end

end ImbalancedChen.Part3.ActualHalfOrderWeakGreenSourceOnly
