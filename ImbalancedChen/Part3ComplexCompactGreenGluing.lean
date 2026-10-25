import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
A complex-valued two-branch compact Green residual identity. Neither an
ODE nor a Wronskian is a premise: both residuals remain in the conclusion.
This is the general gluing calculation needed before substituting actual
complex-order I and K. It asserts no actual I/K connection or spectral result.
-/
namespace ImbalancedChen.Part3.ComplexCompactGreenGluingSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

/-- The source side belongs to the left interval; the singleton has zero
Lebesgue mass, but using one convention avoids a hidden boundary choice. -/
def splice (s : ℝ) (F G : ℝ → ℂ) (r : ℝ) : ℂ :=
  if r ≤ s then F r else G r

theorem splice_integrable (s : ℝ) (F G : ℝ → ℂ)
    (hF : Integrable F) (hG : Integrable G) : Integrable (splice s F G) := by
  exact Integrable.piecewise measurableSet_Iic hF.integrableOn hG.integrableOn

/-- Compact support supplies both remote endpoints. The functions being
spliced need not agree at the source; their exact mismatch is retained. -/
theorem integral_splice_derivatives (s : ℝ) (F G : ℝ → ℂ)
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hcF : HasCompactSupport F) (hcG : HasCompactSupport G) :
    (∫ r : ℝ, splice s (deriv F) (deriv G) r) = F s - G s := by
  have hiF : Integrable (deriv F) :=
    hF.continuous_deriv_one.integrable_of_hasCompactSupport hcF.deriv
  have hiG : Integrable (deriv G) :=
    hG.continuous_deriv_one.integrable_of_hasCompactSupport hcG.deriv
  have hi := splice_integrable s _ _ hiF hiG
  rw [← integral_add_compl (s := Iic s) measurableSet_Iic hi, compl_Iic]
  have hleft : (∫ r in Iic s, splice s (deriv F) (deriv G) r) =
      ∫ r in Iic s, deriv F r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with r hr
    exact if_pos hr
  have hright : (∫ r in Ioi s, splice s (deriv F) (deriv G) r) =
      ∫ r in Ioi s, deriv G r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact if_neg (not_le.mpr hr)
  rw [hleft, hright, HasCompactSupport.integral_Iic_deriv_eq hF hcF,
    HasCompactSupport.integral_Ioi_deriv_eq hG hcG, sub_eq_add_neg]

def flux (u phi : ℝ → ℂ) (r : ℝ) : ℂ :=
  deriv u r * phi r - u r * deriv phi r

private theorem derivative_C1 {u : ℝ → ℂ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (deriv u) := by
  have h : ContDiff ℝ ((1 : ℕ∞ω) + 1) u := by simpa using hu
  exact (contDiff_succ_iff_deriv.mp h).2.2

theorem flux_C1 (u phi : ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (hphi : ContDiff ℝ 2 phi) : ContDiff ℝ 1 (flux u phi) := by
  exact ((derivative_C1 hu).mul (hphi.of_le (by norm_num))).sub
    ((hu.of_le (by norm_num)).mul (derivative_C1 hphi))

theorem flux_compact (u phi : ℝ → ℂ) (hc : HasCompactSupport phi) :
    HasCompactSupport (flux u phi) := by
  exact hc.mul_left.sub hc.deriv.mul_left

theorem flux_derivative (u phi : ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (hphi : ContDiff ℝ 2 phi) (r : ℝ) :
    deriv (flux u phi) r = deriv (deriv u) r * phi r - u r * deriv (deriv phi) r := by
  have h := (((derivative_C1 hu).differentiable_one r).hasDerivAt.mul
    (hphi.differentiable (by norm_num) r).hasDerivAt).sub
    ((hu.differentiable (by norm_num) r).hasDerivAt.mul
      ((derivative_C1 hphi).differentiable_one r).hasDerivAt)
  have hd : HasDerivAt (flux u phi)
      (deriv (deriv u) r * phi r - u r * deriv (deriv phi) r) r := by
    convert h using 1 <;> dsimp [flux] <;> ring
  exact hd.deriv

/-- A complex potential is allowed. Its continuity is not needed in this
identity because it cancels algebraically before integration. -/
def operator (V f : ℝ → ℂ) (r : ℝ) : ℂ :=
  -deriv (deriv f) r + V r * f r

def kernel (u v : ℝ → ℂ) (s r : ℝ) : ℂ :=
  u (min r s) * v (max r s)

/-- Exact Green formula with both differential defects visible. This is
valid for arbitrary complex C2 branches and compact C2 complex tests, so
no target homogeneous equation or normalized jump has been assumed. -/
theorem compact_green_residual_identity (u v V phi : ℝ → ℂ) (s : ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hphi : ContDiff ℝ 2 phi) (hc : HasCompactSupport phi) :
    (∫ r : ℝ, kernel u v s r * operator V phi r -
      splice s (fun x => v s * operator V u x * phi x)
        (fun x => u s * operator V v x * phi x) r) =
      (deriv u s * v s - u s * deriv v s) * phi s := by
  let F : ℝ → ℂ := fun r => v s * flux u phi r
  let G : ℝ → ℂ := fun r => u s * flux v phi r
  have hF : ContDiff ℝ 1 F := contDiff_const.mul (flux_C1 u phi hu hphi)
  have hG : ContDiff ℝ 1 G := contDiff_const.mul (flux_C1 v phi hv hphi)
  have hcF : HasCompactSupport F := (flux_compact u phi hc).mul_left
  have hcG : HasCompactSupport G := (flux_compact v phi hc).mul_left
  have hFd (r : ℝ) : deriv F r = v s *
      (deriv (deriv u) r * phi r - u r * deriv (deriv phi) r) := by
    rw [show deriv F r = v s * deriv (flux u phi) r by
      exact (((flux_C1 u phi hu hphi).differentiable_one r).hasDerivAt.const_mul (v s)).deriv,
      flux_derivative u phi hu hphi]
  have hGd (r : ℝ) : deriv G r = u s *
      (deriv (deriv v) r * phi r - v r * deriv (deriv phi) r) := by
    rw [show deriv G r = u s * deriv (flux v phi) r by
      exact (((flux_C1 v phi hv hphi).differentiable_one r).hasDerivAt.const_mul (u s)).deriv,
      flux_derivative v phi hv hphi]
  calc
    _ = ∫ r : ℝ, splice s (deriv F) (deriv G) r := by
      apply integral_congr_ae
      filter_upwards [] with r
      by_cases hr : r ≤ s
      · simp only [kernel, min_eq_left hr, max_eq_right hr, splice, if_pos hr, hFd, operator]
        ring
      · have hs : s ≤ r := (lt_of_not_ge hr).le
        simp only [kernel, min_eq_right hs, max_eq_left hs, splice, if_neg hr, hGd, operator]
        ring
    _ = F s - G s := integral_splice_derivatives s F G hF hG hcF hcG
    _ = _ := by dsimp [F, G, flux]; ring

end
end ImbalancedChen.Part3.ComplexCompactGreenGluingSourceOnly
