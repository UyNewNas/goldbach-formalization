import ImbalancedChen.Part3ActualCutPlaneKOrderZeroRemovable
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual logarithmic-cover I and K models. The coordinate L is the logarithm
of HALF the physical argument: the physical argument is 2*exp(L), and the
entire core is evaluated at exp(2L). The zero-order model uses its actual
independent order-derivative core formula, not a singular sine quotient.
All log-coordinate functions are proved holomorphic on the whole plane
in the supplied order ranges. Principal-half-log values are bound to the
actual slit models, and hence to actual Laplace K on the right half-plane.
No product-sector identity, monodromy identity or endpoint bound is assumed.
-/

namespace ImbalancedChen.Part3.ActualLogCoverKModel20261026b

noncomputable section
open Set
open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly
open ActualComplexArgumentISlit20261026b ActualICoreZeroOrderDerivative20261026b
open ActualCutPlaneKIModel20261026b ActualCutPlaneKZeroModel20261026b
open ActualCutPlaneKOrderZeroRemovable20261026b ActualComplexArgumentKLaplace20261026b

def logCoverI (nu L : ℂ) : ℂ :=
  Complex.exp (nu * L) * generalICore nu (Complex.exp (2 * L))

def logCoverKNonintegral (nu L : ℂ) : ℂ :=
  (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
    (logCoverI (-nu) L - logCoverI nu L)

def logCoverKZero (L : ℂ) : ℂ :=
  -(L * logCoverI 0 L + coreOrderDerivativeZero (Complex.exp (2 * L)))

def logCoverK (nu L : ℂ) : ℂ :=
  if nu = 0 then logCoverKZero L else logCoverKNonintegral nu L

theorem logCoverI_analyticAt {nu : ℂ} (hnu : -1 < nu.re) (L : ℂ) :
    AnalyticAt ℂ (logCoverI nu) L := by
  have hp : AnalyticAt ℂ (fun w : ℂ => Complex.exp (nu * w)) L :=
    (analyticAt_const.mul analyticAt_id).cexp
  have hc : AnalyticAt ℂ (fun w : ℂ => Complex.exp (2 * w)) L :=
    (analyticAt_const.mul analyticAt_id).cexp
  exact hp.mul ((analyticAt_generalICore hnu (Complex.exp (2 * L))).comp hc)

theorem logCoverI_analyticOnNhd {nu : ℂ} (hnu : -1 < nu.re) :
    AnalyticOnNhd ℂ (logCoverI nu) univ := fun L _ => logCoverI_analyticAt hnu L

theorem logCoverKNonintegral_analyticOnNhd {nu : ℂ} (hL : -1 < nu.re) (hU : nu.re < 1) :
    AnalyticOnNhd ℂ (logCoverKNonintegral nu) univ := by
  have hm : -1 < (-nu).re := by rw [Complex.neg_re]; linarith
  exact analyticOnNhd_const.mul ((logCoverI_analyticOnNhd hm).sub (logCoverI_analyticOnNhd hL))

theorem logCoverKZero_analyticAt (L : ℂ) : AnalyticAt ℂ logCoverKZero L := by
  have hc : AnalyticAt ℂ (fun w : ℂ => Complex.exp (2 * w)) L :=
    (analyticAt_const.mul analyticAt_id).cexp
  exact ((analyticAt_id.mul (logCoverI_analyticAt (nu := 0) (by norm_num) L)).add
    ((coreOrderDerivativeZero_analyticAt (Complex.exp (2 * L))).comp hc)).neg

theorem logCoverK_analyticOnNhd {nu : ℂ} (hL : -1 < nu.re) (hU : nu.re < 1) :
    AnalyticOnNhd ℂ (logCoverK nu) univ := by
  by_cases hn : nu = 0
  · subst nu
    simpa only [logCoverK, if_pos rfl] using
      (show AnalyticOnNhd ℂ logCoverKZero univ from fun L _ => logCoverKZero_analyticAt L)
  · simpa only [logCoverK, if_neg hn] using logCoverKNonintegral_analyticOnNhd hL hU

/-- The zero-order cover model is the actual negative order derivative,
independently of any nonintegral sine-quotient formula. -/
theorem logCoverI_order_zero_hasDerivAt (L : ℂ) :
    HasDerivAt (fun nu : ℂ => logCoverI nu L)
      (L * logCoverI 0 L + coreOrderDerivativeZero (Complex.exp (2 * L))) 0 := by
  have hp : HasDerivAt (fun nu : ℂ => Complex.exp (nu * L)) L 0 := by
    simpa only [zero_mul, Complex.exp_zero, one_mul] using
      ((hasDerivAt_id (0 : ℂ)).mul_const L).cexp
  have hc : HasDerivAt (fun nu : ℂ => generalICore nu (Complex.exp (2 * L)))
      (coreOrderDerivativeZero (Complex.exp (2 * L))) 0 :=
    (analyticAt_generalICore_order 0 (Complex.exp (2 * L)) (by norm_num)).differentiableAt.hasDerivAt
  simpa only [logCoverI, zero_mul, Complex.exp_zero, one_mul] using hp.mul hc

theorem logCoverKZero_eq_neg_order_deriv (L : ℂ) :
    logCoverKZero L = -deriv (fun nu : ℂ => logCoverI nu L) 0 := by
  rw [(logCoverI_order_zero_hasDerivAt L).deriv]
  rfl

theorem exp_double_principal_half_log {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (2 * Complex.log (z / 2)) = (z / 2) ^ (2 : ℕ) := by
  have hh : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  rw [show 2 * Complex.log (z / 2) = Complex.log (z / 2) + Complex.log (z / 2) by ring]
  simp only [Complex.exp_add, Complex.exp_log hh, pow_two]

/-- Binding to the literal I slit model retains the actual half-coordinate. -/
theorem logCoverI_principal_half_log (nu : ℂ) {z : ℂ} (hz : z ≠ 0) :
    logCoverI nu (Complex.log (z / 2)) = complexArgumentI nu z := by
  have hh : z / 2 ≠ 0 := div_ne_zero hz (by norm_num)
  have hp : Complex.exp (nu * Complex.log (z / 2)) = (z / 2) ^ nu := by
    rw [Complex.cpow_def_of_ne_zero hh]
    congr 1
    ring
  unfold logCoverI complexArgumentI
  rw [hp, exp_double_principal_half_log hz]

theorem logCoverKNonintegral_principal_half_log (nu : ℂ) {z : ℂ} (hz : z ≠ 0) :
    logCoverKNonintegral nu (Complex.log (z / 2)) = cutPlaneKNonintegral nu z := by
  unfold logCoverKNonintegral cutPlaneKNonintegral
  rw [logCoverI_principal_half_log (-nu) hz, logCoverI_principal_half_log nu hz]

theorem logCoverKZero_principal_half_log {z : ℂ} (hz : z ≠ 0) :
    logCoverKZero (Complex.log (z / 2)) = cutPlaneKZero z := by
  unfold logCoverKZero
  rw [logCoverI_principal_half_log 0 hz, exp_double_principal_half_log hz,
    cutPlaneKZero_eq_formula hz]

/-- Principal-half-log binding to the actual zero-glued slit K model. -/
theorem logCoverK_principal_half_log (nu : ℂ) {z : ℂ} (hz : z ≠ 0) :
    logCoverK nu (Complex.log (z / 2)) = cutPlaneKWithZero nu z := by
  by_cases hn : nu = 0
  · subst nu
    simp only [logCoverK, cutPlaneKWithZero, if_pos rfl]
    exact logCoverKZero_principal_half_log hz
  · simp only [logCoverK, cutPlaneKWithZero, if_neg hn]
    exact logCoverKNonintegral_principal_half_log nu hz

/-- Binding to the actual Laplace K on the exact supplied order ranges,
now including order zero, throughout Re(z)>0. -/
theorem logCoverK_eq_actual_rightHalfPlane {nu z : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0)) (hz : 0 < z.re) :
    logCoverK nu (Complex.log (z / 2)) = complexArgumentK nu z := by
  have hn : z ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hz
  rw [logCoverK_principal_half_log nu hn]
  exact cutPlaneKWithZero_eq_actual horder hz

end
end ImbalancedChen.Part3.ActualLogCoverKModel20261026b
