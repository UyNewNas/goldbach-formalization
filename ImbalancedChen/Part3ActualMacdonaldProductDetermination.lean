import ImbalancedChen.Part3ActualLogCoverKTurns
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual product-argument determination for Macdonald's kernel. Its
HALF-log coordinate is log(z)+log(w)-log(2*t), with t>0. The physical
argument is proved to be 2*exp(L)=z*w/t; Im(L) is the inherited sum of
the two original phases. Principal-log binding is proved only in its
actual phase window. If the sum crosses that window, explicit +/-2*pi*i
cover turns give the corresponding correction, including zero order.

Thus this model never silently replaces the summed determination by
principalLog(z*w/t). It does not supply larger-sector endpoint L1, decay,
or the full printed DLMF 10.32.18 integral identity; those remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualMacdonaldProductDetermination20261026b

noncomputable section
open Set
open ActualComplexArgumentISlit20261026b ActualCutPlaneKOrderZeroRemovable20261026b
open ActualLogCoverKModel20261026b ActualLogCoverKTurns20261026b
open ActualNegativeCutPowerLimits20261026b

def physicalProductArgument (z w : ℂ) (t : ℝ) : ℂ := z * w / (t : ℂ)

/-- Logarithm of HALF the product argument, retaining the inherited phase. -/
def productHalfLog (z w : ℂ) (t : ℝ) : ℂ :=
  Complex.log z + Complex.log w - (Real.log (2 * t) : ℂ)

def determinedProductK (nu z w : ℂ) (t : ℝ) : ℂ :=
  logCoverK nu (productHalfLog z w t)

theorem physicalProductArgument_ne_zero {z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t) : physicalProductArgument z w t ≠ 0 :=
  div_ne_zero (mul_ne_zero hz hw) (Complex.ofReal_ne_zero.mpr ht.ne')

/-- The coordinate keeps the factor 2 belonging to K's I-core half argument. -/
theorem exp_productHalfLog {z w : ℂ} {t : ℝ} (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t) :
    Complex.exp (productHalfLog z w t) = z * w / (2 * (t : ℂ)) := by
  have hp : 0 < 2 * t := mul_pos (by norm_num) ht
  have he : Complex.exp (Real.log (2 * t) : ℂ) = ((2 * t : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hp]
  unfold productHalfLog
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw, he]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

theorem exp_productHalfLog_eq_half {z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t) :
    Complex.exp (productHalfLog z w t) = physicalProductArgument z w t / 2 := by
  rw [exp_productHalfLog hz hw ht]
  unfold physicalProductArgument
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne'] <;> ring

theorem physical_product_of_half_log {z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t) :
    2 * Complex.exp (productHalfLog z w t) = physicalProductArgument z w t := by
  rw [exp_productHalfLog_eq_half hz hw ht]
  ring

/-- The phase is the inherited sum, before any principal-window reduction. -/
theorem productHalfLog_im (z w : ℂ) (t : ℝ) :
    (productHalfLog z w t).im = Complex.arg z + Complex.arg w := by
  simp only [productHalfLog, Complex.sub_im, Complex.add_im, Complex.log_im, Complex.ofReal_im,
    sub_zero]

theorem productHalfLog_re (z w : ℂ) (t : ℝ) :
    (productHalfLog z w t).re = Real.log ‖z‖ + Real.log ‖w‖ - Real.log (2 * t) := by
  simp only [productHalfLog, Complex.sub_re, Complex.add_re, Complex.log_re, Complex.ofReal_re]

/-- The inherited physical log is log(z)+log(w)-log(t); the K core uses
half the physical argument, so its coordinate has the additional log(2). -/
theorem productHalfLog_eq_sum_logs (z w : ℂ) {t : ℝ} (ht : 0 < t) :
    productHalfLog z w t =
      (Complex.log z + Complex.log w - (Real.log t : ℂ)) - (Real.log 2 : ℂ) := by
  unfold productHalfLog
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
  push_cast
  ring

theorem productHalfLog_analyticAt_left {z : ℂ} (hz : z ∈ Complex.slitPlane) (w : ℂ) (t : ℝ) :
    AnalyticAt ℂ (fun x => productHalfLog x w t) z :=
  ((Complex.analyticAt_clog hz).add analyticAt_const).sub analyticAt_const

theorem productHalfLog_analyticAt_right (z : ℂ) {w : ℂ} (hw : w ∈ Complex.slitPlane) (t : ℝ) :
    AnalyticAt ℂ (fun x => productHalfLog z x t) w :=
  (analyticAt_const.add (Complex.analyticAt_clog hw)).sub analyticAt_const

theorem determinedProductK_analyticAt_left {nu z : ℂ} (hL : -1 < nu.re) (hU : nu.re < 1)
    (hz : z ∈ Complex.slitPlane) (w : ℂ) (t : ℝ) :
    AnalyticAt ℂ (fun x => determinedProductK nu x w t) z :=
  ((logCoverK_analyticOnNhd hL hU) _ (mem_univ _)).comp (productHalfLog_analyticAt_left hz w t)

theorem determinedProductK_analyticAt_right {nu w : ℂ} (hL : -1 < nu.re) (hU : nu.re < 1)
    (z : ℂ) (hw : w ∈ Complex.slitPlane) (t : ℝ) :
    AnalyticAt ℂ (fun x => determinedProductK nu z x t) w :=
  ((logCoverK_analyticOnNhd hL hU) _ (mem_univ _)).comp (productHalfLog_analyticAt_right z hw t)

/-- Principal binding is proved only in the actual principal half-log
window. Its upper boundary corresponds to the upper cut determination. -/
theorem principal_half_log_eq_productHalfLog {z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t)
    (hminus : -Real.pi < Complex.arg z + Complex.arg w)
    (hplus : Complex.arg z + Complex.arg w ≤ Real.pi) :
    Complex.log (physicalProductArgument z w t / 2) = productHalfLog z w t := by
  rw [← exp_productHalfLog_eq_half hz hw ht]
  exact Complex.log_exp (by rw [productHalfLog_im]; exact hminus)
    (by rw [productHalfLog_im]; exact hplus)

theorem determinedProductK_eq_principal {nu z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t)
    (hminus : -Real.pi < Complex.arg z + Complex.arg w)
    (hplus : Complex.arg z + Complex.arg w ≤ Real.pi) :
    determinedProductK nu z w t = cutPlaneKWithZero nu (physicalProductArgument z w t) := by
  unfold determinedProductK
  rw [← principal_half_log_eq_productHalfLog hz hw ht hminus hplus,
    logCoverK_principal_half_log nu (physicalProductArgument_ne_zero hz hw ht)]

private theorem exp_sub_two_pi (L : ℂ) :
    Complex.exp (L - 2 * (Real.pi : ℂ) * Complex.I) = Complex.exp L := by
  rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

private theorem exp_add_two_pi (L : ℂ) :
    Complex.exp (L + 2 * (Real.pi : ℂ) * Complex.I) = Complex.exp L := by
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Above the principal window, the principal half-log is one full turn
below the inherited coordinate. This is derived from actual log(exp). -/
theorem principal_half_log_above {z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t)
    (hphase : Real.pi < Complex.arg z + Complex.arg w) :
    Complex.log (physicalProductArgument z w t / 2) =
      productHalfLog z w t - 2 * (Real.pi : ℂ) * Complex.I := by
  have him : (productHalfLog z w t - 2 * (Real.pi : ℂ) * Complex.I).im =
      Complex.arg z + Complex.arg w - 2 * Real.pi := by
    rw [Complex.sub_im, productHalfLog_im]
    simp
  have hupper := add_le_add (Complex.arg_le_pi z) (Complex.arg_le_pi w)
  have h := Complex.log_exp
    (x := productHalfLog z w t - 2 * (Real.pi : ℂ) * Complex.I)
    (by rw [him]; linarith) (by rw [him]; linarith [Real.pi_pos])
  rw [exp_sub_two_pi, exp_productHalfLog_eq_half hz hw ht] at h
  exact h

/-- At or below the lower cut, the principal half-log is one full turn
above the inherited coordinate. The equality case selects the lower cut
value through the cover, while principal log itself selects the upper. -/
theorem principal_half_log_below {z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t)
    (hphase : Complex.arg z + Complex.arg w ≤ -Real.pi) :
    Complex.log (physicalProductArgument z w t / 2) =
      productHalfLog z w t + 2 * (Real.pi : ℂ) * Complex.I := by
  have him : (productHalfLog z w t + 2 * (Real.pi : ℂ) * Complex.I).im =
      Complex.arg z + Complex.arg w + 2 * Real.pi := by
    rw [Complex.add_im, productHalfLog_im]
    simp
  have hlower := add_lt_add (Complex.neg_pi_lt_arg z) (Complex.neg_pi_lt_arg w)
  have h := Complex.log_exp
    (x := productHalfLog z w t + 2 * (Real.pi : ℂ) * Complex.I)
    (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; linarith)
  rw [exp_add_two_pi, exp_productHalfLog_eq_half hz hw ht] at h
  exact h

/-- Explicit inherited-branch correction after crossing above the cut.
The formula follows from the proved full-turn identity on the cover. -/
theorem determinedProductK_above_principal {nu z w : ℂ} {t : ℝ}
    (hnu : nu = 0 ∨ Complex.sin ((Real.pi : ℂ) * nu) ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t)
    (hphase : Real.pi < Complex.arg z + Complex.arg w) :
    determinedProductK nu z w t = lowerPhase nu ^ 2 *
      cutPlaneKWithZero nu (physicalProductArgument z w t) -
        (Real.pi : ℂ) * Complex.I * (lowerPhase nu + upperPhase nu) *
          complexArgumentI nu (physicalProductArgument z w t) := by
  have hp := principal_half_log_above hz hw ht hphase
  have hL : productHalfLog z w t = Complex.log (physicalProductArgument z w t / 2) +
      2 * (Real.pi : ℂ) * Complex.I := by rw [hp]; ring
  unfold determinedProductK
  rw [hL, logCoverK_add_two_pi hnu,
    logCoverK_principal_half_log nu (physicalProductArgument_ne_zero hz hw ht),
    logCoverI_principal_half_log nu (physicalProductArgument_ne_zero hz hw ht)]

theorem determinedProductK_below_principal {nu z w : ℂ} {t : ℝ}
    (hnu : nu = 0 ∨ Complex.sin ((Real.pi : ℂ) * nu) ≠ 0)
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t)
    (hphase : Complex.arg z + Complex.arg w ≤ -Real.pi) :
    determinedProductK nu z w t = upperPhase nu ^ 2 *
      cutPlaneKWithZero nu (physicalProductArgument z w t) +
        (Real.pi : ℂ) * Complex.I * (upperPhase nu + lowerPhase nu) *
          complexArgumentI nu (physicalProductArgument z w t) := by
  have hp := principal_half_log_below hz hw ht hphase
  have hL : productHalfLog z w t = Complex.log (physicalProductArgument z w t / 2) -
      2 * (Real.pi : ℂ) * Complex.I := by rw [hp]; ring
  unfold determinedProductK
  rw [hL, logCoverK_sub_two_pi hnu,
    logCoverK_principal_half_log nu (physicalProductArgument_ne_zero hz hw ht),
    logCoverI_principal_half_log nu (physicalProductArgument_ne_zero hz hw ht)]

end
end ImbalancedChen.Part3.ActualMacdonaldProductDetermination20261026b
