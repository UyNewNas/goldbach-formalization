import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual upper/lower negative-cut logarithm and complex-power limits. The
pinned principal-log boundary theorems are transported through the real
positive half scaling; powers are then derived from exp(nu*log), away
from the origin. This supplies the branch phases used by the literal
I-core limits, not an assumed Bessel continuation formula.

Primary references checked 2026-10-26: DLMF 10.34.E1, E2, E5
https://dlmf.nist.gov/10.34. The two signs below distinguish actual
upper and lower approaches to the cut; the lower set is strictly Im<0.
-/

namespace ImbalancedChen.Part3.ActualNegativeCutPowerLimits20261026b

noncomputable section
open Set Filter
open scoped Topology

def upperCutFilter (x : ℝ) : Filter ℂ := 𝓝[{z : ℂ | 0 ≤ z.im}] (-(x : ℂ))
def lowerCutFilter (x : ℝ) : Filter ℂ := 𝓝[{z : ℂ | z.im < 0}] (-(x : ℂ))

def upperPhase (nu : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * nu)
def lowerPhase (nu : ℂ) : ℂ := Complex.exp (-((Real.pi : ℂ) * Complex.I * nu))

theorem upperPhase_neg (nu : ℂ) : upperPhase (-nu) = lowerPhase nu := by
  unfold upperPhase lowerPhase
  congr 1
  ring

theorem lowerPhase_neg (nu : ℂ) : lowerPhase (-nu) = upperPhase nu := by
  unfold upperPhase lowerPhase
  congr 1
  ring

theorem upperPhase_eq_cos_sin (nu : ℂ) :
    upperPhase nu = Complex.cos ((Real.pi : ℂ) * nu) +
      Complex.sin ((Real.pi : ℂ) * nu) * Complex.I := by
  unfold upperPhase
  rw [show (Real.pi : ℂ) * Complex.I * nu = ((Real.pi : ℂ) * nu) * Complex.I by ring,
    Complex.exp_mul_I]

theorem lowerPhase_eq_cos_sin (nu : ℂ) :
    lowerPhase nu = Complex.cos ((Real.pi : ℂ) * nu) -
      Complex.sin ((Real.pi : ℂ) * nu) * Complex.I := by
  unfold lowerPhase
  rw [show -((Real.pi : ℂ) * Complex.I * nu) = -((Real.pi : ℂ) * nu) * Complex.I by ring,
    ← Complex.cos_sub_sin_I]

theorem log_tendsto_upper {x : ℝ} (hx : 0 < x) :
    Tendsto Complex.log (upperCutFilter x)
      (𝓝 ((Real.log x : ℂ) + (Real.pi : ℂ) * Complex.I)) := by
  have hre : (-(x : ℂ)).re < 0 := by
    simpa only [Complex.neg_re, Complex.ofReal_re] using neg_lt_zero.mpr hx
  have him : (-(x : ℂ)).im = 0 := by simp
  simpa only [upperCutFilter, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using
    Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him

theorem log_tendsto_lower {x : ℝ} (hx : 0 < x) :
    Tendsto Complex.log (lowerCutFilter x)
      (𝓝 ((Real.log x : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
  have hre : (-(x : ℂ)).re < 0 := by
    simpa only [Complex.neg_re, Complex.ofReal_re] using neg_lt_zero.mpr hx
  have him : (-(x : ℂ)).im = 0 := by simp
  simpa only [lowerCutFilter, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] using
    Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him

theorem cpow_tendsto_upper (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => z ^ nu) (upperCutFilter x) (𝓝 (upperPhase nu * (x : ℂ) ^ nu)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h := Complex.continuous_exp.continuousAt.tendsto.comp ((log_tendsto_upper hx).mul_const nu)
  have hvalue : Complex.exp (((Real.log x : ℂ) + (Real.pi : ℂ) * Complex.I) * nu) =
      upperPhase nu * (x : ℂ) ^ nu := by
    unfold upperPhase
    rw [Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le, ← Complex.exp_add]
    congr 1
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_ne_nhdsWithin (neg_ne_zero.mpr hxC)] with z hz
  rw [Complex.cpow_def_of_ne_zero hz]

theorem cpow_tendsto_lower (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => z ^ nu) (lowerCutFilter x) (𝓝 (lowerPhase nu * (x : ℂ) ^ nu)) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h := Complex.continuous_exp.continuousAt.tendsto.comp ((log_tendsto_lower hx).mul_const nu)
  have hvalue : Complex.exp (((Real.log x : ℂ) - (Real.pi : ℂ) * Complex.I) * nu) =
      lowerPhase nu * (x : ℂ) ^ nu := by
    unfold lowerPhase
    rw [Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le, ← Complex.exp_add]
    congr 1
    ring
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_ne_nhdsWithin (neg_ne_zero.mpr hxC)] with z hz
  rw [Complex.cpow_def_of_ne_zero hz]

theorem half_tendsto_upper (x : ℝ) :
    Tendsto (fun z : ℂ => z / 2) (upperCutFilter x) (upperCutFilter (x / 2)) := by
  unfold upperCutFilter
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := ((continuous_id.div_const (2 : ℂ)).tendsto (-(x : ℂ))).mono_left nhdsWithin_le_nhds
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, neg_div] using h
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [Complex.div_ofNat_im] using div_nonneg hz (by norm_num : (0 : ℝ) ≤ 2)

theorem half_tendsto_lower (x : ℝ) :
    Tendsto (fun z : ℂ => z / 2) (lowerCutFilter x) (lowerCutFilter (x / 2)) := by
  unfold lowerCutFilter
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := ((continuous_id.div_const (2 : ℂ)).tendsto (-(x : ℂ))).mono_left nhdsWithin_le_nhds
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat, neg_div] using h
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa only [Complex.div_ofNat_im] using div_neg_of_neg_of_pos hz (by norm_num : (0 : ℝ) < 2)

theorem half_log_tendsto_upper {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => Complex.log (z / 2)) (upperCutFilter x)
      (𝓝 ((Real.log (x / 2) : ℂ) + (Real.pi : ℂ) * Complex.I)) :=
  (log_tendsto_upper (half_pos hx)).comp (half_tendsto_upper x)

theorem half_log_tendsto_lower {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => Complex.log (z / 2)) (lowerCutFilter x)
      (𝓝 ((Real.log (x / 2) : ℂ) - (Real.pi : ℂ) * Complex.I)) :=
  (log_tendsto_lower (half_pos hx)).comp (half_tendsto_lower x)

theorem half_cpow_tendsto_upper (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => (z / 2) ^ nu) (upperCutFilter x)
      (𝓝 (upperPhase nu * ((x / 2 : ℝ) : ℂ) ^ nu)) :=
  (cpow_tendsto_upper nu (half_pos hx)).comp (half_tendsto_upper x)

theorem half_cpow_tendsto_lower (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun z : ℂ => (z / 2) ^ nu) (lowerCutFilter x)
      (𝓝 (lowerPhase nu * ((x / 2 : ℝ) : ℂ) ^ nu)) :=
  (cpow_tendsto_lower nu (half_pos hx)).comp (half_tendsto_lower x)

end
end ImbalancedChen.Part3.ActualNegativeCutPowerLimits20261026b
