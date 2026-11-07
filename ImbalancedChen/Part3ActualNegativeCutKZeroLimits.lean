import ImbalancedChen.Part3ActualNegativeCutIKLimits
import ImbalancedChen.Part3ActualCutPlaneKZeroModel
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual zero-order upper/lower cut limits. The actual logarithm boundary,
literal I_0 core continuity, and entire order-derivative core continuity
are combined in the proved zero-order formula. Thus
  K_0(-x+i0)=K_0(x)-pi*i*I_0(x),
  K_0(-x-i0)=K_0(x)+pi*i*I_0(x).
No sine quotient is evaluated at zero, no nonzero-order/argument limits
are interchanged, and no continuation formula is assumed. This is the
n=0,m=+/-1 case of the primary DLMF 10.34.E5 checked on 2026-10-26.
The larger-sector E18 product identity and its integral decay remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualNegativeCutKZeroLimits20261026b

noncomputable section
open Set Filter
open scoped Topology
open GeneralComplexISeriesSourceOnly ComplexOrderKBridgeSourceOnly
open ActualComplexArgumentISlit20261026b ActualICoreZeroOrderDerivative20261026b
open ActualCutPlaneKZeroModel20261026b
open ActualNegativeCutPowerLimits20261026b ActualNegativeCutIKLimits20261026b

theorem actual_KZero_positive_log_formula {x : ℝ} (hx : 0 < x) :
    complexOrderK 0 x = -((Real.log (x / 2) : ℂ) * generalI 0 x +
      coreOrderDerivativeZero (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hhalf : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hlog : Complex.log ((x : ℂ) / 2) = (Real.log (x / 2) : ℂ) := by
    rw [hhalf, ← Complex.ofReal_log (half_pos hx).le]
  rw [← cutPlaneKZero_real hx, cutPlaneKZero_eq_formula hxC,
    complexArgumentI_real, hlog, hhalf]

/-- The upper zero-order cut limit from the literal actual derivative
formula, with its positive-real K_0 value supplied independently. -/
theorem actual_KZero_negative_cut_upper {x : ℝ} (hx : 0 < x) :
    Tendsto cutPlaneKZero (upperCutFilter x)
      (𝓝 (complexOrderK 0 x - (Real.pi : ℂ) * Complex.I * generalI 0 x)) := by
  have hI : Tendsto (complexArgumentI 0) (upperCutFilter x) (𝓝 (generalI 0 x)) := by
    simpa only [upperPhase, mul_zero, Complex.exp_zero, one_mul] using
      complexArgumentI_tendsto_upper (nu := 0) (by norm_num) hx
  have hcoordinate : Tendsto (fun z : ℂ => (z / 2) ^ (2 : ℕ)) (upperCutFilter x)
      (𝓝 (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) :=
    (half_square_tendsto x).mono_left nhdsWithin_le_nhds
  have hcore := (coreOrderDerivativeZero_analyticAt (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))).continuousAt.tendsto.comp
    hcoordinate
  have h := (((half_log_tendsto_upper hx).mul hI).add hcore).neg
  have hv : -(((Real.log (x / 2) : ℂ) + (Real.pi : ℂ) * Complex.I) * generalI 0 x +
      coreOrderDerivativeZero (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) =
      complexOrderK 0 x - (Real.pi : ℂ) * Complex.I * generalI 0 x := by
    rw [actual_KZero_positive_log_formula hx]
    ring
  rw [hv] at h
  apply h.congr'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  filter_upwards [eventually_ne_nhdsWithin (neg_ne_zero.mpr hxC)] with z hz
  exact (cutPlaneKZero_eq_formula hz).symm

/-- The lower approach carries the opposite logarithm phase. -/
theorem actual_KZero_negative_cut_lower {x : ℝ} (hx : 0 < x) :
    Tendsto cutPlaneKZero (lowerCutFilter x)
      (𝓝 (complexOrderK 0 x + (Real.pi : ℂ) * Complex.I * generalI 0 x)) := by
  have hI : Tendsto (complexArgumentI 0) (lowerCutFilter x) (𝓝 (generalI 0 x)) := by
    simpa only [lowerPhase, mul_zero, neg_zero, Complex.exp_zero, one_mul] using
      complexArgumentI_tendsto_lower (nu := 0) (by norm_num) hx
  have hcoordinate : Tendsto (fun z : ℂ => (z / 2) ^ (2 : ℕ)) (lowerCutFilter x)
      (𝓝 (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) :=
    (half_square_tendsto x).mono_left nhdsWithin_le_nhds
  have hcore := (coreOrderDerivativeZero_analyticAt (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))).continuousAt.tendsto.comp
    hcoordinate
  have h := (((half_log_tendsto_lower hx).mul hI).add hcore).neg
  have hv : -(((Real.log (x / 2) : ℂ) - (Real.pi : ℂ) * Complex.I) * generalI 0 x +
      coreOrderDerivativeZero (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) =
      complexOrderK 0 x + (Real.pi : ℂ) * Complex.I * generalI 0 x := by
    rw [actual_KZero_positive_log_formula hx]
    ring
  rw [hv] at h
  apply h.congr'
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  filter_upwards [eventually_ne_nhdsWithin (neg_ne_zero.mpr hxC)] with z hz
  exact (cutPlaneKZero_eq_formula hz).symm

end
end ImbalancedChen.Part3.ActualNegativeCutKZeroLimits20261026b
