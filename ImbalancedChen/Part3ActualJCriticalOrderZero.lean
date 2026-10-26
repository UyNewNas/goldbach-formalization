import ImbalancedChen.Part3ActualJLocalOrderHolomorphic
import ImbalancedChen.Part3ActualGeneralJComplexArgument
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The literal order-zero primitive for the actual ordinary J is
  (J_(2*i*z)(q) - J_(-2*i*z)(q)) / sinh(pi*z).
Its extension is defined using actual dslope, proved analytic at zero using
the preceding genuine Poisson order-holomorphy theorem, and identified with
the literal quotient off zero. Its value is (4*i/pi) times the actual J
order derivative at zero, with the order derivative evaluated by a proved
Poisson/Gamma integral formula in the imported source.

The raw quotient is purely imaginary on the real axis. Multiplying by i
makes it real. Both conventions are provided explicitly, without declaring
either one to be the manuscript's automorphic Kuznetsov normalization.
-/

namespace ImbalancedChen.Part3.ActualJCriticalOrderZero20261026a

noncomputable section
open Set Filter Complex
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualGeneralJComplexArgument20261025a
open ActualJLocalOrderHolomorphic20261026a

def oddOrderJ (q : ℝ) (z : ℂ) : ℂ :=
  generalJ (2 * I * z) q - generalJ (-(2 * I * z)) q

def criticalSinh (z : ℂ) : ℂ := Complex.sinh ((Real.pi : ℂ) * z)

/-- Actual analytic extension of the raw quotient, including its native
derivative value rather than totalized zero division at z=0. -/
def criticalJQuotient (q : ℝ) (z : ℂ) : ℂ :=
  dslope (oddOrderJ q) 0 z / dslope criticalSinh 0 z

/-- Explicit i normalization. No automorphic normalization is claimed. -/
def criticalJRealKernel (q : ℝ) (z : ℂ) : ℂ := I * criticalJQuotient q z

private theorem oddOrderJ_zero (q : ℝ) : oddOrderJ q 0 = 0 := by
  simp [oddOrderJ]

private theorem criticalSinh_zero : criticalSinh 0 = 0 := by
  simp [criticalSinh]

theorem oddOrderJ_hasDerivAt_zero {q : ℝ} (hq : 0 < q) :
    HasDerivAt (oddOrderJ q) (4 * I * actualJOrderDerivative 0 q) 0 := by
  have hJ := generalJ_order_hasDerivAt
    (nu := (0 : ℂ)) (by norm_num [orderHalfPlane]) hq
  have hp : HasDerivAt (fun z : ℂ => 2 * I * z) (2 * I) 0 :=
    (hasDerivAt_id 0).const_mul (2 * I)
  have hn := hp.neg
  have h := (hJ.comp 0 (by simpa using hp)).sub (hJ.comp 0 (by simpa using hn))
  convert h using 1 <;> dsimp only [oddOrderJ] <;> ring

theorem criticalSinh_hasDerivAt_zero :
    HasDerivAt criticalSinh (Real.pi : ℂ) 0 := by
  have h := ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).csinh
  simpa only [criticalSinh, mul_zero, Complex.cosh_zero, one_mul] using h

theorem criticalJQuotient_zero {q : ℝ} (hq : 0 < q) :
    criticalJQuotient q 0 =
      (4 * I / (Real.pi : ℂ)) * actualJOrderDerivative 0 q := by
  rw [criticalJQuotient, dslope_same, dslope_same,
    (oddOrderJ_hasDerivAt_zero hq).deriv, criticalSinh_hasDerivAt_zero.deriv]
  ring

/-- Literal off-zero quotient, valid even where the hyperbolic sine is
totalized to zero: the common nonzero z cancels algebraically. -/
theorem criticalJQuotient_eq {q : ℝ} {z : ℂ} (hz : z ≠ 0) :
    criticalJQuotient q z =
      (generalJ (2 * I * z) q - generalJ (-(2 * I * z)) q) /
        Complex.sinh ((Real.pi : ℂ) * z) := by
  rw [criticalJQuotient, dslope_of_ne _ hz, dslope_of_ne _ hz,
    slope_def_module, slope_def_module, oddOrderJ_zero, criticalSinh_zero]
  simp only [sub_zero, smul_eq_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero hz)

private def orderStrip : Set ℂ := {z | |z.im| < 1 / 8}

private theorem orderStrip_open : IsOpen orderStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

private theorem orderStrip_zero : (0 : ℂ) ∈ orderStrip := by
  norm_num [orderStrip]

private theorem oddOrderJ_differentiableOn {q : ℝ} (hq : 0 < q) :
    DifferentiableOn ℂ (oddOrderJ q) orderStrip := by
  intro z hz
  have hi : -(1 / 8 : ℝ) < z.im ∧ z.im < 1 / 8 := abs_lt.mp hz
  have hp : 2 * I * z ∈ orderHalfPlane := by
    dsimp [orderHalfPlane]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hn : -(2 * I * z) ∈ orderHalfPlane := by
    dsimp [orderHalfPlane]
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hleft := (generalJ_order_hasDerivAt hp hq).differentiableAt.comp z
    (show DifferentiableAt ℂ (fun w : ℂ => 2 * I * w) z by fun_prop)
  have hright := (generalJ_order_hasDerivAt hn hq).differentiableAt.comp z
    (show DifferentiableAt ℂ (fun w : ℂ => -(2 * I * w)) z by fun_prop)
  exact (hleft.sub hright).differentiableWithinAt

/-- The removable extension is genuinely analytic at zero, from proved
actual J order holomorphy rather than an analyticity hypothesis. -/
theorem criticalJQuotient_analyticAt_zero {q : ℝ} (hq : 0 < q) :
    AnalyticAt ℂ (criticalJQuotient q) 0 := by
  have hn : AnalyticAt ℂ (dslope (oddOrderJ q) 0) 0 :=
    ((differentiableOn_dslope (orderStrip_open.mem_nhds orderStrip_zero)).2
      (oddOrderJ_differentiableOn hq)).analyticAt
        (orderStrip_open.mem_nhds orderStrip_zero)
  have hd : DifferentiableOn ℂ criticalSinh (univ : Set ℂ) := by
    intro z _
    exact (show DifferentiableAt ℂ criticalSinh z by
      dsimp [criticalSinh]
      fun_prop).differentiableWithinAt
  have hda : AnalyticAt ℂ (dslope criticalSinh 0) 0 :=
    ((differentiableOn_dslope (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 (0 : ℂ))).2 hd).analyticAt
      Filter.univ_mem
  have hdnz : dslope criticalSinh 0 0 ≠ 0 := by
    rw [dslope_same, criticalSinh_hasDerivAt_zero.deriv]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  exact hn.div hda hdnz

theorem criticalJRealKernel_analyticAt_zero {q : ℝ} (hq : 0 < q) :
    AnalyticAt ℂ (criticalJRealKernel q) 0 :=
  analyticAt_const.mul (criticalJQuotient_analyticAt_zero hq)

/-- Exact complex removable limit, including the factor from BOTH orders
2*i*z and -2*i*z. -/
theorem criticalJQuotient_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun z : ℂ =>
      (generalJ (2 * I * z) q - generalJ (-(2 * I * z)) q) /
        Complex.sinh ((Real.pi : ℂ) * z)) (𝓝[≠] 0)
      (𝓝 ((4 * I / (Real.pi : ℂ)) * actualJOrderDerivative 0 q)) := by
  have h := (criticalJQuotient_analyticAt_zero hq).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds
  rw [criticalJQuotient_zero hq] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact criticalJQuotient_eq hz

theorem criticalJQuotient_even (q : ℝ) (z : ℂ) :
    criticalJQuotient q (-z) = criticalJQuotient q z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [criticalJQuotient_eq (neg_ne_zero.mpr hz), criticalJQuotient_eq hz]
    have h1 : 2 * I * (-z) = -(2 * I * z) := by ring
    have h2 : (Real.pi : ℂ) * (-z) = -((Real.pi : ℂ) * z) := by ring
    rw [h1, neg_neg, h2, Complex.sinh_neg]
    rw [show generalJ (-(2 * I * z)) q - generalJ (2 * I * z) q =
      -(generalJ (2 * I * z) q - generalJ (-(2 * I * z)) q) by ring,
      neg_div_neg_eq]

/-- The literal real-height form uses sinh(pi*t), with no hidden rescaling
of t. Its limit therefore has the exact 4*i/pi factor. -/
theorem criticalJQuotient_real_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun t : ℝ =>
      (generalJ (2 * I * (t : ℂ)) q - generalJ (-(2 * I * (t : ℂ))) q) /
        (Real.sinh (Real.pi * t) : ℂ)) (𝓝[≠] 0)
      (𝓝 ((4 * I / (Real.pi : ℂ)) * actualJOrderDerivative 0 q)) := by
  have hc : ContinuousAt (fun t : ℝ => criticalJQuotient q (t : ℂ)) 0 :=
    (criticalJQuotient_analyticAt_zero hq).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds : (𝓝[≠] (0 : ℝ)) ≤ 𝓝 0)
  simp only [Complex.ofReal_zero, criticalJQuotient_zero hq] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [criticalJQuotient_eq (Complex.ofReal_ne_zero.mpr ht),
    Complex.ofReal_sinh, Complex.ofReal_mul]

theorem criticalJRealKernel_even (q : ℝ) (z : ℂ) :
    criticalJRealKernel q (-z) = criticalJRealKernel q z := by
  rw [criticalJRealKernel, criticalJQuotient_even, criticalJRealKernel]

private theorem conj_generalJ (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    conj (generalJ nu q) = generalJ (conj nu) q := by
  have h := conj_generalJComplex nu (z := (q : ℂ)) (by simp [hq])
  simpa only [generalJComplex_ofReal, Complex.conj_ofReal] using h

theorem actualJOrderDerivative_zero_conj {q : ℝ} (hq : 0 < q) :
    conj (actualJOrderDerivative 0 q) = actualJOrderDerivative 0 q := by
  have h := generalJ_order_hasDerivAt (nu := (0 : ℂ))
    (by norm_num [orderHalfPlane]) hq
  have hc := h.conj_conj
  have heq : (conj ∘ (fun z : ℂ => generalJ z q) ∘ conj) =
      (fun z : ℂ => generalJ z q) := by
    funext z
    simp only [Function.comp_apply, conj_generalJ _ hq, Complex.conj_conj]
  rw [heq, map_zero] at hc
  exact hc.unique h

/-- The raw quotient is purely imaginary for real t, including its
removable value at t=0. This records the normalization-sensitive reality. -/
theorem criticalJQuotient_conj_real {q : ℝ} (hq : 0 < q) (t : ℝ) :
    conj (criticalJQuotient q (t : ℂ)) = -criticalJQuotient q (t : ℂ) := by
  by_cases ht : t = 0
  · subst t
    rw [Complex.ofReal_zero, criticalJQuotient_zero hq]
    simp only [map_mul, map_div₀, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
      actualJOrderDerivative_zero_conj hq]
    ring
  · rw [criticalJQuotient_eq (Complex.ofReal_ne_zero.mpr ht)]
    have hc : conj (2 * I * (t : ℂ)) = -(2 * I * (t : ℂ)) := by
      simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hs : conj (Complex.sinh ((Real.pi : ℂ) * (t : ℂ))) =
        Complex.sinh ((Real.pi : ℂ) * (t : ℂ)) := by
      rw [← Complex.sinh_conj]
      simp
    rw [map_div₀, map_sub, conj_generalJ _ hq, conj_generalJ _ hq,
      hc, map_neg, hc, neg_neg, hs]
    rw [show generalJ (-(2 * I * (t : ℂ))) q - generalJ (2 * I * (t : ℂ)) q =
      -(generalJ (2 * I * (t : ℂ)) q - generalJ (-(2 * I * (t : ℂ))) q) by ring,
      neg_div]

theorem criticalJQuotient_re_zero {q : ℝ} (hq : 0 < q) (t : ℝ) :
    (criticalJQuotient q (t : ℂ)).re = 0 := by
  have h := congrArg Complex.re (criticalJQuotient_conj_real hq t)
  simp only [Complex.conj_re, Complex.neg_re] at h
  linarith

theorem criticalJRealKernel_im_zero {q : ℝ} (hq : 0 < q) (t : ℝ) :
    (criticalJRealKernel q (t : ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [criticalJRealKernel, map_mul, Complex.conj_I,
    criticalJQuotient_conj_real hq t, neg_mul_neg]

theorem criticalJRealKernel_zero {q : ℝ} (hq : 0 < q) :
    criticalJRealKernel q 0 = -(4 / (Real.pi : ℂ)) * actualJOrderDerivative 0 q := by
  rw [criticalJRealKernel, criticalJQuotient_zero hq]
  calc
    I * ((4 * I / (Real.pi : ℂ)) * actualJOrderDerivative 0 q) =
      (4 / (Real.pi : ℂ)) * (I * I) * actualJOrderDerivative 0 q := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

end
end ImbalancedChen.Part3.ActualJCriticalOrderZero20261026a
