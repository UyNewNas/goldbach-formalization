import ImbalancedChen.Part3ActualComplexKIConnection
import ImbalancedChen.Part3GeneralIOrderHolomorphy
import ImbalancedChen.Part3ComplexOrderKHolomorphic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
The removable order-zero value of the actual K/I connection is the negative
complex order derivative of the literal I series. The proof uses the actual
positive-strip connection, the proved order derivative, and derivative-limit
definitions for both the odd I numerator and sin(pi*nu). No l'Hopital,
connection identity, or removable-value supplier is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped Topology
open Filter Set

namespace ImbalancedChen.Part3.ActualZeroOrderKIConnectionSourceOnly

open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly
open ComplexOrderKBridgeSourceOnly ComplexOrderKHolomorphicSourceOnly
open ImaginaryOrderKBesselSourceOnly RealOrderKExceptionalSourceOnly

/-- The actual odd I numerator has its true derivative at order zero. -/
theorem hasDerivAt_generalI_odd_order_zero {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun nu : ℂ => generalI (-nu) q - generalI nu q)
      (-2 * deriv (fun nu : ℂ => generalI nu q) 0) 0 := by
  have hp := (analyticAt_generalI_order (0 : ℂ) (by norm_num) hq).differentiableAt.hasDerivAt
  have hm := (analyticAt_generalI_order (-(0 : ℂ)) (by norm_num) hq).differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun nu : ℂ => generalI (-nu) q)
      (-deriv (fun nu : ℂ => generalI nu q) 0) 0 := by
    simpa only [neg_zero, mul_neg_one] using hm.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  convert hn.sub hp using 1 <;> ring

/-- The order-zero removable limit is computed directly from two actual
derivative limits on the complex punctured neighborhood. -/
theorem tendsto_actualKIConnection_order_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (fun nu : ℂ =>
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
        (generalI (-nu) q - generalI nu q))
      (𝓝[≠] 0) (𝓝 (-deriv (fun nu : ℂ => generalI nu q) 0)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : Tendsto (fun nu : ℂ => (generalI (-nu) q - generalI nu q) / nu)
      (𝓝[≠] 0) (𝓝 (-2 * deriv (fun nu : ℂ => generalI nu q) 0)) := by
    simpa only [zero_add, neg_zero, sub_self, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using (hasDerivAt_generalI_odd_order_zero hq).tendsto_slope_zero
  have hs : HasDerivAt (fun nu : ℂ => Complex.sin ((Real.pi : ℂ) * nu))
      (Real.pi : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).csin
  have hslope : Tendsto (fun nu : ℂ => Complex.sin ((Real.pi : ℂ) * nu) / nu)
      (𝓝[≠] 0) (𝓝 (Real.pi : ℂ)) := by
    simpa only [zero_add, mul_zero, Complex.sin_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hs.tendsto_slope_zero
  have hratio := (hg.div hslope hpi).const_mul ((Real.pi : ℂ) / 2)
  have hconstant : (Real.pi : ℂ) / 2 *
      ((-2 * deriv (fun nu : ℂ => generalI nu q) 0) / (Real.pi : ℂ)) =
        -deriv (fun nu : ℂ => generalI nu q) 0 := by
    field_simp [hpi]
    <;> ring
  rw [hconstant] at hratio
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with nu hnu
  have hn : nu ≠ 0 := hnu
  rw [div_div_div_cancel_right₀ hn]
  ring

private theorem tendsto_positive_real_order_punctured :
    Tendsto (fun eps : ℝ => (eps : ℂ)) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
  have ht : Tendsto (fun eps : ℝ => (eps : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have h0 : Tendsto (fun eps : ℝ => (eps : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
      simpa using Complex.continuous_ofReal.tendsto 0
    exact h0.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ht
  filter_upwards [self_mem_nhdsWithin] with eps heps
  change (eps : ℂ) ≠ 0
  exact Complex.ofReal_ne_zero.mpr heps.ne'

/-- The genuine K_0 integral equals the negative order derivative of the
genuine convergent I-series. This fills the excluded order-zero connection. -/
theorem complexOrderK_zero_eq_neg_order_deriv {q : ℝ} (hq : 0 < q) :
    complexOrderK 0 q = -deriv (fun nu : ℂ => generalI nu q) 0 := by
  have hk : ContinuousAt (fun nu : ℂ => complexOrderK nu q) 0 :=
    (complexOrderK_hasDerivAt 0 q hq (by norm_num)).continuousAt
  have hpath := tendsto_positive_real_order_punctured
  have hklim := hk.tendsto.comp (hpath.mono_right nhdsWithin_le_nhds)
  have hrlim := (tendsto_actualKIConnection_order_zero hq).comp hpath
  have heq : (fun eps : ℝ => complexOrderK (eps : ℂ) q) =ᶠ[𝓝[>] 0]
      (fun eps : ℝ => (Real.pi : ℂ) /
        (2 * Complex.sin ((Real.pi : ℂ) * (eps : ℂ))) *
          (generalI (-(eps : ℂ)) q - generalI (eps : ℂ) q)) := by
    have hlt : ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < 1 :=
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with eps heps heps1
    exact ActualComplexKIConnection.complexOrderK_eq_generalI_sub
      (by simpa using heps) (by simpa using heps1) hq
  exact tendsto_nhds_unique hklim (hrlim.congr' heq.symm)

theorem imaginaryOrderK_zero_eq_neg_order_deriv {q : ℝ} (hq : 0 < q) :
    (imaginaryOrderK 0 q : ℂ) = -deriv (fun nu : ℂ => generalI nu q) 0 := by
  have hb := complexOrderK_imaginary 0 q
  simp only [mul_zero, Complex.ofReal_zero, zero_mul] at hb
  rw [← hb]
  exact complexOrderK_zero_eq_neg_order_deriv hq

theorem realOrderK_zero_eq_neg_order_deriv {q : ℝ} (hq : 0 < q) :
    (realOrderK 0 q : ℂ) = -deriv (fun nu : ℂ => generalI nu q) 0 := by
  have hb := complexOrderK_real 0 q
  simp only [Complex.ofReal_zero] at hb
  rw [← hb]
  exact complexOrderK_zero_eq_neg_order_deriv hq

end ImbalancedChen.Part3.ActualZeroOrderKIConnectionSourceOnly
