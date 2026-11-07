import ImbalancedChen.Part3GeneralComplexISeries
import ImbalancedChen.Part3GeneralIQODE
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Actual small-q leading terms and the general I-pair Wronskian limit

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The functions here are the literal convergent Gamma-coefficient I-series.
Their scaled leading values follow from continuity of the actual entire
core at zero and its zeroth coefficient. The derivative limit uses the
proved derivative of that same series, not an assumed leading asymptotic.
Both orders are legal on -1 < Re nu < 1. The Wronskian convention is
I_nu * I_{-nu}' - I_nu' * I_{-nu}, giving a negative constant.

Reflection and the global reciprocal-Gamma recurrence identify the limit
as -2*sin(pi*nu)/pi. The actual qODE then proves Abel constancy on q>0,
so the small-q limit identifies the global Wronskian constant.
KL and automorphic spectral measures and the genuine P3 saving remain OPEN.
-/

namespace ImbalancedChen.Part3.GeneralISmallQWronskian20261025a

noncomputable section
open Complex Filter Set Topology
open GeneralComplexISeriesSourceOnly GeneralIQODE20261025a

/-- The reflection constant for the two actual zeroth coefficients. The
reciprocal-Gamma recurrence makes this algebra valid even at Gamma poles. -/
theorem gamma_leading_wronskian_constant (nu : ℂ) :
    (Complex.Gamma (nu + 1))⁻¹ * (-nu * (Complex.Gamma (1 - nu))⁻¹) -
      (nu * (Complex.Gamma (nu + 1))⁻¹) * (Complex.Gamma (1 - nu))⁻¹ =
        -2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ) := by
  calc
    _ = -2 * ((nu * (Complex.Gamma (nu + 1))⁻¹) *
        (Complex.Gamma (1 - nu))⁻¹) := by ring
    _ = -2 * ((Complex.Gamma nu)⁻¹ * (Complex.Gamma (1 - nu))⁻¹) := by
      rw [← Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
    _ = -2 * (Complex.Gamma nu * Complex.Gamma (1 - nu))⁻¹ := by
      rw [mul_inv]
    _ = -2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ) := by
      rw [Complex.Gamma_mul_Gamma_one_sub, inv_div]
      ring

private theorem tendsto_core_coordinate_zero :
    Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have h : Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using
      (show Continuous (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
        from by fun_prop).tendsto 0
  exact h.mono_left nhdsWithin_le_nhds

/-- The actual core evaluated at q²/4 tends to its actual zeroth term. -/
theorem tendsto_generalICore_small_q {nu : ℂ} (hnu : -1 < nu.re) :
    Tendsto (fun q : ℝ => generalICore nu (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 ((Complex.Gamma (nu + 1))⁻¹)) := by
  simpa only [generalICore_zero] using
    ((continuous_generalICore hnu).tendsto 0).comp tendsto_core_coordinate_zero

/-- Exact scaling cancels the principal positive-base power. -/
theorem generalI_scaled_eq_core (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    (((q / 2 : ℝ) : ℂ) ^ (-nu)) * generalI nu q =
      generalICore nu (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
  have hbase : ((q / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne'
  rw [generalI, ← mul_assoc, ← Complex.cpow_add (-nu) nu hbase,
    neg_add_cancel, Complex.cpow_zero, one_mul]

/-- Actual leading small-q asymptotic, without a leading-term hypothesis. -/
theorem tendsto_scaled_generalI_zero {nu : ℂ} (hnu : -1 < nu.re) :
    Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (-nu)) * generalI nu q)
      (𝓝[>] 0) (𝓝 ((Complex.Gamma (nu + 1))⁻¹)) := by
  apply (tendsto_generalICore_small_q hnu).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (generalI_scaled_eq_core nu hq).symm

/-- Leading term of the actual real-q derivative. The extra q² core term
vanishes by convergence of the actual shifted-order series. -/
theorem tendsto_scaled_generalI_deriv_zero {nu : ℂ} (hnu : -1 < nu.re) :
    Tendsto (fun q : ℝ => (q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) *
      deriv (generalI nu) q)
      (𝓝[>] 0) (𝓝 (nu * (Complex.Gamma (nu + 1))⁻¹)) := by
  have hshift : -1 < (nu + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hnu]
  have hmain := (tendsto_generalICore_small_q hnu).const_mul nu
  have htail := (tendsto_core_coordinate_zero.const_mul (2 : ℂ)).mul
    (tendsto_generalICore_small_q hshift)
  have hlim : Tendsto
      (fun q : ℝ => nu * generalICore nu (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) +
        2 * (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) *
          generalICore (nu + 1) (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 (nu * (Complex.Gamma (nu + 1))⁻¹)) := by
    simpa only [mul_zero, zero_mul, add_zero] using hmain.add htail
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (generalI_normalized_first hnu hq).symm

/-- The actual I-pair Wronskian, with a fixed order and sign convention. -/
def generalIWronskian (nu : ℂ) (q : ℝ) : ℂ :=
  generalI nu q * deriv (generalI (-nu)) q -
    deriv (generalI nu) q * generalI (-nu) q

/-- Products of normalized actual functions remove all potentially
singular individual powers before the q→0 limit is taken. -/
theorem q_mul_generalIWronskian_eq_scaled (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * generalIWronskian nu q =
      ((((q / 2 : ℝ) : ℂ) ^ (-nu)) * generalI nu q) *
        ((q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-(-nu))) * deriv (generalI (-nu)) q) -
      ((q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) * deriv (generalI nu) q) *
        ((((q / 2 : ℝ) : ℂ) ^ (-(-nu))) * generalI (-nu) q) := by
  have hbase : ((q / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne'
  have hcancel : (((q / 2 : ℝ) : ℂ) ^ (-nu)) *
      (((q / 2 : ℝ) : ℂ) ^ nu) = 1 := by
    rw [← Complex.cpow_add (-nu) nu hbase, neg_add_cancel, Complex.cpow_zero]
  simp only [neg_neg]
  calc
    (q : ℂ) * generalIWronskian nu q =
        ((((q / 2 : ℝ) : ℂ) ^ (-nu)) * (((q / 2 : ℝ) : ℂ) ^ nu)) *
          ((q : ℂ) * generalIWronskian nu q) := by rw [hcancel, one_mul]
    _ = _ := by unfold generalIWronskian; ring

/-- The genuine small-q Wronskian constant throughout the common strip.
No Wronskian, connection formula, or leading asymptotic is an assumption. -/
theorem tendsto_q_mul_generalIWronskian_zero {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1) :
    Tendsto (fun q : ℝ => (q : ℂ) * generalIWronskian nu q)
      (𝓝[>] 0) (𝓝 (-2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ))) := by
  have hneg : -1 < (-nu).re := by
    simp only [Complex.neg_re]
    linarith only [hnuUpper]
  have h := ((tendsto_scaled_generalI_zero hnuLower).mul
      (tendsto_scaled_generalI_deriv_zero hneg)).sub
    ((tendsto_scaled_generalI_deriv_zero hnuLower).mul
      (tendsto_scaled_generalI_zero hneg))
  have hconstant :
      (Complex.Gamma (nu + 1))⁻¹ * (-nu * (Complex.Gamma (-nu + 1))⁻¹) -
        (nu * (Complex.Gamma (nu + 1))⁻¹) * (Complex.Gamma (-nu + 1))⁻¹ =
          -2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ) := by
    rw [show -nu + 1 = 1 - nu by ring]
    exact gamma_leading_wronskian_constant nu
  rw [hconstant] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (q_mul_generalIWronskian_eq_scaled nu hq).symm

/-- Abel's identity for the two actual I-series, obtained from their proved
qODE and actual first and second derivatives. No Wronskian is supplied. -/
theorem q_mul_generalIWronskian_hasDerivAt_zero {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * generalIWronskian nu x) 0 q := by
  have hneg : -1 < (-nu).re := by
    simp only [Complex.neg_re]
    linarith only [hnuUpper]
  have hy := (generalI_differentiableAt hnuLower hq).hasDerivAt
  have hz := (generalI_differentiableAt hneg hq).hasDerivAt
  have hy' := (generalI_deriv_differentiableAt hnuLower hq).hasDerivAt
  have hz' := (generalI_deriv_differentiableAt hneg hq).hasDerivAt
  have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 q := Complex.ofRealCLM.hasDerivAt
  let D : ℂ := generalIWronskian nu q + (q : ℂ) *
    (generalI nu q * deriv (deriv (generalI (-nu))) q -
      deriv (deriv (generalI nu)) q * generalI (-nu) q)
  have hcalc : HasDerivAt (fun x : ℝ => (x : ℂ) * generalIWronskian nu x) D q := by
    convert hid.mul ((hy.mul hz').sub (hy'.mul hz)) using 1 <;>
      dsimp only [D, generalIWronskian] <;> ring
  have hyODE := generalI_modifiedBessel_equation hnuLower hq
  have hzODE := generalI_modifiedBessel_equation hneg hq
  simp only [neg_sq] at hzODE
  have hqD : (q : ℂ) * D = 0 := by
    dsimp only [D, generalIWronskian]
    linear_combination (generalI nu q) * hzODE - (generalI (-nu) q) * hyODE
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hD : D = 0 := (mul_eq_zero.mp hqD).resolve_left hqC
  simpa only [hD] using hcalc

/-- The normalized Wronskian is constant on the whole positive half-line. -/
theorem q_mul_generalIWronskian_eq {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1)
    {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (q₁ : ℂ) * generalIWronskian nu q₁ = (q₂ : ℂ) * generalIWronskian nu q₂ := by
  have hdiff : DifferentiableOn ℝ
      (fun x : ℝ => (x : ℂ) * generalIWronskian nu x) (Ioi (0 : ℝ)) := by
    intro x hx
    exact (q_mul_generalIWronskian_hasDerivAt_zero hnuLower hnuUpper hx).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn
      (deriv (fun x : ℝ => (x : ℂ) * generalIWronskian nu x)) 0 (Ioi (0 : ℝ)) := by
    intro x hx
    exact (q_mul_generalIWronskian_hasDerivAt_zero hnuLower hnuUpper hx).deriv
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hderiv hq₁ hq₂

/-- General-order exact Wronskian of the two actual convergent I-series.
The common strip includes both real noninteger 0<nu<1 and imaginary orders.
At nu=0 the two functions coincide and the displayed constant is zero. -/
theorem q_mul_generalIWronskian_eq_neg_two_sin {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * generalIWronskian nu q =
      -2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ) := by
  have hconstant : (fun x : ℝ => (x : ℂ) * generalIWronskian nu x) =ᶠ[𝓝[>] 0]
      (fun _ : ℝ => (q : ℂ) * generalIWronskian nu q) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact q_mul_generalIWronskian_eq hnuLower hnuUpper hx hq
  have hlim : Tendsto (fun x : ℝ => (x : ℂ) * generalIWronskian nu x)
      (𝓝[>] 0) (𝓝 ((q : ℂ) * generalIWronskian nu q)) :=
    tendsto_const_nhds.congr' hconstant.symm
  exact tendsto_nhds_unique hlim (tendsto_q_mul_generalIWronskian_zero hnuLower hnuUpper)

end
end ImbalancedChen.Part3.GeneralISmallQWronskian20261025a
