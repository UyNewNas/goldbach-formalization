import ImbalancedChen.Part3ActualGeneralJBessel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
Actual ordinary J-pair Wronskian, conjugation, and imaginary-order real basis.
The negative quadratic Gamma core gives the true J small-q leading terms;
the ordinary J equation proves Abel constancy on the positive q-axis.
No I Wronskian or I conjugation theorem is imported or used.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualGeneralJWronskian20261025a

noncomputable section
open Complex Filter Set Topology
open GeneralComplexISeriesSourceOnly ActualGeneralJBesselSourceOnly

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
    Tendsto (fun q : ℝ => (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have h : Tendsto (fun q : ℝ => (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))))
      (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa using
      (show Continuous (fun q : ℝ => (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))))
        from by fun_prop).tendsto 0
  exact h.mono_left nhdsWithin_le_nhds

/-- The actual core evaluated at -q²/4 tends to its actual zeroth term. -/
theorem tendsto_generalICore_small_q {nu : ℂ} (hnu : -1 < nu.re) :
    Tendsto (fun q : ℝ => generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))))
      (𝓝[>] 0) (𝓝 ((Complex.Gamma (nu + 1))⁻¹)) := by
  simpa only [generalICore_zero] using
    ((continuous_generalICore hnu).tendsto 0).comp tendsto_core_coordinate_zero

/-- Exact scaling cancels the principal positive-base power. -/
theorem generalJ_scaled_eq_core (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    (((q / 2 : ℝ) : ℂ) ^ (-nu)) * generalJ nu q =
      generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) := by
  have hbase : ((q / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne'
  rw [generalJ, ← mul_assoc, ← Complex.cpow_add (-nu) nu hbase,
    neg_add_cancel, Complex.cpow_zero, one_mul]

/-- Actual leading small-q asymptotic, without a leading-term hypothesis. -/
theorem tendsto_scaled_generalJ_zero {nu : ℂ} (hnu : -1 < nu.re) :
    Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (-nu)) * generalJ nu q)
      (𝓝[>] 0) (𝓝 ((Complex.Gamma (nu + 1))⁻¹)) := by
  apply (tendsto_generalICore_small_q hnu).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (generalJ_scaled_eq_core nu hq).symm

/-- The ordinary J derivative has the negative quadratic core contribution.
This follows from the actual native derivative of the J series. -/
theorem generalJ_normalized_first {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) * deriv (generalJ nu) q =
      nu * generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) +
        2 * (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) *
          generalICore (nu + 1) (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hbase : ((q / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne'
  have hc : (((q / 2 : ℝ) : ℂ) ^ (-nu)) *
      (((q / 2 : ℝ) : ℂ) ^ nu) = 1 := by
    rw [← Complex.cpow_add (-nu) nu hbase, neg_add_cancel, Complex.cpow_zero]
  rw [(generalJ_hasDerivAt hnu hq).deriv]
  change (q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) *
      ((((q / 2 : ℝ) : ℂ) ^ nu) *
        ((nu / (q : ℂ)) * generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ 2)) -
          ((q / 2 : ℝ) : ℂ) * generalICore (nu + 1) (-(((q / 2 : ℝ) : ℂ) ^ 2)))) = _
  calc
    _ = ((((q / 2 : ℝ) : ℂ) ^ (-nu)) * (((q / 2 : ℝ) : ℂ) ^ nu)) *
        (nu * generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ 2)) -
          (q : ℂ) * ((q / 2 : ℝ) : ℂ) *
            generalICore (nu + 1) (-(((q / 2 : ℝ) : ℂ) ^ 2))) := by
      field_simp [hqC]
      <;> ring
    _ = _ := by rw [hc, one_mul]; push_cast; ring

/-- Leading term of the actual real-q derivative. The extra q² core term
vanishes by convergence of the actual shifted-order series. -/
theorem tendsto_scaled_generalJ_deriv_zero {nu : ℂ} (hnu : -1 < nu.re) :
    Tendsto (fun q : ℝ => (q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) *
      deriv (generalJ nu) q)
      (𝓝[>] 0) (𝓝 (nu * (Complex.Gamma (nu + 1))⁻¹)) := by
  have hshift : -1 < (nu + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hnu]
  have hmain := (tendsto_generalICore_small_q hnu).const_mul nu
  have htail := (tendsto_core_coordinate_zero.const_mul (2 : ℂ)).mul
    (tendsto_generalICore_small_q hshift)
  have hlim : Tendsto
      (fun q : ℝ => nu * generalICore nu (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) +
        2 * (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) *
          generalICore (nu + 1) (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))))
      (𝓝[>] 0) (𝓝 (nu * (Complex.Gamma (nu + 1))⁻¹)) := by
    simpa only [mul_zero, zero_mul, add_zero] using hmain.add htail
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (generalJ_normalized_first hnu hq).symm

/-- The actual ordinary J-pair Wronskian, with a fixed sign convention. -/
def generalJWronskian (nu : ℂ) (q : ℝ) : ℂ :=
  generalJ nu q * deriv (generalJ (-nu)) q -
    deriv (generalJ nu) q * generalJ (-nu) q

/-- Products of normalized actual functions remove all potentially
singular individual powers before the q→0 limit is taken. -/
theorem q_mul_generalJWronskian_eq_scaled (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * generalJWronskian nu q =
      ((((q / 2 : ℝ) : ℂ) ^ (-nu)) * generalJ nu q) *
        ((q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-(-nu))) * deriv (generalJ (-nu)) q) -
      ((q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) * deriv (generalJ nu) q) *
        ((((q / 2 : ℝ) : ℂ) ^ (-(-nu))) * generalJ (-nu) q) := by
  have hbase : ((q / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne'
  have hcancel : (((q / 2 : ℝ) : ℂ) ^ (-nu)) *
      (((q / 2 : ℝ) : ℂ) ^ nu) = 1 := by
    rw [← Complex.cpow_add (-nu) nu hbase, neg_add_cancel, Complex.cpow_zero]
  simp only [neg_neg]
  calc
    (q : ℂ) * generalJWronskian nu q =
        ((((q / 2 : ℝ) : ℂ) ^ (-nu)) * (((q / 2 : ℝ) : ℂ) ^ nu)) *
          ((q : ℂ) * generalJWronskian nu q) := by rw [hcancel, one_mul]
    _ = _ := by unfold generalJWronskian; ring

/-- The genuine small-q Wronskian constant throughout the common strip.
No Wronskian, connection formula, or leading asymptotic is an assumption. -/
theorem tendsto_q_mul_generalJWronskian_zero {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1) :
    Tendsto (fun q : ℝ => (q : ℂ) * generalJWronskian nu q)
      (𝓝[>] 0) (𝓝 (-2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ))) := by
  have hneg : -1 < (-nu).re := by
    simp only [Complex.neg_re]
    linarith only [hnuUpper]
  have h := ((tendsto_scaled_generalJ_zero hnuLower).mul
      (tendsto_scaled_generalJ_deriv_zero hneg)).sub
    ((tendsto_scaled_generalJ_deriv_zero hnuLower).mul
      (tendsto_scaled_generalJ_zero hneg))
  have hconstant :
      (Complex.Gamma (nu + 1))⁻¹ * (-nu * (Complex.Gamma (-nu + 1))⁻¹) -
        (nu * (Complex.Gamma (nu + 1))⁻¹) * (Complex.Gamma (-nu + 1))⁻¹ =
          -2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ) := by
    rw [show -nu + 1 = 1 - nu by ring]
    exact gamma_leading_wronskian_constant nu
  rw [hconstant] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (q_mul_generalJWronskian_eq_scaled nu hq).symm

/-- Abel's identity for the two actual ordinary J-series, obtained from their proved
qODE and actual first and second derivatives. No Wronskian is supplied. -/
theorem q_mul_generalJWronskian_hasDerivAt_zero {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * generalJWronskian nu x) 0 q := by
  have hneg : -1 < (-nu).re := by
    simp only [Complex.neg_re]
    linarith only [hnuUpper]
  have hy := (generalJ_differentiableAt hnuLower hq).hasDerivAt
  have hz := (generalJ_differentiableAt hneg hq).hasDerivAt
  have hy' := (generalJ_deriv_differentiableAt hnuLower hq).hasDerivAt
  have hz' := (generalJ_deriv_differentiableAt hneg hq).hasDerivAt
  have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 q := Complex.ofRealCLM.hasDerivAt
  let D : ℂ := generalJWronskian nu q + (q : ℂ) *
    (generalJ nu q * deriv (deriv (generalJ (-nu))) q -
      deriv (deriv (generalJ nu)) q * generalJ (-nu) q)
  have hcalc : HasDerivAt (fun x : ℝ => (x : ℂ) * generalJWronskian nu x) D q := by
    convert hid.mul ((hy.mul hz').sub (hy'.mul hz)) using 1 <;>
      dsimp only [D, generalJWronskian] <;> ring
  have hyODE := generalJ_ordinaryBessel_equation hnuLower hq
  have hzODE := generalJ_ordinaryBessel_equation hneg hq
  simp only [neg_sq] at hzODE
  have hqD : (q : ℂ) * D = 0 := by
    dsimp only [D, generalJWronskian]
    linear_combination (generalJ nu q) * hzODE - (generalJ (-nu) q) * hyODE
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hD : D = 0 := (mul_eq_zero.mp hqD).resolve_left hqC
  simpa only [hD] using hcalc

/-- The normalized Wronskian is constant on the whole positive half-line. -/
theorem q_mul_generalJWronskian_eq {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1)
    {q₁ q₂ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (q₁ : ℂ) * generalJWronskian nu q₁ = (q₂ : ℂ) * generalJWronskian nu q₂ := by
  have hdiff : DifferentiableOn ℝ
      (fun x : ℝ => (x : ℂ) * generalJWronskian nu x) (Ioi (0 : ℝ)) := by
    intro x hx
    exact (q_mul_generalJWronskian_hasDerivAt_zero hnuLower hnuUpper hx).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn
      (deriv (fun x : ℝ => (x : ℂ) * generalJWronskian nu x)) 0 (Ioi (0 : ℝ)) := by
    intro x hx
    exact (q_mul_generalJWronskian_hasDerivAt_zero hnuLower hnuUpper hx).deriv
  exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hderiv hq₁ hq₂

/-- General-order exact Wronskian of the two actual convergent J-series.
The common strip includes both real noninteger 0<nu<1 and imaginary orders.
At nu=0 the two functions coincide and the displayed constant is zero. -/
theorem q_mul_generalJWronskian_eq_neg_two_sin {nu : ℂ}
    (hnuLower : -1 < nu.re) (hnuUpper : nu.re < 1) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * generalJWronskian nu q =
      -2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ) := by
  have hconstant : (fun x : ℝ => (x : ℂ) * generalJWronskian nu x) =ᶠ[𝓝[>] 0]
      (fun _ : ℝ => (q : ℂ) * generalJWronskian nu q) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact q_mul_generalJWronskian_eq hnuLower hnuUpper hx hq
  have hlim : Tendsto (fun x : ℝ => (x : ℂ) * generalJWronskian nu x)
      (𝓝[>] 0) (𝓝 ((q : ℂ) * generalJWronskian nu q)) :=
    tendsto_const_nhds.congr' hconstant.symm
  exact tendsto_nhds_unique hlim (tendsto_q_mul_generalJWronskian_zero hnuLower hnuUpper)


private theorem conj_coefficient (nu : ℂ) (n : ℕ) :
    conj (generalICoeff nu n) = generalICoeff (conj nu) n := by
  simp [generalICoeff, ← Complex.Gamma_conj]

private theorem conj_core (nu z : ℂ) :
    conj (generalICore nu z) = generalICore (conj nu) (conj z) := by
  simp only [generalICore, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [map_mul, conj_coefficient, map_pow]

private theorem conj_positive_power (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    conj ((x : ℂ) ^ nu) = (x : ℂ) ^ conj nu := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  simpa only [Complex.conj_ofReal] using (Complex.cpow_conj (x : ℂ) nu harg).symm

/-- Actual ordinary J conjugation from the Gamma coefficients and the
negative quadratic argument, valid for every complex order at q>0. -/
theorem conj_generalJ (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    conj (generalJ nu q) = generalJ (conj nu) q := by
  simp only [generalJ, map_mul, conj_positive_power nu (div_pos hq (by norm_num)),
    conj_core, map_neg, map_pow, Complex.conj_ofReal]

theorem deriv_generalJ_conj {nu : ℂ} (hnu : -1 < nu.re) {q : ℝ} (hq : 0 < q) :
    deriv (generalJ (conj nu)) q = conj (deriv (generalJ nu) q) := by
  have h := (generalJ_differentiableAt hnu hq).hasDerivAt.star
  have hd : HasDerivAt (generalJ (conj nu)) (conj (deriv (generalJ nu) q)) q := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (conj_generalJ nu hx).symm
  exact hd.deriv

theorem generalJ_neg_imaginary_eq_conj (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    generalJ (-((tau : ℂ) * I)) q = conj (generalJ ((tau : ℂ) * I) q) := by
  simpa using (conj_generalJ ((tau : ℂ) * I) hq).symm

theorem deriv_generalJ_neg_imaginary_eq_conj (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (generalJ (-((tau : ℂ) * I))) q = conj (deriv (generalJ ((tau : ℂ) * I)) q) := by
  have hn : -1 < ((tau : ℂ) * I).re := by simp
  simpa using deriv_generalJ_conj hn hq

/-- Genuine real and imaginary ordinary J modes, retaining q as the
physical positive Bessel variable rather than silently replacing q by exp r. -/
def imaginaryJReal (tau q : ℝ) : ℝ := (generalJ ((tau : ℂ) * I) q).re

def imaginaryJImag (tau q : ℝ) : ℝ := (generalJ ((tau : ℂ) * I) q).im

theorem imaginaryJReal_hasDerivAt (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (imaginaryJReal tau) (deriv (generalJ ((tau : ℂ) * I)) q).re q := by
  have hn : -1 < ((tau : ℂ) * I).re := by simp
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt q
    (generalJ_differentiableAt hn hq).hasDerivAt

theorem imaginaryJImag_hasDerivAt (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (imaginaryJImag tau) (deriv (generalJ ((tau : ℂ) * I)) q).im q := by
  have hn : -1 < ((tau : ℂ) * I).re := by simp
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt q
    (generalJ_differentiableAt hn hq).hasDerivAt

private theorem imaginaryJReal_second (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (deriv (imaginaryJReal tau)) q =
      (deriv (deriv (generalJ ((tau : ℂ) * I))) q).re := by
  have hn : -1 < ((tau : ℂ) * I).re := by simp
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt q
    (generalJ_deriv_differentiableAt hn hq).hasDerivAt
  have he : deriv (imaginaryJReal tau) =ᶠ[𝓝 q]
      (fun x : ℝ => (deriv (generalJ ((tau : ℂ) * I)) x).re) := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (imaginaryJReal_hasDerivAt tau hx).deriv
  exact (hd.congr_of_eventuallyEq he).deriv

private theorem imaginaryJImag_second (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (deriv (imaginaryJImag tau)) q =
      (deriv (deriv (generalJ ((tau : ℂ) * I))) q).im := by
  have hn : -1 < ((tau : ℂ) * I).re := by simp
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt q
    (generalJ_deriv_differentiableAt hn hq).hasDerivAt
  have he : deriv (imaginaryJImag tau) =ᶠ[𝓝 q]
      (fun x : ℝ => (deriv (generalJ ((tau : ℂ) * I)) x).im) := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact (imaginaryJImag_hasDerivAt tau hx).deriv
  exact (hd.congr_of_eventuallyEq he).deriv

private theorem imaginary_ordinary_coefficient (tau q : ℝ) :
    (q : ℂ) ^ 2 - ((tau : ℂ) * I) ^ 2 = ((q ^ 2 + tau ^ 2 : ℝ) : ℂ) := by
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

/-- Both real modes solve the actual ordinary imaginary-order equation,
with coefficient q²+tau² and the ordinary positive q² sign. -/
theorem imaginaryJReal_equation (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    q ^ 2 * deriv (deriv (imaginaryJReal tau)) q +
      q * deriv (imaginaryJReal tau) q + (q ^ 2 + tau ^ 2) * imaginaryJReal tau q = 0 := by
  have hn : -1 < ((tau : ℂ) * I).re := by simp
  have hODE := generalJ_ordinaryBessel_equation hn hq
  rw [imaginary_ordinary_coefficient, ← Complex.ofReal_pow] at hODE
  have h := congrArg Complex.re hODE
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.zero_re] at h
  rw [imaginaryJReal_second tau hq, (imaginaryJReal_hasDerivAt tau hq).deriv]
  exact h

theorem imaginaryJImag_equation (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    q ^ 2 * deriv (deriv (imaginaryJImag tau)) q +
      q * deriv (imaginaryJImag tau) q + (q ^ 2 + tau ^ 2) * imaginaryJImag tau q = 0 := by
  have hn : -1 < ((tau : ℂ) * I).re := by simp
  have hODE := generalJ_ordinaryBessel_equation hn hq
  rw [imaginary_ordinary_coefficient, ← Complex.ofReal_pow] at hODE
  have h := congrArg Complex.im hODE
  simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.zero_im] at h
  rw [imaginaryJImag_second tau hq, (imaginaryJImag_hasDerivAt tau hq).deriv]
  exact h

/-- The actual ordinary J/conjugate-J Wronskian at imaginary order. -/
theorem q_mul_generalJ_conjugate_wronskian (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * (generalJ ((tau : ℂ) * I) q * conj (deriv (generalJ ((tau : ℂ) * I)) q) -
      deriv (generalJ ((tau : ℂ) * I)) q * conj (generalJ ((tau : ℂ) * I) q)) =
        -2 * ((Real.sinh (Real.pi * tau) / Real.pi : ℝ) : ℂ) * I := by
  have hL : -1 < ((tau : ℂ) * I).re := by simp
  have hU : ((tau : ℂ) * I).re < 1 := by simp
  have hW := q_mul_generalJWronskian_eq_neg_two_sin hL hU hq
  rw [generalJWronskian, generalJ_neg_imaginary_eq_conj tau hq,
    deriv_generalJ_neg_imaginary_eq_conj tau hq] at hW
  have hsin : Complex.sin ((Real.pi : ℂ) * ((tau : ℂ) * I)) =
      (Real.sinh (Real.pi * tau) : ℂ) * I := by
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [hsin] at hW
  calc
    _ = -2 * ((Real.sinh (Real.pi * tau) : ℂ) * I) / (Real.pi : ℂ) := hW
    _ = _ := by push_cast; ring

/-- The real/imaginary ordinary J modes have a genuine nonzero weighted
Wronskian. The unweighted Wronskian is this constant divided by q. -/
theorem imaginaryJ_q_wronskian (tau : ℝ) {q : ℝ} (hq : 0 < q) :
    q * (imaginaryJReal tau q * deriv (imaginaryJImag tau) q -
      deriv (imaginaryJReal tau) q * imaginaryJImag tau q) =
        Real.sinh (Real.pi * tau) / Real.pi := by
  have h := congrArg Complex.im (q_mul_generalJ_conjugate_wronskian tau hq)
  have hpair (z w : ℂ) :
      (z * conj w - w * conj z).im = -2 * (z.re * w.im - w.re * z.im) := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  simp only [Complex.im_ofReal_mul] at h
  rw [hpair] at h
  simp at h
  have hflat : -2 * (q *
      ((generalJ ((tau : ℂ) * I) q).re * (deriv (generalJ ((tau : ℂ) * I)) q).im -
        (deriv (generalJ ((tau : ℂ) * I)) q).re * (generalJ ((tau : ℂ) * I) q).im)) =
      -2 * (Real.sinh (Real.pi * tau) / Real.pi) := by
    convert h using 1 <;> ring
  rw [(imaginaryJReal_hasDerivAt tau hq).deriv, (imaginaryJImag_hasDerivAt tau hq).deriv]
  unfold imaginaryJReal imaginaryJImag
  linarith only [hflat]

theorem imaginaryJ_wronskian_ne_zero {tau q : ℝ} (htau : tau ≠ 0) (hq : 0 < q) :
    imaginaryJReal tau q * deriv (imaginaryJImag tau) q -
      deriv (imaginaryJReal tau) q * imaginaryJImag tau q ≠ 0 := by
  have hC : Real.sinh (Real.pi * tau) / Real.pi ≠ 0 :=
    div_ne_zero (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero htau)) Real.pi_ne_zero
  intro hz
  have h := imaginaryJ_q_wronskian tau hq
  rw [hz, mul_zero] at h
  exact hC h.symm

/-- Value and native q derivative determine both real coefficients at
any positive q whenever tau is nonzero. No completeness is claimed. -/
theorem imaginaryJ_initial_data_nondegenerate {tau q : ℝ} (htau : tau ≠ 0) (hq : 0 < q)
    (a b : ℝ)
    (hvalue : a * imaginaryJReal tau q + b * imaginaryJImag tau q = 0)
    (hderiv : a * deriv (imaginaryJReal tau) q + b * deriv (imaginaryJImag tau) q = 0) :
    a = 0 ∧ b = 0 := by
  have hW := imaginaryJ_wronskian_ne_zero htau hq
  have ha : a * (imaginaryJReal tau q * deriv (imaginaryJImag tau) q -
      deriv (imaginaryJReal tau) q * imaginaryJImag tau q) = 0 := by
    linear_combination deriv (imaginaryJImag tau) q * hvalue - imaginaryJImag tau q * hderiv
  have hb : b * (imaginaryJReal tau q * deriv (imaginaryJImag tau) q -
      deriv (imaginaryJReal tau) q * imaginaryJImag tau q) = 0 := by
    linear_combination imaginaryJReal tau q * hderiv - deriv (imaginaryJReal tau) q * hvalue
  exact ⟨(mul_eq_zero.mp ha).resolve_right hW, (mul_eq_zero.mp hb).resolve_right hW⟩

end
end ImbalancedChen.Part3.ActualGeneralJWronskian20261025a
