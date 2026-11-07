import ImbalancedChen.Part3ComplexOrderKShiftDerivative
import ImbalancedChen.Part3ComplexOrderKSmallArgument
import ImbalancedChen.Part3ComplexOrderKQODE
import ImbalancedChen.Part3GeneralISmallQWronskian
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual I/K Wronskian on 0<Re nu<1, obtained directly from genuine small-q
limits, the adjacent-order K derivative, and the two actual q equations.
No K/I connection, leading coefficient, or Wronskian is a hypothesis.
-/
namespace ImbalancedChen.Part3.GeneralIKWronskianSourceOnly
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus ComplexOrderKQODE
open ComplexOrderKShiftDerivativeSourceOnly ComplexOrderKSmallArgument20261025a
open ComplexOrderKPositiveLaplace20261025a
open GeneralComplexISeriesSourceOnly GeneralIQODE20261025a GeneralISmallQWronskian20261025a

theorem tendsto_half_scaled_K_zero {nu : ℂ} (hnu : 0 < nu.re) :
    Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ nu) * complexOrderK nu q)
      (𝓝[>] 0) (𝓝 (Complex.Gamma nu / 2)) := by
  have h := ((dampedGamma_integral_tendsto hnu).mono_left nhdsWithin_le_nhds).div_const (2 : ℂ)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [dampedGammaDensity_integral nu hq]
  ring

theorem tendsto_half_cpow_zero {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun q : ℝ => ((q / 2 : ℝ) : ℂ) ^ z) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have hn : z ≠ 0 := by intro h; simpa [h] using hz
  have hbase : Tendsto (fun q : ℝ => ((q / 2 : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have hc : Continuous (fun q : ℝ => ((q / 2 : ℝ) : ℂ)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hp := (Complex.continuousAt_cpow_const_of_re_pos
    (z := (0 : ℂ)) (Or.inl (by simp)) hz).tendsto.comp hbase
  simpa only [Complex.zero_cpow hn] using hp

/-- The reflected lower adjacent order is lower order after scaling.
Both adjacent K limits are genuine positive-real-part integral limits. -/
theorem tendsto_half_scaled_K_deriv_zero {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1) :
    Tendsto (fun q : ℝ => (q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ nu) *
      deriv (complexOrderK nu) q) (𝓝[>] 0) (𝓝 (-Complex.Gamma (nu + 1) / 2)) := by
  have hplus : 0 < (nu + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hminus : 0 < (1 - nu).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have htwice : 0 < (2 * nu).re := by simp only [Complex.mul_re, Complex.ofNat_re,
    Complex.ofNat_im, zero_mul, sub_zero]; linarith
  have htail := (tendsto_half_cpow_zero htwice).mul (tendsto_half_scaled_K_zero hminus)
  have hlim : Tendsto (fun q : ℝ =>
      -((((q / 2 : ℝ) : ℂ) ^ (nu + 1)) * complexOrderK (nu + 1) q +
        (((q / 2 : ℝ) : ℂ) ^ (2 * nu)) *
          ((((q / 2 : ℝ) : ℂ) ^ (1 - nu)) * complexOrderK (1 - nu) q)))
      (𝓝[>] 0) (𝓝 (-Complex.Gamma (nu + 1) / 2)) := by
    simpa only [zero_mul, add_zero, neg_div] using
      ((tendsto_half_scaled_K_zero hplus).add htail).neg
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hb : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (half_pos hq).ne'
  have hp : (((q / 2 : ℝ) : ℂ) ^ (nu + 1)) =
      (((q / 2 : ℝ) : ℂ) ^ nu) * ((q / 2 : ℝ) : ℂ) := by
    rw [Complex.cpow_add _ _ hb, Complex.cpow_one]
  have hc : (((q / 2 : ℝ) : ℂ) ^ (2 * nu)) *
      (((q / 2 : ℝ) : ℂ) ^ (1 - nu)) = (((q / 2 : ℝ) : ℂ) ^ (nu + 1)) := by
    rw [← Complex.cpow_add _ _ hb]
    congr 1
    ring
  rw [actual_K_derivative_eq_positive_adjacent nu hq, ← mul_assoc _ _ (complexOrderK (1 - nu) q), hc, hp]
  push_cast
  ring

def actualIKWronskian (nu : ℂ) (q : ℝ) : ℂ :=
  generalI nu q * deriv (complexOrderK nu) q - deriv (generalI nu) q * complexOrderK nu q

theorem q_mul_actualIKWronskian_eq_scaled (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * actualIKWronskian nu q =
      ((((q / 2 : ℝ) : ℂ) ^ (-nu)) * generalI nu q) *
        ((q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ nu) * deriv (complexOrderK nu) q) -
      ((q : ℂ) * (((q / 2 : ℝ) : ℂ) ^ (-nu)) * deriv (generalI nu) q) *
        ((((q / 2 : ℝ) : ℂ) ^ nu) * complexOrderK nu q) := by
  have hb : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (half_pos hq).ne'
  have hc : (((q / 2 : ℝ) : ℂ) ^ (-nu)) * (((q / 2 : ℝ) : ℂ) ^ nu) = 1 := by
    rw [← Complex.cpow_add _ _ hb, neg_add_cancel, Complex.cpow_zero]
  calc
    _ = ((((q / 2 : ℝ) : ℂ) ^ (-nu)) * (((q / 2 : ℝ) : ℂ) ^ nu)) *
        ((q : ℂ) * actualIKWronskian nu q) := by rw [hc, one_mul]
    _ = _ := by unfold actualIKWronskian; ring

theorem actualIK_leading_constant {nu : ℂ} (hnu : 0 < nu.re) :
    (Complex.Gamma (nu + 1))⁻¹ * (-Complex.Gamma (nu + 1) / 2) -
      (nu * (Complex.Gamma (nu + 1))⁻¹) * (Complex.Gamma nu / 2) = -1 := by
  have hn : nu ≠ 0 := by intro h; simpa [h] using hnu
  have hG := Complex.Gamma_ne_zero_of_re_pos hnu
  rw [Complex.Gamma_add_one nu hn]
  field_simp [hn, hG]
  <;> ring

theorem tendsto_q_actualIKWronskian_zero {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1) :
    Tendsto (fun q : ℝ => (q : ℂ) * actualIKWronskian nu q)
      (𝓝[>] 0) (𝓝 (-1 : ℂ)) := by
  have hi : -1 < nu.re := by linarith
  have h := ((tendsto_scaled_generalI_zero hi).mul
      (tendsto_half_scaled_K_deriv_zero hnu hnuUpper)).sub
    ((tendsto_scaled_generalI_deriv_zero hi).mul (tendsto_half_scaled_K_zero hnu))
  rw [actualIK_leading_constant hnu] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (q_mul_actualIKWronskian_eq_scaled nu hq).symm

/-- Abel differentiation uses the proved actual equations on both sides. -/
theorem q_actualIKWronskian_hasDerivAt_zero {nu : ℂ}
    (hnu : -1 < nu.re) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => (x : ℂ) * actualIKWronskian nu x) 0 q := by
  have hy := (generalI_differentiableAt hnu hq).hasDerivAt
  have hz := (complexOrderK_hasDerivAt_q nu hq).differentiableAt.hasDerivAt
  have hy' := (generalI_deriv_differentiableAt hnu hq).hasDerivAt
  have hz' := (deriv_complexOrderK_hasDerivAt_q nu hq).differentiableAt.hasDerivAt
  have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 q := Complex.ofRealCLM.hasDerivAt
  let D : ℂ := actualIKWronskian nu q + (q : ℂ) *
    (generalI nu q * deriv (deriv (complexOrderK nu)) q -
      deriv (deriv (generalI nu)) q * complexOrderK nu q)
  have hd : HasDerivAt (fun x : ℝ => (x : ℂ) * actualIKWronskian nu x) D q := by
    convert hid.mul ((hy.mul hz').sub (hy'.mul hz)) using 1 <;>
      dsimp only [D, actualIKWronskian] <;> ring
  have hiODE := generalI_modifiedBessel_equation hnu hq
  have hkODE := complexOrderK_modifiedBessel_equation nu hq
  have hzD : (q : ℂ) * D = 0 := by
    dsimp only [D, actualIKWronskian]
    linear_combination (generalI nu q) * hkODE - (complexOrderK nu q) * hiODE
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hD : D = 0 := (mul_eq_zero.mp hzD).resolve_left hqC
  simpa only [hD] using hd

theorem q_actualIKWronskian_eq {nu : ℂ} (hnu : -1 < nu.re)
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    (q : ℂ) * actualIKWronskian nu q = (r : ℂ) * actualIKWronskian nu r := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro x hx
    exact (q_actualIKWronskian_hasDerivAt_zero hnu hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (q_actualIKWronskian_hasDerivAt_zero hnu hx).deriv
  · exact hq
  · exact hr

/-- The actual normalized I/K Wronskian, without a connection premise. -/
theorem q_actualIKWronskian_eq_neg_one {nu : ℂ}
    (hnu : 0 < nu.re) (hnuUpper : nu.re < 1) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) * actualIKWronskian nu q = -1 := by
  have hi : -1 < nu.re := by linarith
  have he : (fun x : ℝ => (x : ℂ) * actualIKWronskian nu x) =ᶠ[𝓝[>] 0]
      (fun _ : ℝ => (q : ℂ) * actualIKWronskian nu q) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact q_actualIKWronskian_eq hi hx hq
  have hl : Tendsto (fun x : ℝ => (x : ℂ) * actualIKWronskian nu x)
      (𝓝[>] 0) (𝓝 ((q : ℂ) * actualIKWronskian nu q)) :=
    tendsto_const_nhds.congr' he.symm
  exact tendsto_nhds_unique hl (tendsto_q_actualIKWronskian_zero hnu hnuUpper)

end
end ImbalancedChen.Part3.GeneralIKWronskianSourceOnly
