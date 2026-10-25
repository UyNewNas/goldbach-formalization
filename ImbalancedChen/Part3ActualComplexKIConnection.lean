import ImbalancedChen.Part3ActualComplexKIBasis
import ImbalancedChen.Part3GeneralISmallQRemainder
import ImbalancedChen.Part3ComplexOrderKSmallArgument
import ImbalancedChen.Part3ComplexOrderKSecondSmallArgument
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The actual complex K/I connection on the open order strip

The coefficients of the actual global I-pair basis are identified by two
independently proved endpoint limits. The first K limit identifies the I_-nu
coefficient. The second K limit, together with the genuine I_-nu remainder,
identifies the I_nu coefficient. No connection, asymptotic, or ODE premise is
assumed. All powers are principal complex powers with positive real bases.

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped Topology
open Set Filter

namespace ImbalancedChen.Part3.ActualComplexKIConnection

open ActualComplexKIBasis ComplexOrderKBridgeSourceOnly
open GeneralComplexISeriesSourceOnly GeneralISmallQRemainderSourceOnly
open ComplexOrderKSmallArgument20261025a ComplexOrderKSecondSmallArgument20261025a

private theorem two_cpow_ne_zero (ν : ℂ) : (2 : ℂ) ^ ν ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))

private theorem two_cpow_sub_one (ν : ℂ) :
    (2 : ℂ) ^ (ν - 1) = (2 : ℂ) ^ ν / 2 := by
  rw [Complex.cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]

/-- The dominant coefficient is fixed by the first actual K limit. -/
theorem actualKICoefficientMinus_eq_gamma {ν : ℂ}
    (hL : 0 < ν.re) (hU : ν.re < 1) :
    actualKICoefficientMinus ν = Complex.Gamma ν * Complex.Gamma (1 - ν) / 2 := by
  have hn : -1 < (-ν).re := by simp only [Complex.neg_re]; linarith
  have hG : Complex.Gamma (1 - ν) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hU)
  have hT := two_cpow_ne_zero ν
  have hm : Tendsto (fun q : ℝ => (q : ℂ) ^ ν * generalI (-ν) q)
      (𝓝[>] 0) (𝓝 ((2 : ℂ) ^ ν / Complex.Gamma (1 - ν))) := by
    simpa only [neg_neg, Complex.cpow_neg, inv_inv,
      show -ν + 1 = 1 - ν by ring, div_eq_mul_inv] using
      (tendsto_q_neg_order_mul_generalI hn)
  have hs := ((tendsto_q_order_mul_generalI_zero hL).const_mul
    (actualKICoefficientPlus ν)).add (hm.const_mul (actualKICoefficientMinus ν))
  have hb : Tendsto (fun q : ℝ => (q : ℂ) ^ ν * complexOrderK ν q)
      (𝓝[>] 0)
      (𝓝 (actualKICoefficientMinus ν * ((2 : ℂ) ^ ν / Complex.Gamma (1 - ν)))) := by
    have hs' := hs
    simp only [mul_zero, zero_add] at hs'
    apply hs'.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [actualK_eq_generalI_basis hL hU hq]
    ring
  have he := tendsto_nhds_unique (complexOrderK_small_argument hL) hb
  rw [two_cpow_sub_one] at he
  calc
    actualKICoefficientMinus ν =
        (((2 : ℂ) ^ ν / 2) * Complex.Gamma ν) /
          ((2 : ℂ) ^ ν / Complex.Gamma (1 - ν)) :=
      (eq_div_iff (div_ne_zero hT hG)).mpr he.symm
    _ = Complex.Gamma ν * Complex.Gamma (1 - ν) / 2 := by
      field_simp [hT, hG]
      <;> ring

private theorem half_base_negative_cpow (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (((q / 2 : ℝ) : ℂ) ^ (-ν)) = (2 : ℂ) ^ ν * (q : ℂ) ^ (-ν) := by
  simpa only [Complex.cpow_zero, one_mul, zero_add, Complex.cpow_neg, inv_inv] using
    (positive_half_base_cpow_product 0 (-ν) hq)

/-- The dominant basis term agrees exactly with the subtracted K term. -/
theorem actualK_dominant_term_eq {ν : ℂ}
    (hL : 0 < ν.re) (hU : ν.re < 1) {q : ℝ} (hq : 0 < q) :
    actualKICoefficientMinus ν *
        ((((q / 2 : ℝ) : ℂ) ^ (-ν)) / Complex.Gamma (1 - ν)) =
      (2 : ℂ) ^ (ν - 1) * Complex.Gamma ν * (q : ℂ) ^ (-ν) := by
  have hG : Complex.Gamma (1 - ν) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using sub_pos.mpr hU)
  rw [actualKICoefficientMinus_eq_gamma hL hU, half_base_negative_cpow ν hq,
    two_cpow_sub_one]
  field_simp [hG]
  <;> ring

/-- The second actual K coefficient and the true negative-order I remainder
fix the previously undetermined recessive coefficient. -/
theorem actualKICoefficientPlus_eq_gamma {ν : ℂ}
    (hL : 0 < ν.re) (hU : ν.re < 1) :
    actualKICoefficientPlus ν = Complex.Gamma (-ν) * Complex.Gamma (ν + 1) / 2 := by
  have hG : Complex.Gamma (ν + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have hT := two_cpow_ne_zero ν
  have hp := tendsto_q_neg_order_mul_generalI (by linarith : -1 < ν.re)
  have hm := tendsto_generalI_neg_order_remainder hU
  have hs := (hp.const_mul (actualKICoefficientPlus ν)).add
    (hm.const_mul (actualKICoefficientMinus ν))
  have hb : Tendsto (fun q : ℝ => (q : ℂ) ^ (-ν) * (complexOrderK ν q -
      (2 : ℂ) ^ (ν - 1) * Complex.Gamma ν * (q : ℂ) ^ (-ν)))
      (𝓝[>] 0)
      (𝓝 (actualKICoefficientPlus ν *
        (((2 : ℂ) ^ ν)⁻¹ * (Complex.Gamma (ν + 1))⁻¹))) := by
    have hs' := hs
    simp only [mul_zero, add_zero] at hs'
    apply hs'.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [actualK_eq_generalI_basis hL hU hq, ← actualK_dominant_term_eq hL hU hq]
    ring
  have he := tendsto_nhds_unique (complexOrderK_second_small_argument hL hU) hb
  rw [two_cpow_sub_one, Complex.cpow_neg] at he
  calc
    actualKICoefficientPlus ν =
        ((((2 : ℂ) ^ ν)⁻¹ / 2) * Complex.Gamma (-ν)) /
          (((2 : ℂ) ^ ν)⁻¹ * (Complex.Gamma (ν + 1))⁻¹) :=
      (eq_div_iff (mul_ne_zero (inv_ne_zero hT) (inv_ne_zero hG))).mpr he.symm
    _ = Complex.Gamma (-ν) * Complex.Gamma (ν + 1) / 2 := by
      field_simp [hT, hG]
      <;> ring

theorem actualKICoefficientMinus_eq_sine {ν : ℂ}
    (hL : 0 < ν.re) (hU : ν.re < 1) :
    actualKICoefficientMinus ν =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * ν)) := by
  rw [actualKICoefficientMinus_eq_gamma hL hU, Complex.Gamma_mul_Gamma_one_sub]
  ring

theorem actualKICoefficientPlus_eq_sine {ν : ℂ}
    (hL : 0 < ν.re) (hU : ν.re < 1) :
    actualKICoefficientPlus ν =
      -((Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * ν))) := by
  rw [actualKICoefficientPlus_eq_gamma hL hU,
    show ν + 1 = 1 - (-ν) by ring, Complex.Gamma_mul_Gamma_one_sub]
  simp only [mul_neg, Complex.sin_neg, div_neg]
  ring

/-- The actual general complex-order K/I connection, with no assumed
connection, asymptotic coefficient, or differential equation. -/
theorem complexOrderK_eq_generalI_sub {ν : ℂ}
    (hL : 0 < ν.re) (hU : ν.re < 1) {q : ℝ} (hq : 0 < q) :
    complexOrderK ν q =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * ν)) *
        (generalI (-ν) q - generalI ν q) := by
  rw [actualK_eq_generalI_basis hL hU hq,
    actualKICoefficientPlus_eq_sine hL hU, actualKICoefficientMinus_eq_sine hL hU]
  ring

end ImbalancedChen.Part3.ActualComplexKIConnection
