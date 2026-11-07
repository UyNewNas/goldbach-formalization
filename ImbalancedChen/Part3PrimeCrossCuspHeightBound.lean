import ImbalancedChen.Part3PrimeActualCuspOrbits
import ImbalancedChen.Part3FrickeNormalizer
import ImbalancedChen.Part3InfinityZeroArithmetic
import ImbalancedChen.Part3IntegralCuspFordGeometry

/-! Actual normalized cross-cusp height product. The real SL2 Mobius
denominator supplies c^2*Im(gz)*Im(z)<=1. For Gamma0(p)*W_p the literal
lower-left entry is sqrt(p)*d; primitive determinant arithmetic forces
d nonzero, hence its square is at least one. No cusp-disjointness premise.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimeActualCuspOrbits20261026b
open ImbalancedChen.Part3.Gamma0GeneralCuspUnitPeriod20261025a

namespace ImbalancedChen.Part3.PrimeCrossCuspHeightBound20261026b

/-- Exact real lower-left height inequality, before an arithmetic lower
bound on the modulus is supplied. -/
theorem realSL_csq_height_product_le (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    (g • z).im * z.im * (g 1 0) ^ 2 ≤ 1 := by
  let G := SpecialLinearGroup.mapGL ℝ g
  have hden : (g 1 0 * z.im) ^ 2 ≤ Complex.normSq (UpperHalfPlane.denom G z) := by
    simpa [G, mapGL_coe_matrix] using UpperHalfPlane.c_mul_im_sq_le_normSq_denom G z
  have hdenpos : 0 < Complex.normSq (UpperHalfPlane.denom G z) :=
    UpperHalfPlane.normSq_denom_pos G z.im_ne_zero
  have him : (g • z).im = z.im / Complex.normSq (UpperHalfPlane.denom G z) := by
    change (G • z).im = _
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp only [G, SpecialLinearGroup.det_mapGL, Units.val_one, abs_one, one_mul]
  have heq : (g • z).im * Complex.normSq (UpperHalfPlane.denom G z) = z.im :=
    (eq_div_iff hdenpos.ne').mp him
  have hsq : (g • z).im * (g 1 0 * z.im) ^ 2 ≤ z.im :=
    (mul_le_mul_of_nonneg_left hden (g • z).im_pos.le).trans_eq heq
  apply (mul_le_mul_right z.im_pos).mp
  nlinarith [hsq]

theorem realSL_height_product_le_one (g : SL(2, ℝ))
    (hc : 1 ≤ (g 1 0) ^ 2) (z : UpperHalfPlane) :
    (g • z).im * z.im ≤ 1 := by
  have h := realSL_csq_height_product_le g z
  have hpos : 0 ≤ (g • z).im * z.im := mul_nonneg (g • z).im_pos.le z.im_pos.le
  have hm := mul_le_mul_of_nonneg_left hc hpos
  nlinarith [hm]

theorem realSL_integral_action (g : SL(2, ℤ)) (z : UpperHalfPlane) : realSL g • z = g • z := by
  simpa only [realSL, integralReal] using integralReal_smul g z

/-- The original normalized infinity-to-zero modulus, without changing
either scaling matrix or the integer denominator. -/
theorem gamma0_fricke_lowerLeft {p : ℕ} (hp : p.Prime)
    (g : CongruenceSubgroup.Gamma0 p) :
    (realSL (g : SL(2, ℤ)) * frickeSL p hp.pos) 1 0 =
      Real.sqrt (p : ℝ) * ((g : SL(2, ℤ)) 1 1 : ℝ) := by
  simp [realSL, frickeSL, frickeMatrix, coe_mul, Matrix.mul_fin_two,
    Matrix.SpecialLinearGroup.map_apply_coe] <;> ring

theorem gamma0_fricke_modulus_sq_one_le {p : ℕ} (hp : p.Prime)
    (g : CongruenceSubgroup.Gamma0 p) :
    1 ≤ ((realSL (g : SL(2, ℤ)) * frickeSL p hp.pos) 1 0) ^ 2 := by
  have hd : (g : SL(2, ℤ)) 1 1 ≠ 0 := by
    intro hd
    apply gamma0_zero_ne_infinity hp (g : SL(2, ℤ)) g.property
    simp [OnePoint.smul_some_eq_ite, mapGL_coe_matrix, hd]
  have hdi : (0 : ℤ) < ((g : SL(2, ℤ)) 1 1) ^ 2 := sq_pos_of_ne_zero hd
  have hdi1 : (1 : ℤ) ≤ ((g : SL(2, ℤ)) 1 1) ^ 2 := by omega
  have hdr : (1 : ℝ) ≤ (((g : SL(2, ℤ)) 1 1 : ℝ)) ^ 2 := by exact_mod_cast hdi1
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  rw [gamma0_fricke_lowerLeft hp g, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ))]
  have hm := mul_le_mul_of_nonneg_right hpr (sq_nonneg (((g : SL(2, ℤ)) 1 1 : ℝ)))
  nlinarith [hm]

/-- True cross-channel height product for every actual Gamma0 deck map. -/
theorem gamma0_fricke_height_product {p : ℕ} (hp : p.Prime)
    (g : CongruenceSubgroup.Gamma0 p) (z : UpperHalfPlane) :
    (g • (frickeSL p hp.pos • z)).im * z.im ≤ 1 := by
  have h := realSL_height_product_le_one
    (realSL (g : SL(2, ℤ)) * frickeSL p hp.pos) (gamma0_fricke_modulus_sq_one_le hp g) z
  simpa only [mul_smul, realSL_integral_action] using h

end ImbalancedChen.Part3.PrimeCrossCuspHeightBound20261026b
