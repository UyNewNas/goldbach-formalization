import ImbalancedChen.Part3CharacterEisensteinSeries
import ImbalancedChen.Part3Gamma0GeneralCuspWidth

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal geometry of an actual integral middle-cusp matrix sigma with
lower-left p. The native p*dilation of sigma*z is T_a*S applied to
p*z+d. Thus S(T_-a(p*sigma*z))=p*z+d with exact positive height factors.
No character sum, asymptotic, incoming/nonzero or automorphy assertion. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup Complex
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.CharacterEisensteinSeries

namespace ImbalancedChen.Part3.CharacterMiddleCuspGeometry20261026b

/-- These integral middle matrices already have native width one at p^2;
no Fricke scaling or additional sqrt(width) dilation belongs in this frame. -/
theorem middle_cusp_width_one (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) :
    Gamma0GeneralCuspWidth20261025a.cuspWidth (p ^ 2) sigma = 1 := by
  simp [Gamma0GeneralCuspWidth20261025a.cuspWidth, hc, pow_ne_zero 2 hp.ne']

def middleChartMatrix (a : ℤ) : SL(2, ℤ) := ModularGroup.T ^ a * ModularGroup.S

def middleAffinePoint (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    UpperHalfPlane := (sigma 1 1 : ℝ) +ᵥ scaledPoint p hp z

theorem middleAffinePoint_coe (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    (middleAffinePoint p hp sigma z : ℂ) = (p : ℂ) * (z : ℂ) + (sigma 1 1 : ℂ) := by
  simp [middleAffinePoint, UpperHalfPlane.coe_vadd, scaledPoint_coe, add_comm]

theorem middleAffinePoint_im (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    (middleAffinePoint p hp sigma z).im = (p : ℝ) * z.im := by
  rw [middleAffinePoint, UpperHalfPlane.vadd_im, scaledPoint_im]

theorem middle_affine_denominator_ne_zero (p : ℕ) (hp : 0 < p)
    (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    (p : ℂ) * (z : ℂ) + (sigma 1 1 : ℂ) ≠ 0 := by
  rw [← middleAffinePoint_coe p hp sigma z]
  exact (middleAffinePoint p hp sigma z).ne_zero

/-- Determinant one supplies the numerator -1; it is not an assumed
linear-fractional chart identity. -/
theorem scaled_middle_coe (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    (scaledPoint p hp (sigma • z) : ℂ) =
      (sigma 0 0 : ℂ) - 1 / ((p : ℂ) * (z : ℂ) + (sigma 1 1 : ℂ)) := by
  have hden := middle_affine_denominator_ne_zero p hp sigma z
  have hdet : sigma 0 0 * sigma 1 1 - sigma 0 1 * (p : ℤ) = 1 := by
    simpa only [Matrix.det_fin_two, hc] using sigma.det_coe
  have hdetC : (sigma 0 0 : ℂ) * (sigma 1 1 : ℂ) -
      (sigma 0 1 : ℂ) * (p : ℂ) = 1 := by exact_mod_cast hdet
  have hsig : ((sigma • z : UpperHalfPlane) : ℂ) =
      ((sigma 0 0 : ℂ) * (z : ℂ) + (sigma 0 1 : ℂ)) /
        ((p : ℂ) * (z : ℂ) + (sigma 1 1 : ℂ)) := by
    simp [UpperHalfPlane.coe_specialLinearGroup_apply, hc]
  rw [scaledPoint_coe, hsig]
  field_simp [hden]
  linear_combination -hdetC

theorem scaled_middle_eq_chart_affine (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    scaledPoint p hp (sigma • z) =
      middleChartMatrix (sigma 0 0) • middleAffinePoint p hp sigma z := by
  apply UpperHalfPlane.ext
  rw [scaled_middle_coe p hp sigma hc z, middleChartMatrix, mul_smul,
    UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    UpperHalfPlane.modular_S_smul, middleAffinePoint_coe]
  simp only [Complex.ofReal_intCast, inv_neg, one_div]
  ring

/-- The requested literal S(T_-a(p*sigma*z))=p*z+d on native H. -/
theorem middle_scaled_translate_invert (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    ModularGroup.S • ((-(sigma 0 0 : ℝ)) +ᵥ scaledPoint p hp (sigma • z)) =
      middleAffinePoint p hp sigma z := by
  have ht : (-(sigma 0 0 : ℝ)) +ᵥ scaledPoint p hp (sigma • z) =
      ModularGroup.S • middleAffinePoint p hp sigma z := by
    rw [scaled_middle_eq_chart_affine p hp sigma hc z, middleChartMatrix, mul_smul,
      UpperHalfPlane.modular_T_zpow_smul]
    simp only [vadd_vadd, neg_add_cancel, zero_vadd]
  rw [ht]
  simpa only [ModularGroup.S_inv, UpperHalfPlane.SL_neg_smul] using
    (inv_smul_smul ModularGroup.S (middleAffinePoint p hp sigma z))

/-- The original scaled chart and the affine chart have EXACT reciprocal
norm-square and positive p*height factors. -/
theorem scaled_middle_im (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    (scaledPoint p hp (sigma • z)).im =
      ((p : ℝ) * z.im) / Complex.normSq ((p : ℂ) * (z : ℂ) + (sigma 1 1 : ℂ)) := by
  rw [scaled_middle_eq_chart_affine p hp sigma hc z, middleChartMatrix, mul_smul,
    UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.vadd_im,
    ModularGroup.im_smul_eq_div_normSq]
  simp [UpperHalfPlane.denom, SpecialLinearGroup.mapGL_coe_matrix, ModularGroup.S,
    middleAffinePoint_coe, middleAffinePoint_im]

end ImbalancedChen.Part3.CharacterMiddleCuspGeometry20261026b
