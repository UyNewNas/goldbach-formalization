import ImbalancedChen.Part3CharacterMiddleCuspGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The missing p^2 oldform-dilation geometry in an actual middle-cusp matrix
sigma=[[a,b],[p,d]]. Literal S(T_(-pa)(p^2*sigma*z))=z+d/p has height Im(z),
whereas the existing p-dilation has affine height p*Im(z). All statements
are finite native H geometry; no series, limit, scalar-span or basis claim.
The k=1 channel uses the existing full SL2 automorphy theorem unchanged. -/

noncomputable section
open Matrix Matrix.SpecialLinearGroup Complex
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.CharacterEisensteinSeries
open ImbalancedChen.Part3.CharacterMiddleCuspGeometry20261026b

namespace ImbalancedChen.Part3.UntwistedMiddleSquareDilationGeometry20261026b

theorem middle_square_affine_coe (p : ℕ) (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane) : ℂ) =
      (z : ℂ) + (sigma 1 1 : ℂ) / (p : ℂ) := by
  simp [UpperHalfPlane.coe_vadd, add_comm]

/-- Both affine coordinates are literal, including the horizontal d/p
shift. In particular the vertical factor is one for EVERY unit cusp label. -/
theorem middle_square_affine_im (p : ℕ) (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane)).im = z.im :=
  UpperHalfPlane.vadd_im _ z

theorem middle_square_affine_re (p : ℕ) (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane)).re =
      z.re + (sigma 1 1 : ℝ) / (p : ℝ) := by
  rw [UpperHalfPlane.vadd_re]
  ring

private theorem square_affine_denominator_ne_zero (p : ℕ)
    (sigma : SL(2, ℤ)) (z : UpperHalfPlane) :
    (z : ℂ) + (sigma 1 1 : ℂ) / (p : ℂ) ≠ 0 := by
  rw [← middle_square_affine_coe p sigma z]
  exact ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane)).ne_zero

/-- Reuse the already derived determinant-one p-dilation identity. The
extra p multiplies the horizontal integer a and divides the affine d shift. -/
theorem scaled_square_middle_coe (p : ℕ) (hp : 0 < p) (sigma : SL(2, ℤ))
    (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    (scaledPoint (p ^ 2) (pow_pos hp 2) (sigma • z) : ℂ) =
      (p : ℂ) * (sigma 0 0 : ℂ) -
        1 / ((z : ℂ) + (sigma 1 1 : ℂ) / (p : ℂ)) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hden := middle_affine_denominator_ne_zero p hp sigma z
  have hden2 := square_affine_denominator_ne_zero p sigma z
  have hscale : (scaledPoint (p ^ 2) (pow_pos hp 2) (sigma • z) : ℂ) =
      (p : ℂ) * (scaledPoint p hp (sigma • z) : ℂ) := by
    rw [scaledPoint_coe, scaledPoint_coe]
    push_cast
    ring
  rw [hscale, scaled_middle_coe p hp sigma hc z]
  field_simp [hpC, hden, hden2]
  <;> ring

/-- Exact finite ABI for the actual k=p^2 untwisted dilation. The
SL2 chart T^(pa)*S is integral, and the affine point is the native z+d/p. -/
theorem scaled_square_middle_eq_chart_affine (p : ℕ) (hp : 0 < p)
    (sigma : SL(2, ℤ)) (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    scaledPoint (p ^ 2) (pow_pos hp 2) (sigma • z) =
      middleChartMatrix ((p : ℤ) * sigma 0 0) •
        ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane)) := by
  apply UpperHalfPlane.ext
  rw [scaled_square_middle_coe p hp sigma hc z, middleChartMatrix, mul_smul,
    UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    UpperHalfPlane.modular_S_smul, middle_square_affine_coe]
  simp only [Complex.ofReal_intCast, Int.cast_mul, Int.cast_natCast, inv_neg, one_div]
  ring

/-- Literal S(T_(-pa)(p^2*sigma*z))=z+d/p, with its exact real shift. -/
theorem square_middle_translate_invert (p : ℕ) (hp : 0 < p)
    (sigma : SL(2, ℤ)) (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    ModularGroup.S •
        ((-(((p : ℤ) * sigma 0 0 : ℤ) : ℝ)) +ᵥ
          scaledPoint (p ^ 2) (pow_pos hp 2) (sigma • z)) =
      ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane)) := by
  have ht : (-(((p : ℤ) * sigma 0 0 : ℤ) : ℝ)) +ᵥ
      scaledPoint (p ^ 2) (pow_pos hp 2) (sigma • z) =
        ModularGroup.S • ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane)) := by
    rw [scaled_square_middle_eq_chart_affine p hp sigma hc z,
      middleChartMatrix, mul_smul, UpperHalfPlane.modular_T_zpow_smul]
    simp only [vadd_vadd, neg_add_cancel, zero_vadd]
  rw [ht]
  simpa only [ModularGroup.S_inv, UpperHalfPlane.SL_neg_smul] using
    (inv_smul_smul ModularGroup.S ((((sigma 1 1 : ℝ) / (p : ℝ)) +ᵥ z : UpperHalfPlane)))

theorem scaled_square_middle_im (p : ℕ) (hp : 0 < p)
    (sigma : SL(2, ℤ)) (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) :
    (scaledPoint (p ^ 2) (pow_pos hp 2) (sigma • z)).im =
      z.im / Complex.normSq ((z : ℂ) + (sigma 1 1 : ℂ) / (p : ℂ)) := by
  rw [scaled_square_middle_eq_chart_affine p hp sigma hc z,
    middleChartMatrix, mul_smul, UpperHalfPlane.modular_T_zpow_smul,
    UpperHalfPlane.vadd_im, ModularGroup.im_smul_eq_div_normSq]
  simp [UpperHalfPlane.denom, SpecialLinearGroup.mapGL_coe_matrix, ModularGroup.S,
    middle_square_affine_coe, middle_square_affine_im]

end ImbalancedChen.Part3.UntwistedMiddleSquareDilationGeometry20261026b
