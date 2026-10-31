import ImbalancedChen.Certificates.PairedV2FullCertificate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FinCases

/-!
SOURCE ONLY: written without executing Lean, lake, a producer, or a replay.

The coordinate dictionary for the existing paired fourfold integral is
`t = tl*T`, `u = ul*U`, `z = a*V`, `w = a*W`.  Its determinant is
`tl*ul*a^2`; its rational kernel has degree minus five under these
three independent dilations.  The resulting coefficient is exactly `K/a`.
The original coefficient K and the original integral are never redefined.

The real integral identity is derived from the existing proved evaluation
of the literal iterated integral.  The domain equivalence, derivative,
matrix determinant, and pointwise density identity are also supplied.
The rational adapter preserves the existing certificate's three checked
logarithms and both numerical endpoints, and proves its check from the
original check.  No historical five-coordinate identification is asserted.
-/

namespace ImbalancedChen.Certificates.P2PairedFibreScaleNormalization

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval Matrix

/-- Exact normalization of the existing literal fourfold integral.
Outer endpoint ordering is unnecessary; their positivity is sufficient. -/
theorem pairedLocalIntegral_normalize (K : ℝ) {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (haZ : a ≤ Z)
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hur : 0 < ur) :
    pairedLocalIntegral K a tl tr ul ur Z =
      pairedLocalIntegral (K / a) 1 1 (tr / tl) 1 (ur / ul) (Z / a) := by
  have h1Z : (1 : ℝ) ≤ Z / a := by
    apply (le_div_iff₀ ha).mpr
    simpa only [one_mul] using haZ
  rw [pairedLocalIntegral_eq K ha haZ htl htr hul hur,
    pairedLocalIntegral_eq (K / a) zero_lt_one h1Z zero_lt_one
      (div_pos htr htl) zero_lt_one (div_pos hur hul)]
  simp only [div_one, one_div_one]
  field_simp [ha.ne', (ha.trans_le haZ).ne']
  <;> ring

/-- The same identity written using only the literal rational kernel. -/
theorem literal_integral_normalize (K : ℝ) {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (haZ : a ≤ Z)
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hur : 0 < ur) :
    (K / 80) * (∫ t in tl..tr, ∫ u in ul..ur,
      ∫ z in a..Z, ∫ w in a..z, 1 / (t * u * z ^ 2 * w)) =
    ((K / a) / 80) * (∫ T in (1 : ℝ)..(tr / tl),
      ∫ U in (1 : ℝ)..(ur / ul), ∫ V in (1 : ℝ)..(Z / a),
      ∫ W in (1 : ℝ)..V, 1 / (T * U * V ^ 2 * W)) := by
  simpa only [pairedLocalIntegral_eq_literal] using
    pairedLocalIntegral_normalize K ha haZ htl htr hul hur

/-- The literal kernel scaling also holds at zero coordinate values,
because real inversion uses its usual totalized field convention. -/
theorem pairedFibreKernel_dilate (a tl ul T U V W : ℝ) :
    pairedFibreKernel (tl * T) (ul * U) (a * V) (a * W) =
      pairedFibreKernel T U V W / (tl * ul * a ^ 3) := by
  simp only [pairedFibreKernel, div_eq_mul_inv, one_mul,
    mul_pow, mul_inv_rev, ← inv_pow]
  ring

/-- The determinant compensates exactly four of the five kernel degrees. -/
theorem weighted_kernel_dilate (K : ℝ) {a tl ul : ℝ}
    (ha : 0 < a) (htl : 0 < tl) (hul : 0 < ul) (T U V W : ℝ) :
    (K / 80) * pairedFibreKernel (tl * T) (ul * U) (a * V) (a * W) *
        (tl * ul * a ^ 2) =
      ((K / a) / 80) * pairedFibreKernel T U V W := by
  rw [pairedFibreKernel_dilate]
  field_simp [ha.ne', htl.ne', hul.ne']
  <;> ring

abbrev Point := Fin 4 → ℝ

def scaleVector (a tl ul : ℝ) : Point := ![tl, ul, a, a]

def dilatePoint (a tl ul : ℝ) (x : Point) : Point :=
  fun i => scaleVector a tl ul i * x i

private theorem scaleVector_ne_zero {a tl ul : ℝ}
    (ha : a ≠ 0) (htl : tl ≠ 0) (hul : ul ≠ 0) (i : Fin 4) :
    scaleVector a tl ul i ≠ 0 := by
  fin_cases i <;> simp [scaleVector, ha, htl, hul]

/-- A genuine real linear equivalence, hence an affine dilation fixing zero. -/
def dilation {a tl ul : ℝ} (ha : a ≠ 0) (htl : tl ≠ 0) (hul : ul ≠ 0) :
    Point ≃ₗ[ℝ] Point where
  toFun := dilatePoint a tl ul
  invFun := fun x i => x i / scaleVector a tl ul i
  left_inv x := by
    funext i
    dsimp [dilatePoint]
    exact mul_div_cancel_left₀ (x i) (scaleVector_ne_zero ha htl hul i)
  right_inv x := by
    funext i
    dsimp [dilatePoint]
    exact mul_div_cancel₀ (x i) (scaleVector_ne_zero ha htl hul i)
  map_add' x y := by
    funext i
    exact mul_add _ _ _
  map_smul' c x := by
    funext i
    change scaleVector a tl ul i * (c * x i) =
      c * (scaleVector a tl ul i * x i)
    ring

/-- The derivative of this coordinate map is the same concrete linear map. -/
theorem hasFDerivAt_dilatePoint {a tl ul : ℝ}
    (ha : a ≠ 0) (htl : tl ≠ 0) (hul : ul ≠ 0) (x : Point) :
    HasFDerivAt (dilatePoint a tl ul)
      (dilation ha htl hul).toContinuousLinearEquiv.toContinuousLinearMap x := by
  exact (dilation ha htl hul).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt

/-- The derivative matrix in the four literal coordinate directions. -/
def dilationMatrix (a tl ul : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (scaleVector a tl ul)

theorem dilationMatrix_mulVec (a tl ul : ℝ) (x : Point) :
    dilationMatrix a tl ul *ᵥ x = dilatePoint a tl ul x := by
  funext i
  exact Matrix.mulVec_diagonal (scaleVector a tl ul) x i

theorem dilationMatrix_det (a tl ul : ℝ) :
    (dilationMatrix a tl ul).det = tl * ul * a ^ 2 := by
  simp only [dilationMatrix, Matrix.det_diagonal, scaleVector,
    Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one]
  ring

theorem dilationMatrix_abs_det {a tl ul : ℝ}
    (ha : 0 < a) (htl : 0 < tl) (hul : 0 < ul) :
    |(dilationMatrix a tl ul).det| = tl * ul * a ^ 2 := by
  rw [dilationMatrix_det, abs_of_pos (by positivity : 0 < tl * ul * a ^ 2)]

theorem derivative_eq_matrix_mulVec {a tl ul : ℝ}
    (ha : a ≠ 0) (htl : tl ≠ 0) (hul : ul ≠ 0) (h : Point) :
    (dilation ha htl hul).toContinuousLinearEquiv.toContinuousLinearMap h =
      dilationMatrix a tl ul *ᵥ h := by
  exact (dilationMatrix_mulVec a tl ul h).symm

/-- Pointwise change-of-variables density using the absolute determinant
of the actual derivative matrix, rather than an independently chosen factor. -/
theorem weighted_kernel_abs_jacobian (K : ℝ) {a tl ul : ℝ}
    (ha : 0 < a) (htl : 0 < tl) (hul : 0 < ul) (x : Point) :
    (K / 80) * pairedFibreKernel
        (dilatePoint a tl ul x 0) (dilatePoint a tl ul x 1)
        (dilatePoint a tl ul x 2) (dilatePoint a tl ul x 3) *
        |(dilationMatrix a tl ul).det| =
      ((K / a) / 80) * pairedFibreKernel (x 0) (x 1) (x 2) (x 3) := by
  rw [dilationMatrix_abs_det ha htl hul]
  exact weighted_kernel_dilate K ha htl hul (x 0) (x 1) (x 2) (x 3)

/-- The actual open paired fibre, with endpoint names matching the original
definition of `pairedLocalIntegral`. -/
def fibreDomain (a tl tr ul ur Z : ℝ) : Set Point :=
  {x | tl < x 0 ∧ x 0 < tr ∧ ul < x 1 ∧ x 1 < ur ∧
    a < x 3 ∧ x 3 < x 2 ∧ x 2 < Z}

private theorem lower_mul_iff {c x : ℝ} (hc : 0 < c) :
    c < c * x ↔ 1 < x := by
  simpa only [mul_one] using (mul_lt_mul_iff_of_pos_left hc : c * 1 < c * x ↔ 1 < x)

private theorem upper_mul_iff {c x b : ℝ} (hc : 0 < c) :
    c * x < b ↔ x < b / c := by
  rw [lt_div_iff₀ hc, mul_comm x c]

theorem mem_fibreDomain_dilate_iff {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (htl : 0 < tl) (hul : 0 < ul) (x : Point) :
    dilatePoint a tl ul x ∈ fibreDomain a tl tr ul ur Z ↔
      x ∈ fibreDomain 1 1 (tr / tl) 1 (ur / ul) (Z / a) := by
  change (tl < tl * x 0 ∧ tl * x 0 < tr ∧
    ul < ul * x 1 ∧ ul * x 1 < ur ∧
    a < a * x 3 ∧ a * x 3 < a * x 2 ∧ a * x 2 < Z) ↔ _
  rw [lower_mul_iff htl, upper_mul_iff htl,
    lower_mul_iff hul, upper_mul_iff hul,
    lower_mul_iff ha, mul_lt_mul_iff_of_pos_left ha, upper_mul_iff ha]
  rfl

/-- Bijective domain transport, including empty and degenerate fibres. -/
def fibreDomainEquiv {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (htl : 0 < tl) (hul : 0 < ul) :
    {x // x ∈ fibreDomain 1 1 (tr / tl) 1 (ur / ul) (Z / a)} ≃
      {x // x ∈ fibreDomain a tl tr ul ur Z} where
  toFun x := ⟨dilation ha.ne' htl.ne' hul.ne' x,
    (mem_fibreDomain_dilate_iff ha htl hul x).2 x.property⟩
  invFun x := ⟨(dilation ha.ne' htl.ne' hul.ne').symm x,
    (mem_fibreDomain_dilate_iff ha htl hul
      ((dilation ha.ne' htl.ne' hul.ne').symm x)).1 (by
        change (dilation ha.ne' htl.ne' hul.ne')
          ((dilation ha.ne' htl.ne' hul.ne').symm x.val) ∈
            fibreDomain a tl tr ul ur Z
        simpa only [LinearEquiv.apply_symm_apply]
          using x.property)⟩
  left_inv x := by
    apply Subtype.ext
    exact (dilation ha.ne' htl.ne' hul.ne').symm_apply_apply x
  right_inv x := by
    apply Subtype.ext
    exact (dilation ha.ne' htl.ne' hul.ne').apply_symm_apply x

/-- This generic real domain is exactly the existing adopted row domain. -/
theorem adopted_openFibreSet_eq (i j : ℕ) (Z : ℚ) :
    PairedV2.openFibreSet i j Z =
      fibreDomain PairedV2.a (PairedV2.tLower i) (PairedV2.tUpper i)
        (PairedV2.uLower j) (PairedV2.uUpper j) Z := by
  rfl

/-- Normalize only coordinates and coefficient; keep every checked log and
the certified rational numerical endpoints literally unchanged. -/
def normalizeCertificate (c : PairedIntegralCertificate) : PairedIntegralCertificate :=
  { c with
    K := c.K / c.a
    a := 1
    tl := 1
    tr := c.tr / c.tl
    ul := 1
    ur := c.ur / c.ul
    Z := c.Z / c.a }

theorem normalizeCertificate_bracketLower (c : PairedIntegralCertificate)
    (ha : c.a ≠ 0) (hZ : c.Z ≠ 0) :
    (normalizeCertificate c).bracketLower = c.a * c.bracketLower := by
  dsimp [normalizeCertificate, PairedIntegralCertificate.bracketLower]
  field_simp [ha, hZ]
  <;> ring

theorem normalizeCertificate_bracketUpper (c : PairedIntegralCertificate)
    (ha : c.a ≠ 0) (hZ : c.Z ≠ 0) :
    (normalizeCertificate c).bracketUpper = c.a * c.bracketUpper := by
  dsimp [normalizeCertificate, PairedIntegralCertificate.bracketUpper]
  field_simp [ha, hZ]
  <;> ring

theorem normalizeCertificate_productLower (c : PairedIntegralCertificate)
    (ha : c.a ≠ 0) (hZ : c.Z ≠ 0) :
    (normalizeCertificate c).productLower = c.productLower := by
  rw [PairedIntegralCertificate.productLower,
    normalizeCertificate_bracketLower c ha hZ]
  dsimp [normalizeCertificate, PairedIntegralCertificate.productLower]
  field_simp [ha]
  <;> ring

theorem normalizeCertificate_productUpper (c : PairedIntegralCertificate)
    (ha : c.a ≠ 0) (hZ : c.Z ≠ 0) :
    (normalizeCertificate c).productUpper = c.productUpper := by
  rw [PairedIntegralCertificate.productUpper,
    normalizeCertificate_bracketUpper c ha hZ]
  dsimp [normalizeCertificate, PairedIntegralCertificate.productUpper]
  field_simp [ha]
  <;> ring

/-- Original checker validity implies normalized checker validity; no
enclosure inequality is added as a new premise. -/
theorem normalizeCertificate_valid (c : PairedIntegralCertificate) (hv : c.Valid) :
    (normalizeCertificate c).Valid := by
  rcases hv with ⟨hK, ha, haZ, htl, ht, hul, hu, hargT, hargU, hargZ,
    hcheckT, hcheckU, hcheckZ, hlogT, hlogU, hbracket, hlo, hhi⟩
  have hZ : c.Z ≠ 0 := (ha.trans_le haZ).ne'
  have h1Z : (1 : ℚ) ≤ c.Z / c.a := by
    exact (le_div_iff₀ ha).mpr (by simpa only [one_mul] using haZ)
  have h1T : (1 : ℚ) ≤ c.tr / c.tl := by
    exact (le_div_iff₀ htl).mpr (by simpa only [one_mul] using ht)
  have h1U : (1 : ℚ) ≤ c.ur / c.ul := by
    exact (le_div_iff₀ hul).mpr (by simpa only [one_mul] using hu)
  refine ⟨div_pos hK ha, zero_lt_one, h1Z, zero_lt_one, h1T,
    zero_lt_one, h1U, ?_, ?_, ?_, hcheckT, hcheckU, hcheckZ,
    hlogT, hlogU, ?_, ?_, ?_⟩
  · simpa only [normalizeCertificate, div_one] using hargT
  · simpa only [normalizeCertificate, div_one] using hargU
  · simpa only [normalizeCertificate, div_one] using hargZ
  · rw [normalizeCertificate_bracketLower c ha.ne' hZ]
    exact mul_nonneg ha.le hbracket
  · rw [normalizeCertificate_productLower c ha.ne' hZ]
    exact hlo
  · rw [normalizeCertificate_productUpper c ha.ne' hZ]
    exact hhi

theorem normalizeCertificate_checked (c : PairedIntegralCertificate)
    (hc : c.check = true) : (normalizeCertificate c).check = true := by
  have hv : c.Valid := of_decide_eq_true hc
  exact decide_eq_true (normalizeCertificate_valid c hv)

/-- A checked rational row and its normalized row represent the identical
real integral, with the coefficient cast from the exact rational K/a. -/
theorem normalized_integral_eq (c : PairedIntegralCertificate) (hv : c.Valid) :
    pairedLocalIntegral (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z =
      pairedLocalIntegral ((c.K / c.a : ℚ) : ℝ)
        1 1 ((c.tr / c.tl : ℚ) : ℝ) 1
        ((c.ur / c.ul : ℚ) : ℝ) ((c.Z / c.a : ℚ) : ℝ) := by
  rcases hv with ⟨_, ha, haZ, htl, ht, hul, hu, _⟩
  have haR : (0 : ℝ) < (c.a : ℝ) := by exact_mod_cast ha
  have haZR : (c.a : ℝ) ≤ (c.Z : ℝ) := by exact_mod_cast haZ
  have htlR : (0 : ℝ) < (c.tl : ℝ) := by exact_mod_cast htl
  have htrR : (0 : ℝ) < (c.tr : ℝ) := by exact_mod_cast htl.trans_le ht
  have hulR : (0 : ℝ) < (c.ul : ℝ) := by exact_mod_cast hul
  have hurR : (0 : ℝ) < (c.ur : ℝ) := by exact_mod_cast hul.trans_le hu
  simpa only [Rat.cast_div] using
    pairedLocalIntegral_normalize (c.K : ℝ) haR haZR htlR htrR hulR hurR

theorem normalized_certificate_bounds (c : PairedIntegralCertificate)
    (hc : c.check = true) :
    (c.lower : ℝ) ≤ pairedLocalIntegral ((c.K / c.a : ℚ) : ℝ)
        1 1 ((c.tr / c.tl : ℚ) : ℝ) 1
        ((c.ur / c.ul : ℚ) : ℝ) ((c.Z / c.a : ℚ) : ℝ) ∧
      pairedLocalIntegral ((c.K / c.a : ℚ) : ℝ)
        1 1 ((c.tr / c.tl : ℚ) : ℝ) 1
        ((c.ur / c.ul : ℚ) : ℝ) ((c.Z / c.a : ℚ) : ℝ) ≤ (c.upper : ℝ) := by
  simpa only [normalizeCertificate, Rat.cast_one] using
    (normalizeCertificate c).check_sound (normalizeCertificate_checked c hc)

/-- Every adopted rational row has a normalized checked certificate,
using its actual logarithms, data selector, and original checker supplier. -/
theorem adopted_row_normalized_checked (r : PairedV2.FullMask.Row) :
    (normalizeCertificate (PairedV2.FullMask.makeCertificate r
      (PairedV2.FullMask.approximation r))).check = true := by
  exact normalizeCertificate_checked _ (PairedV2.FullMask.all_certificates_checked r)

/-- Concrete full-mask row adapter, preserving both rational endpoints. -/
theorem adopted_row_normalized_bounds (r : PairedV2.FullMask.Row) :
    let c := PairedV2.FullMask.makeCertificate r (PairedV2.FullMask.approximation r)
    (c.lower : ℝ) ≤ pairedLocalIntegral ((PairedV2.K / PairedV2.a : ℚ) : ℝ)
      1 1 ((c.tr / c.tl : ℚ) : ℝ) 1
      ((c.ur / c.ul : ℚ) : ℝ) ((c.Z / PairedV2.a : ℚ) : ℝ) ∧
    pairedLocalIntegral ((PairedV2.K / PairedV2.a : ℚ) : ℝ)
      1 1 ((c.tr / c.tl : ℚ) : ℝ) 1
      ((c.ur / c.ul : ℚ) : ℝ) ((c.Z / PairedV2.a : ℚ) : ℝ) ≤ (c.upper : ℝ) := by
  exact normalized_certificate_bounds _ (PairedV2.FullMask.all_certificates_checked r)

/-- A normalized actual row integral, using only the original row geometry. -/
def normalizedRowIntegral (r : PairedV2.FullMask.Row) : ℝ :=
  pairedLocalIntegral ((PairedV2.K / PairedV2.a : ℚ) : ℝ)
    1 1 ((PairedV2.tUpper (PairedV2.FullMask.indices r).1 /
      PairedV2.tLower (PairedV2.FullMask.indices r).1 : ℚ) : ℝ)
    1 ((PairedV2.uUpper (PairedV2.FullMask.indices r).2 /
      PairedV2.uLower (PairedV2.FullMask.indices r).2 : ℚ) : ℝ)
    ((PairedV2.FullMask.cutoff r / PairedV2.a : ℚ) : ℝ)

theorem normalizedRowIntegral_eq (r : PairedV2.FullMask.Row) :
    normalizedRowIntegral r = pairedLocalIntegral (PairedV2.K : ℝ) PairedV2.a
      (PairedV2.tLower (PairedV2.FullMask.indices r).1)
      (PairedV2.tUpper (PairedV2.FullMask.indices r).1)
      (PairedV2.uLower (PairedV2.FullMask.indices r).2)
      (PairedV2.uUpper (PairedV2.FullMask.indices r).2)
      (PairedV2.FullMask.cutoff r) := by
  exact (normalized_integral_eq
    (PairedV2.FullMask.makeCertificate r (PairedV2.FullMask.approximation r))
    (of_decide_eq_true (PairedV2.FullMask.all_certificates_checked r))).symm

/-- No row or numerical contribution is lost by the coordinate dictionary. -/
theorem normalized_full_sum_eq :
    (∑ r : PairedV2.FullMask.Row, normalizedRowIntegral r) =
      PairedV2.FullMask.integral := by
  simp only [normalizedRowIntegral_eq, PairedV2.FullMask.integral]

/-- The original actual all-row numerical enclosure is inherited verbatim. -/
theorem normalized_full_bounds :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤
        ∑ r : PairedV2.FullMask.Row, normalizedRowIntegral r ∧
      (∑ r : PairedV2.FullMask.Row, normalizedRowIntegral r) ≤
        (55858409959907296 / 100000000000000000000 : ℝ) := by
  rw [normalized_full_sum_eq]
  exact PairedV2.FullMask.integral_bounds

end

end ImbalancedChen.Certificates.P2PairedFibreScaleNormalization
