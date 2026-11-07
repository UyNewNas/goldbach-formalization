import ImbalancedChen.Part3ActualHeckeAllFrameCommonPeriod
import ImbalancedChen.Part3IntegerDetPrimeNormalForm

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Actual normalized-real Hecke/rational-frame affine dictionary. An INTEGER
upper-triangular normal form is transported through the ORIGINAL explicit
sqrt(width) scaling matrices; both sqrt(p) and both cusp widths remain
visible. The resulting physical height and horizontal affine parameters
are a=k^2*w_g/(p*w_h)>0 and b=k*beta/(p*w_h), with no presumed affine/frame
factorization. Generic integer normal-form existence is independently
proved by IntegerDetPrimeNormalForm and consumed for actual branch witnesses.
No constant-term preservation or cusp-space invariance is assumed here.
-/

namespace ImbalancedChen.Part3.ActualHeckeNormalizedFrameAffine20261026b
noncomputable section
open Set Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open ActualHeckeAllFrameCommonPeriod20261026b IntegerDetPrimeNormalForm20261026b

/-- Literal positive real affine map on H, with both physical coordinates. -/
def positiveAffineAction (a b : ℝ) (ha : 0 < a) (z : ℍ) : ℍ :=
  ⟨(a : ℂ)*(z : ℂ)+(b : ℂ),by simpa using mul_pos ha z.im_pos⟩

def positiveAffineSL (alpha eta : ℝ) (halpha : 0 < alpha) : SL(2, ℝ) :=
  ⟨!![alpha,eta;0,alpha⁻¹],by simp [Matrix.det_fin_two_of,halpha.ne']⟩

theorem positiveAffineSL_coe_action (alpha eta : ℝ) (halpha : 0 < alpha) (z : ℍ) :
    ((positiveAffineSL alpha eta halpha • z : ℍ) : ℂ) =
      ((alpha^2 : ℝ) : ℂ)*(z : ℂ)+((alpha*eta : ℝ) : ℂ) := by
  have haC : (alpha : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr halpha.ne'
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [positiveAffineSL,Matrix.SpecialLinearGroup.coeFn_eq_coe,Complex.ofReal_inv,
    Complex.ofReal_pow,Complex.ofReal_mul] <;> field_simp [haC] <;> ring

variable (N p : ℕ) (hN : 0 < N) (hp : 0 < p)

def frameAffineRatio (k : ℕ) (g h : SL(2, ℤ)) : ℝ :=
  (k : ℝ)*Real.sqrt (cuspWidth N g : ℝ)/
    (Real.sqrt (p : ℝ)*Real.sqrt (cuspWidth N h : ℝ))

def frameAffineUpper (beta : ℤ) (g h : SL(2, ℤ)) : ℝ :=
  (beta : ℝ)/(Real.sqrt (p : ℝ)*Real.sqrt (cuspWidth N g : ℝ)*Real.sqrt (cuspWidth N h : ℝ))

def frameAffineHeight (k : ℕ) (g h : SL(2, ℤ)) : ℝ :=
  (k : ℝ)^2*(cuspWidth N g : ℝ)/((p : ℝ)*(cuspWidth N h : ℝ))

def frameAffineShift (k : ℕ) (beta : ℤ) (h : SL(2, ℤ)) : ℝ :=
  (k : ℝ)*(beta : ℝ)/((p : ℝ)*(cuspWidth N h : ℝ))

theorem frameAffineRatio_pos {k : ℕ} (hk : 0 < k) (g h : SL(2, ℤ)) :
    0 < frameAffineRatio N p k g h := by
  unfold frameAffineRatio
  exact div_pos (mul_pos (by exact_mod_cast hk)
    (Real.sqrt_pos.mpr (by exact_mod_cast cuspWidth_pos N hN g)))
    (mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hp))
      (Real.sqrt_pos.mpr (by exact_mod_cast cuspWidth_pos N hN h)))

theorem frameAffineHeight_pos {k : ℕ} (hk : 0 < k) (g h : SL(2, ℤ)) :
    0 < frameAffineHeight N p k g h := by
  unfold frameAffineHeight
  exact div_pos (mul_pos (sq_pos_of_pos (by exact_mod_cast hk))
    (by exact_mod_cast cuspWidth_pos N hN g))
    (mul_pos (by exact_mod_cast hp) (by exact_mod_cast cuspWidth_pos N hN h))

theorem frameAffineRatio_square (k : ℕ) (g h : SL(2, ℤ)) :
    (frameAffineRatio N p k g h)^2 = frameAffineHeight N p k g h := by
  unfold frameAffineRatio frameAffineHeight
  rw [div_pow,mul_pow,mul_pow,
    Real.sq_sqrt (by exact_mod_cast (cuspWidth_pos N hN g).le),
    Real.sq_sqrt (by exact_mod_cast hp.le),
    Real.sq_sqrt (by exact_mod_cast (cuspWidth_pos N hN h).le)]

theorem frameAffineRatio_mul_upper (k : ℕ) (beta : ℤ) (g h : SL(2, ℤ)) :
    frameAffineRatio N p k g h*frameAffineUpper N p beta g h = frameAffineShift N p k beta h := by
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hp)).ne'
  have hx : Real.sqrt (cuspWidth N g : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast cuspWidth_pos N hN g)).ne'
  have hy : Real.sqrt (cuspWidth N h : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast cuspWidth_pos N hN h)).ne'
  calc
    _ = (k : ℝ)*(beta : ℝ)/((Real.sqrt (p : ℝ))^2*(Real.sqrt (cuspWidth N h : ℝ))^2) := by
      unfold frameAffineRatio frameAffineUpper
      field_simp [hs,hx,hy] <;> ring
    _ = _ := by
      rw [Real.sq_sqrt (by exact_mod_cast hp.le),
        Real.sq_sqrt (by exact_mod_cast (cuspWidth_pos N hN h).le)]
      rfl

/-- Exact normalized REAL factorization paid by a literal integer
normal form. The normal-form premise names only integer matrix data. -/
theorem normalized_frame_factor_of_integer_normalForm (j : Branch p) (g h : SL(2, ℤ))
    (k : ℕ) (hk : 0 < k) (beta : ℤ) (hdiv : (k : ℤ)*((p : ℤ)/(k : ℤ))=(p : ℤ))
    (hM : branchMatrix p j*(g : Matrix (Fin 2) (Fin 2) ℤ) =
      (h : Matrix (Fin 2) (Fin 2) ℤ)*!![(k : ℤ),beta;0,(p : ℤ)/(k : ℤ)]) :
    branchSL p hp j*normalizedScaling N hN g = normalizedScaling N hN h*
      positiveAffineSL (frameAffineRatio N p k g h) (frameAffineUpper N p beta g h)
        (frameAffineRatio_pos N p hN hp hk g h) := by
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hp)).ne'
  have hx : Real.sqrt (cuspWidth N g : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast cuspWidth_pos N hN g)).ne'
  have hy : Real.sqrt (cuspWidth N h : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast cuspWidth_pos N hN h)).ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdR : (((p : ℤ)/(k : ℤ) : ℤ) : ℝ)=(p : ℝ)/(k : ℝ) := by
    apply (eq_div_iff hkR).mpr
    have ht : (k : ℝ)*(((p : ℤ)/(k : ℤ) : ℤ) : ℝ)=(p : ℝ) := by exact_mod_cast hdiv
    nlinarith
  have hdS : (((p : ℤ)/(k : ℤ) : ℤ) : ℝ)=(Real.sqrt (p : ℝ))^2/(k : ℝ) := by
    rw [Real.sq_sqrt (by exact_mod_cast hp.le)]
    exact hdR
  have hinner : ((Real.sqrt (p : ℝ))⁻¹ • (!![(k : ℤ),beta;0,(p : ℤ)/(k : ℤ)]).map (Int.castRingHom ℝ)) *
      (widthDiagonal (cuspWidth N g) (cuspWidth_pos N hN g) : Matrix (Fin 2) (Fin 2) ℝ) =
    (widthDiagonal (cuspWidth N h) (cuspWidth_pos N hN h) : Matrix (Fin 2) (Fin 2) ℝ)*
      (positiveAffineSL (frameAffineRatio N p k g h) (frameAffineUpper N p beta g h)
        (frameAffineRatio_pos N p hN hp hk g h) : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l
    · simp [widthDiagonal,positiveAffineSL,Matrix.mul_fin_two,frameAffineRatio,frameAffineUpper,smul_eq_mul] <;>
        field_simp [hs,hx,hy,hkR] <;> ring
    · simp [widthDiagonal,positiveAffineSL,Matrix.mul_fin_two,frameAffineRatio,frameAffineUpper,smul_eq_mul] <;>
        field_simp [hs,hx,hy,hkR] <;> ring
    · simp [widthDiagonal,positiveAffineSL,Matrix.mul_fin_two,smul_eq_mul]
    · simp [widthDiagonal,positiveAffineSL,Matrix.mul_fin_two,smul_eq_mul]
      change (Real.sqrt (p : ℝ))⁻¹*(((p : ℤ)/(k : ℤ) : ℤ) : ℝ)*(Real.sqrt (cuspWidth N g : ℝ))⁻¹ =
        (Real.sqrt (cuspWidth N h : ℝ))⁻¹*(frameAffineRatio N p k g h)⁻¹
      rw [hdS]
      unfold frameAffineRatio
      field_simp [hs,hx,hy,hkR] <;> ring
  apply Subtype.ext
  change ((Real.sqrt (p : ℝ))⁻¹ • (branchMatrix p j).map (Int.castRingHom ℝ))*
      (((g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ))*
        (widthDiagonal (cuspWidth N g) (cuspWidth_pos N hN g) : Matrix (Fin 2) (Fin 2) ℝ)) = _
  rw [← Matrix.mul_assoc,Matrix.smul_mul,← Matrix.map_mul,hM,Matrix.map_mul,
    ← Matrix.mul_smul,Matrix.mul_assoc,hinner,← Matrix.mul_assoc]

/-- Actual physical coordinate action, including the exact original
width ratio in height and exact horizontal rational shift. -/
theorem normalized_frame_action_of_integer_normalForm (j : Branch p) (g h : SL(2, ℤ))
    (k : ℕ) (hk : 0 < k) (beta : ℤ) (hdiv : (k : ℤ)*((p : ℤ)/(k : ℤ))=(p : ℤ))
    (hM : branchMatrix p j*(g : Matrix (Fin 2) (Fin 2) ℤ) =
      (h : Matrix (Fin 2) (Fin 2) ℤ)*!![(k : ℤ),beta;0,(p : ℤ)/(k : ℤ)]) (z : ℍ) :
    branchSL p hp j • (normalizedScaling N hN g • z) =
      normalizedScaling N hN h • positiveAffineAction (frameAffineHeight N p k g h)
        (frameAffineShift N p k beta h) (frameAffineHeight_pos N p hN hp hk g h) z := by
  have hm := normalized_frame_factor_of_integer_normalForm N p hN hp j g h k hk beta hdiv hM
  have hcoord : positiveAffineSL (frameAffineRatio N p k g h) (frameAffineUpper N p beta g h)
      (frameAffineRatio_pos N p hN hp hk g h) • z =
        positiveAffineAction (frameAffineHeight N p k g h) (frameAffineShift N p k beta h)
          (frameAffineHeight_pos N p hN hp hk g h) z := by
    apply UpperHalfPlane.ext
    rw [positiveAffineSL_coe_action,frameAffineRatio_square N p hN hp,frameAffineRatio_mul_upper N p hN hp]
    rfl
  calc
    _ = (branchSL p hp j*normalizedScaling N hN g) • z := (mul_smul _ _ _).symm
    _ = _ := by rw [hm,mul_smul,hcoord]

/-- Actual branch arithmetic data, derived from the independently proved
integer determinant-prime normal form. No affine conclusion is a field. -/
structure RationalBranchData (j : Branch p) (g : SL(2, ℤ)) where
  outputFrame : SL(2, ℤ)
  columnGcd : ℕ
  beta : ℤ
  positive : 0 < columnGcd
  primeCases : columnGcd=1 ∨ columnGcd=p
  integerFactor : branchMatrix p j*(g : Matrix (Fin 2) (Fin 2) ℤ) =
    (outputFrame : Matrix (Fin 2) (Fin 2) ℤ)*
      !![(columnGcd : ℤ),beta;0,(p : ℤ)/(columnGcd : ℤ)]

def actualRationalBranchData (hprime : p.Prime) (j : Branch p) (g : SL(2, ℤ)) :
    RationalBranchData p j g := by
  have hdet : Matrix.det (branchMatrix p j*(g : Matrix (Fin 2) (Fin 2) ℤ))=(p : ℤ) := by
    rw [Matrix.det_mul,branchMatrix_det,g.det_coe,mul_one]
  obtain ⟨h,k,beta,hkgcd,hkpos,hkdvd,hkcases,h00,h10,hbeta,hinverse,hfactor⟩ :=
    exists_prime_normal_form_with_gcd p hprime _ hdet
  exact ⟨h,k,beta,hkpos,hkcases,hfactor⟩

theorem RationalBranchData.diagonal_product {j : Branch p} {g : SL(2, ℤ)}
    (d : RationalBranchData p j g) :
    (d.columnGcd : ℤ)*((p : ℤ)/(d.columnGcd : ℤ))=(p : ℤ) := by
  rcases d.primeCases with hd | hd
  · rw [hd]
    simp
  · rw [hd]
    simp [show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne']

/-- Concrete derived normalized affine action for EVERY actual physical
branch and EVERY original integral rational-cusp frame. -/
theorem actual_normalized_frame_action (hprime : p.Prime) (j : Branch p) (g : SL(2, ℤ)) (z : ℍ) :
    let d := actualRationalBranchData p hprime j g
    branchSL p hp j • (normalizedScaling N hN g • z) =
      normalizedScaling N hN d.outputFrame • positiveAffineAction
        (frameAffineHeight N p d.columnGcd g d.outputFrame)
        (frameAffineShift N p d.columnGcd d.beta d.outputFrame)
        (frameAffineHeight_pos N p hN hp d.positive g d.outputFrame) z := by
  let d := actualRationalBranchData p hprime j g
  exact normalized_frame_action_of_integer_normalForm N p hN hp j g d.outputFrame d.columnGcd
    d.positive d.beta (RationalBranchData.diagonal_product p hp d) d.integerFactor z
end
end ImbalancedChen.Part3.ActualHeckeNormalizedFrameAffine20261026b



