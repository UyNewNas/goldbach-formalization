import ImbalancedChen.Part3Gamma0ActualCusps
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_CREDIT.

Literal Fricke W_N=[0,-1/sqrt(N);sqrt(N),0] at a POSITIVE integer level.
Its conjugate of the actual integer matrix[a,b;c,d] is proved equal to
[d,-c/N;-N*b,a]. Exact integer divisibility N|c supplies the quotient and
determinant proof. No normalizer or conjugacy premise is supplied.

The actual Gamma0 group has the resulting involutive automorphism, its
real image is normalized by W_N, W_N^2=-I acts as an involution on H, and
Mathlib's canonical hyperbolic volume is preserved by the literal action.
No Fourier phase, spectral assertion, or numerical execution occurs here.
-/

namespace ImbalancedChen.Part3.FrickeNormalizer

noncomputable section

open Matrix Matrix.SpecialLinearGroup MatrixGroups Set MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly

def frickeMatrix (N : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -(1 / Real.sqrt (N : ℝ)); Real.sqrt (N : ℝ), 0]

theorem frickeMatrix_det (N : ℕ) (hN : 0 < N) : Matrix.det (frickeMatrix N) = 1 := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  simp [frickeMatrix, Matrix.det_fin_two_of, hs]

def frickeSL (N : ℕ) (hN : 0 < N) : SL(2, ℝ) :=
  ⟨frickeMatrix N, frickeMatrix_det N hN⟩

def realSL (g : SL(2, ℤ)) : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g

theorem realSL_injective : Function.Injective realSL :=
  Matrix.SpecialLinearGroup.map_intCast_injective

theorem realSL_mul (g h : SL(2, ℤ)) : realSL (g * h) = realSL g * realSL h :=
  map_mul (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g h

theorem gamma0_exact_division (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (N : ℤ) * ((g : SL(2, ℤ)) 1 0 / (N : ℤ)) = (g : SL(2, ℤ)) 1 0 :=
  Int.mul_ediv_cancel' ((gamma0_mem_iff_level_dvd_c N (g : SL(2, ℤ))).mp g.property)

/-- Actual integral conjugate; division is exact from the Gamma0 level condition. -/
def integerFricke (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ) :=
  ⟨!![(g : SL(2, ℤ)) 1 1, -((g : SL(2, ℤ)) 1 0 / (N : ℤ));
      -(N : ℤ) * (g : SL(2, ℤ)) 0 1, (g : SL(2, ℤ)) 0 0], by
    have hdet : (g : SL(2, ℤ)) 0 0 * (g : SL(2, ℤ)) 1 1 -
        (g : SL(2, ℤ)) 0 1 * (g : SL(2, ℤ)) 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using (g : SL(2, ℤ)).det_coe
    rw [Matrix.det_fin_two_of]
    calc
      _ = (g : SL(2, ℤ)) 0 0 * (g : SL(2, ℤ)) 1 1 -
          (g : SL(2, ℤ)) 0 1 * ((N : ℤ) * ((g : SL(2, ℤ)) 1 0 / (N : ℤ))) := by ring
      _ = 1 := by rw [gamma0_exact_division]; exact hdet⟩

theorem integerFricke_mem_gamma0 (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    integerFricke N g ∈ CongruenceSubgroup.Gamma0 N := by
  rw [gamma0_mem_iff_level_dvd_c]
  refine ⟨-((g : SL(2, ℤ)) 0 1), ?_⟩
  change -(N : ℤ) * (g : SL(2, ℤ)) 0 1 = (N : ℤ) * -((g : SL(2, ℤ)) 0 1)
  ring

def frickeGamma0 (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) : CongruenceSubgroup.Gamma0 N :=
  ⟨integerFricke N g, integerFricke_mem_gamma0 N g⟩

theorem frickeGamma0_involutive (N : ℕ) (hN : 0 < N) : Function.Involutive (frickeGamma0 N) := by
  intro g
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change -((-(N : ℤ) * (g : SL(2, ℤ)) 0 1) / (N : ℤ)) = (g : SL(2, ℤ)) 0 1
    rw [show -(N : ℤ) * (g : SL(2, ℤ)) 0 1 =
      (-((g : SL(2, ℤ)) 0 1)) * (N : ℤ) by ring, Int.mul_ediv_cancel _ hN0, neg_neg]
  · change -(N : ℤ) * -((g : SL(2, ℤ)) 1 0 / (N : ℤ)) = (g : SL(2, ℤ)) 1 0
    simpa only [neg_mul_neg] using gamma0_exact_division N g
  · rfl

theorem frickeSL_inv_coe (N : ℕ) (hN : 0 < N) :
    ((frickeSL N hN)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1 / Real.sqrt (N : ℝ); -Real.sqrt (N : ℝ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frickeSL, frickeMatrix, SL2_inv_expl]

/-- Pure real matrix algebra before any integer quotient is interpreted. -/
theorem fricke_conjugation_matrix_formula (r : ℝ) (hr : r ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    !![0, 1 / r; -r, 0] * M * !![0, -(1 / r); r, 0] =
      !![M 1 1, -(M 1 0) / r ^ 2; -(r ^ 2) * M 0 1, M 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_fin_two] <;> field_simp [hr] <;> ring

/-- The actual real conjugate is exactly the cast of an integral Gamma0 matrix. -/
theorem frickeSL_conjugate_gamma0 (N : ℕ) (hN : 0 < N) (g : CongruenceSubgroup.Gamma0 N) :
    (frickeSL N hN)⁻¹ * realSL (g : SL(2, ℤ)) * frickeSL N hN =
      realSL (frickeGamma0 N g : SL(2, ℤ)) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNr.le
  have hquotR : (N : ℝ) * (((g : SL(2, ℤ)) 1 0 / (N : ℤ) : ℤ) : ℝ) =
      ((g : SL(2, ℤ)) 1 0 : ℝ) := by exact_mod_cast gamma0_exact_division N g
  have hcast : (((g : SL(2, ℤ)) 1 0 / (N : ℤ) : ℤ) : ℝ) =
      ((g : SL(2, ℤ)) 1 0 : ℝ) / (N : ℝ) := by
    apply (eq_div_iff hNr.ne').mpr
    simpa only [mul_comm] using hquotR
  apply Subtype.ext
  change ((frickeSL N hN)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) *
    (realSL (g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℝ) * frickeMatrix N = _
  rw [frickeSL_inv_coe]
  unfold frickeMatrix
  rw [fricke_conjugation_matrix_formula _ hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realSL, frickeGamma0, integerFricke, Matrix.SpecialLinearGroup.map_apply_coe, hsqr, hcast]

theorem frickeGamma0_mul (N : ℕ) (hN : 0 < N) (g h : CongruenceSubgroup.Gamma0 N) :
    frickeGamma0 N (g * h) = frickeGamma0 N g * frickeGamma0 N h := by
  apply Subtype.ext
  apply realSL_injective
  change realSL (frickeGamma0 N (g * h) : SL(2, ℤ)) =
    realSL ((frickeGamma0 N g : SL(2, ℤ)) * (frickeGamma0 N h : SL(2, ℤ)))
  rw [realSL_mul, ← frickeSL_conjugate_gamma0 N hN (g * h),
    ← frickeSL_conjugate_gamma0 N hN g, ← frickeSL_conjugate_gamma0 N hN h]
  change (frickeSL N hN)⁻¹ * realSL ((g : SL(2, ℤ)) * (h : SL(2, ℤ))) * frickeSL N hN = _
  rw [realSL_mul]
  group

/-- An actual involutive automorphism of the original integer Gamma0 group. -/
def frickeGamma0Aut (N : ℕ) (hN : 0 < N) : CongruenceSubgroup.Gamma0 N ≃*
    CongruenceSubgroup.Gamma0 N where
  toFun := frickeGamma0 N
  invFun := frickeGamma0 N
  left_inv := frickeGamma0_involutive N hN
  right_inv := frickeGamma0_involutive N hN
  map_mul' := frickeGamma0_mul N hN

def realGamma0 (N : ℕ) : Set (SL(2, ℝ)) :=
  Set.range (fun g : CongruenceSubgroup.Gamma0 N => realSL (g : SL(2, ℤ)))

/-- Literal set normalization W^-1 Gamma0 W=Gamma0, with both directions proved. -/
theorem frickeSL_normalizes_realGamma0 (N : ℕ) (hN : 0 < N) :
    (fun A : SL(2, ℝ) => (frickeSL N hN)⁻¹ * A * frickeSL N hN) '' realGamma0 N = realGamma0 N := by
  ext A
  constructor
  · rintro ⟨B, ⟨g, rfl⟩, rfl⟩
    exact ⟨frickeGamma0 N g, (frickeSL_conjugate_gamma0 N hN g).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨realSL (frickeGamma0 N g : SL(2, ℤ)), ⟨frickeGamma0 N g, rfl⟩, ?_⟩
    rw [frickeSL_conjugate_gamma0, frickeGamma0_involutive N hN g]

theorem frickeSL_square (N : ℕ) (hN : 0 < N) :
    frickeSL N hN * frickeSL N hN = -(1 : SL(2, ℝ)) := by
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeSL, frickeMatrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two, hs]

theorem real_negative_identity_smul (z : UpperHalfPlane) : (-(1 : SL(2, ℝ))) • z = z := by
  apply UpperHalfPlane.ext
  simp [UpperHalfPlane.coe_specialLinearGroup_apply]

theorem frickeSL_action_involutive (N : ℕ) (hN : 0 < N) :
    Function.Involutive (fun z : UpperHalfPlane => frickeSL N hN • z) := by
  intro z
  rw [← mul_smul, frickeSL_square, real_negative_identity_smul]

/-- The actual W_N action preserves Mathlib's canonical dxdy/y^2 volume. -/
theorem frickeSL_measurePreserving (N : ℕ) (hN : 0 < N) :
    MeasurePreserving (fun z : UpperHalfPlane => frickeSL N hN • z)
      (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane) := by
  change MeasurePreserving
    (fun z : UpperHalfPlane => (Matrix.SpecialLinearGroup.mapGL ℝ (frickeSL N hN)) • z)
    (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane)
  exact measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ (frickeSL N hN))
    (volume : Measure UpperHalfPlane)

end
end ImbalancedChen.Part3.FrickeNormalizer
