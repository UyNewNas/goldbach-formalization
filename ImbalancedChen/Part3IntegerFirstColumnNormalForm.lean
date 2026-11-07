import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual integer 2x2 first-column gcd normal form. The primitive-column
completion is REUSED from pinned Mathlib IsCoprime.exists_SL2_col, whose
proof is the literal Bezout matrix [[a,-v],[c,u]]. It is not postulated
as a factorization supplier. The first diagonal entry is the positive
natural gcd of the ORIGINAL first column, and beta is computed with the
orientation h11*M01-h01*M11. The actual h^-1*M matrix is proved upper
triangular, and its bottom-right entry follows from the actual determinant.
No cusp, Hecke normalization or preservation premise occurs in this file.
-/

namespace ImbalancedChen.Part3.IntegerFirstColumnNormalForm20261026b

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

def firstColumnGcd (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Int.gcd (M 0 0) (M 1 0)

theorem firstColumnGcd_dvd_det (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (firstColumnGcd M : ℤ) ∣ M.det := by
  rw [Matrix.det_fin_two]
  exact dvd_sub
    (dvd_mul_of_dvd_left (Int.gcd_dvd_left (M 0 0) (M 1 0)) (M 1 1))
    (dvd_mul_of_dvd_right (Int.gcd_dvd_right (M 0 0) (M 1 0)) (M 0 1))

theorem firstColumnGcd_pos (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det ≠ 0) :
    0 < firstColumnGcd M := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hzero : Int.gcd (M 0 0) (M 1 0) = 0 := hz
  obtain ⟨ha, hc⟩ := Int.gcd_eq_zero_iff.mp hzero
  apply hdet
  simp [Matrix.det_fin_two, ha, hc]

/-- Dividing BOTH actual signed first-column entries by the positive
natural gcd gives the true primitive integer column. -/
theorem divided_first_column_isCoprime (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det ≠ 0) :
    IsCoprime (M 0 0 / (firstColumnGcd M : ℤ)) (M 1 0 / (firstColumnGcd M : ℤ)) := by
  apply Int.isCoprime_iff_nat_coprime.mpr
  change Int.gcd (M 0 0 / (firstColumnGcd M : ℤ))
    (M 1 0 / (firstColumnGcd M : ℤ)) = 1
  exact Int.gcd_ediv_gcd_ediv_gcd (firstColumnGcd_pos M hdet)

/-- Genuine integral completion, upper-triangular reduction and recovery
of the original matrix. The gcd, inverse matrix and beta are all literal. -/
theorem exists_gcd_upper_triangular (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det ≠ 0) :
    ∃ h : SL(2, ℤ), ∃ beta : ℤ,
      h 0 0 = M 0 0 / (firstColumnGcd M : ℤ) ∧
      h 1 0 = M 1 0 / (firstColumnGcd M : ℤ) ∧
      beta = h 1 1 * M 0 1 - h 0 1 * M 1 1 ∧
      (h⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * M =
        !![(firstColumnGcd M : ℤ), beta; 0, M.det / (firstColumnGcd M : ℤ)] ∧
      M = (h : Matrix (Fin 2) (Fin 2) ℤ) *
        !![(firstColumnGcd M : ℤ), beta; 0, M.det / (firstColumnGcd M : ℤ)] := by
  have hk := firstColumnGcd_pos M hdet
  have hkz : (firstColumnGcd M : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  obtain ⟨h, ha, hc⟩ := (divided_first_column_isCoprime M hdet).exists_SL2_col (0 : Fin 2)
  have h00 : M 0 0 = h 0 0 * (firstColumnGcd M : ℤ) := by
    rw [ha]
    exact (Int.ediv_mul_cancel (Int.gcd_dvd_left (M 0 0) (M 1 0))).symm
  have h10 : M 1 0 = h 1 0 * (firstColumnGcd M : ℤ) := by
    rw [hc]
    exact (Int.ediv_mul_cancel (Int.gcd_dvd_right (M 0 0) (M 1 0))).symm
  have hdetone : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using h.det_coe
  let beta : ℤ := h 1 1 * M 0 1 - h 0 1 * M 1 1
  let bottom : ℤ := h 0 0 * M 1 1 - h 1 0 * M 0 1
  have h01 : M 0 1 = h 0 0 * beta + h 0 1 * bottom := by
    dsimp [beta, bottom]
    linear_combination -(M 0 1) * hdetone
  have h11 : M 1 1 = h 1 0 * beta + h 1 1 * bottom := by
    dsimp [beta, bottom]
    linear_combination -(M 1 1) * hdetone
  have hfactor : M = (h : Matrix (Fin 2) (Fin 2) ℤ) *
      !![(firstColumnGcd M : ℤ), beta; 0, bottom] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_fin_two] using h00
    · simpa [Matrix.mul_fin_two] using h01
    · simpa [Matrix.mul_fin_two] using h10
    · simpa [Matrix.mul_fin_two] using h11
  have hproduct : (firstColumnGcd M : ℤ) * bottom = M.det := by
    have hd := congrArg Matrix.det hfactor
    rw [Matrix.det_mul, h.det_coe, one_mul, Matrix.det_fin_two_of] at hd
    simpa only [mul_zero, sub_zero] using hd.symm
  have hquot : M.det / (firstColumnGcd M : ℤ) = bottom :=
    Int.ediv_eq_of_eq_mul_right hkz hproduct.symm
  have hinverse : (h⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * M =
      !![(firstColumnGcd M : ℤ), beta; 0, bottom] := by
    calc
      (h⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * M =
          (h⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) *
            ((h : Matrix (Fin 2) (Fin 2) ℤ) * !![(firstColumnGcd M : ℤ), beta; 0, bottom]) :=
        congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ =>
          (h⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * A) hfactor
      _ = _ := by
        rw [← Matrix.mul_assoc, ← coe_mul, inv_mul_cancel, coe_one, Matrix.one_mul]
  refine ⟨h, beta, ha, hc, rfl, ?_, ?_⟩
  · rw [hquot]
    exact hinverse
  · rw [hquot]
    exact hfactor

end
end ImbalancedChen.Part3.IntegerFirstColumnNormalForm20261026b
