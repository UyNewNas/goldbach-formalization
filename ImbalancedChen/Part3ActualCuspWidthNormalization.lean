import ImbalancedChen.Part3Gamma0ActualCusps
import ImbalancedChen.Part3ActualCuspScalingSourceOnly
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
The actual old scaling matrix at positive integer level is cuspOneMatrix
times diag(sqrt N,1/sqrt N). Its conjugation carries period one to the
integer cusp-1 stabilizer period N inside Mathlib's Gamma0 N.
The second import names the future installed sibling cusp-scaling draft.
-/

namespace ImbalancedChen.Part3.ActualCuspWidthNormalizationSourceOnly
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup
open Gamma0ActualCuspsSourceOnly
open P3ActualCuspScalingSourceOnly

private def cuspOneReal : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) cuspOneMatrix

def realTranslation (k : ℤ) : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (ModularGroup.T ^ k)

/-- Determinant-one diagonal matrix taking unit translation to N translation. -/
private def widthDiagonal (N : ℕ) (hN : 0 < N) : SL(2, ℝ) :=
  ⟨!![Real.sqrt (N : ℝ), 0; 0, 1 / Real.sqrt (N : ℝ)], by
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hs : Real.sqrt (N : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 hNr).ne'
    simp [Matrix.det_fin_two_of, hs]⟩

/-- Literal factorization of the sibling's S_old matrix. -/
theorem oldScaling_factor (N : ℕ) (hN : 0 < N) :
    oldSL (N : ℝ) (by exact_mod_cast hN) =
      cuspOneReal * widthDiagonal N hN := by
  apply Subtype.ext
  change oldScaling (N : ℝ) =
    (cuspOneReal : Matrix (Fin 2) (Fin 2) ℝ) *
      (widthDiagonal N hN : Matrix (Fin 2) (Fin 2) ℝ)
  simp [oldScaling, cuspOneReal, cuspOneMatrix, widthDiagonal,
    Matrix.mul_fin_two, Matrix.SpecialLinearGroup.map_apply_coe]

/-- The real diagonal scaling turns T(k) into T(Nk). -/
private theorem widthDiagonal_conj_translation (N : ℕ) (hN : 0 < N)
    (k : ℤ) :
    widthDiagonal N hN * realTranslation k * (widthDiagonal N hN)⁻¹ =
      realTranslation ((N : ℤ) * k) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hNr.le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [widthDiagonal, realTranslation, SL2_inv_expl,
      ModularGroup.coe_T_zpow, coe_mul, Matrix.mul_fin_two,
      Matrix.SpecialLinearGroup.map_apply_coe] <;>
    field_simp [hs] <;>
    nlinarith [hsqr]

/-- Real S_old conjugation is exactly the cast of an integral cusp-1
translation at a multiple of the level. -/
theorem oldSL_conj_translation_eq_integral (N : ℕ) (hN : 0 < N)
    (k : ℤ) :
    oldSL (N : ℝ) (by exact_mod_cast hN) * realTranslation k *
        (oldSL (N : ℝ) (by exact_mod_cast hN))⁻¹ =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
        (cuspOneMatrix * ModularGroup.T ^ ((N : ℤ) * k) *
          cuspOneMatrix⁻¹) := by
  rw [oldScaling_factor N hN]
  calc
    (cuspOneReal * widthDiagonal N hN) * realTranslation k *
        (cuspOneReal * widthDiagonal N hN)⁻¹ =
      cuspOneReal *
        (widthDiagonal N hN * realTranslation k *
          (widthDiagonal N hN)⁻¹) * cuspOneReal⁻¹ := by group
    _ = cuspOneReal * realTranslation ((N : ℤ) * k) * cuspOneReal⁻¹ := by
      rw [widthDiagonal_conj_translation N hN k]
    _ = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
          (cuspOneMatrix * ModularGroup.T ^ ((N : ℤ) * k) *
            cuspOneMatrix⁻¹) := by
      simp [cuspOneReal, realTranslation]

/-- The integral matrix just obtained belongs to the actual Gamma0 level. -/
theorem normalized_period_integral_mem_gamma0 (N : ℕ) (hN : 0 < N)
    (k : ℤ) :
    cuspOneMatrix * ModularGroup.T ^ ((N : ℤ) * k) * cuspOneMatrix⁻¹ ∈
      CongruenceSubgroup.Gamma0 N := by
  rw [cuspOne_conj_translation_mem_gamma0_iff]
  exact ⟨k, rfl⟩

/-- Conversely the integer cusp-1 stabilizer periods are exactly Nℤ. -/
theorem cuspOne_period_iff_level_multiple (N : ℕ) (hN : 0 < N)
    (j : ℤ) :
    cuspOneMatrix * ModularGroup.T ^ j * cuspOneMatrix⁻¹ ∈
      CongruenceSubgroup.Gamma0 N ↔
      ∃ k : ℤ, j = (N : ℤ) * k := by
  rw [cuspOne_conj_translation_mem_gamma0_iff]
  rfl

end
end ImbalancedChen.Part3.ActualCuspWidthNormalizationSourceOnly
