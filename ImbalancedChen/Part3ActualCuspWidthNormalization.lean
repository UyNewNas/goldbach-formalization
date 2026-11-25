import ImbalancedChen.Part3Gamma0ActualCusps
import ImbalancedChen.Part3CuspScalingMatrices
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
  have hc : (cuspOneReal : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 1, 1] := by
    change (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  rw [hc]
  simp [oldScaling, widthDiagonal]

/-- The real diagonal scaling turns T(k) into T(Nk). -/
private theorem widthDiagonal_conj_translation (N : ℕ) (hN : 0 < N)
    (k : ℤ) :
    widthDiagonal N hN * realTranslation k * (widthDiagonal N hN)⁻¹ =
      realTranslation ((N : ℤ) * k) := by
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNr).ne'
  have hsqr : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt hNr.le
  have hT (m : ℤ) : (realTranslation m).1 = !![1, (m : ℝ); 0, 1] := by
    change (ModularGroup.T ^ m).1.map (Int.castRingHom ℝ) = _
    rw [ModularGroup.coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  have hprod : Real.sqrt (N : ℝ) * (k : ℝ) * Real.sqrt (N : ℝ) =
      (N : ℝ) * (k : ℝ) := by
    calc
      _ = Real.sqrt (N : ℝ) ^ 2 * (k : ℝ) := by ring
      _ = _ := by rw [hsqr]
  rw [SL2_inv_expl]
  apply Subtype.ext
  change !![Real.sqrt (N : ℝ), 0; 0, 1 / Real.sqrt (N : ℝ)] * (realTranslation k).1 *
    !![1 / Real.sqrt (N : ℝ), -0; -0, Real.sqrt (N : ℝ)] = (realTranslation _).1
  rw [hT, hT, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [hs, hprod]

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
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [cuspOne_conj_translation_mem_gamma0_iff]
  exact ⟨k, rfl⟩

/-- Conversely the integer cusp-1 stabilizer periods are exactly Nℤ. -/
theorem cuspOne_period_iff_level_multiple (N : ℕ) (hN : 0 < N)
    (j : ℤ) :
    cuspOneMatrix * ModularGroup.T ^ j * cuspOneMatrix⁻¹ ∈
      CongruenceSubgroup.Gamma0 N ↔
      ∃ k : ℤ, j = (N : ℤ) * k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [cuspOne_conj_translation_mem_gamma0_iff]
  rfl

end
end ImbalancedChen.Part3.ActualCuspWidthNormalizationSourceOnly
