import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
Actual Gamma0 level and the two elementary rational-cusp matrix calculations.
Mathlib already defines Gamma0 and proves its width at infinity; those
objects are reused here. No spectral decomposition or old/newform theorem
is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups ModularGroup

/-- An integer matrix lies in Mathlib's Gamma0 exactly when its c-entry is
divisible by the natural level. -/
theorem gamma0_mem_iff_level_dvd_c (N : ℕ) (g : SL(2, ℤ)) :
    g ∈ CongruenceSubgroup.Gamma0 N ↔ (N : ℤ) ∣ g 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd

/-- Every integral translation fixes the standard Gamma0 cusp at infinity. -/
theorem translation_mem_gamma0 (N : ℕ) (k : ℤ) :
    ModularGroup.T ^ k ∈ CongruenceSubgroup.Gamma0 N := by
  simp [CongruenceSubgroup.Gamma0_mem, ModularGroup.coe_T_zpow]

/-- The stabilizer condition at infinity is exactly c=0 inside Gamma0. -/
theorem gamma0_fix_infty_iff (N : ℕ) (g : SL(2, ℤ)) :
    g ∈ CongruenceSubgroup.Gamma0 N ∧
        mapGL ℝ g • (∞ : OnePoint ℝ) = ∞ ↔
      g ∈ CongruenceSubgroup.Gamma0 N ∧ g 1 0 = 0 := by
  simp [smul_infty_eq_self_iff, mapGL_coe_matrix]

/-- Reuse Mathlib's actual strict cusp width at infinity. -/
theorem gamma0_strict_width_infty_one (N : ℕ) :
    Subgroup.strictWidthInfty
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) = 1 :=
  CongruenceSubgroup.strictWidthInfty_Gamma0 N

/-- The integral determinant-one matrix sending infinity to the rational cusp 1. -/
def cuspOneMatrix : SL(2, ℤ) :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩

theorem cuspOneMatrix_smul_infty :
    mapGL ℝ cuspOneMatrix • (∞ : OnePoint ℝ) = (1 : ℝ) := by
  simp [smul_infty_eq_ite, cuspOneMatrix, mapGL_coe_matrix]

/-- Conjugating a translation by the cusp-1 scaling matrix gives c=-k. -/
theorem cuspOne_conj_translation_c (k : ℤ) :
    (cuspOneMatrix * ModularGroup.T ^ k * cuspOneMatrix⁻¹) 1 0 = -k := by
  simp [cuspOneMatrix, SL2_inv_expl, ModularGroup.coe_T_zpow,
    Matrix.mul_fin_two, coe_mul] <;> ring

/-- The corresponding cusp-1 translation is in Gamma0 precisely at
integer periods divisible by the actual level. -/
theorem cuspOne_conj_translation_mem_gamma0_iff (N : ℕ) (k : ℤ) :
    cuspOneMatrix * ModularGroup.T ^ k * cuspOneMatrix⁻¹ ∈
      CongruenceSubgroup.Gamma0 N ↔ (N : ℤ) ∣ k := by
  rw [gamma0_mem_iff_level_dvd_c,
    cuspOne_conj_translation_c]
  simp

end
end ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
