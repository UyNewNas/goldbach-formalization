import ImbalancedChen.Part3ActualPrimeHeckeBranchPermutation
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual determinant-p integer Hecke branches are normalized uniformly
by 1/sqrt(p) into actual SL2(R). Their native upper-half-plane action is
exactly z->p*z and z->(z+b)/p. The proved integer branch factorization
lifts to equality of actual real group elements; no action identity or
unknown scaling frame is supplied as a premise.
-/

namespace ImbalancedChen.Part3.ActualPrimeHeckeRealBranch20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b

def branchRealMatrix (p : ℕ) (j : Branch p) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt (p : ℝ))⁻¹ • (branchMatrix p j).map (Int.castRingHom ℝ)

theorem branchRealMatrix_det (p : ℕ) (hp : 0 < p) (j : Branch p) :
    Matrix.det (branchRealMatrix p j) = 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpR).ne'
  have hsq := Real.sq_sqrt hpR.le
  cases j <;>
    simp [branchRealMatrix, branchMatrix, Matrix.det_fin_two_of, smul_eq_mul] <;>
    field_simp [hs] <;> nlinarith [hsq]

def branchSL (p : ℕ) (hp : 0 < p) (j : Branch p) : SL(2, ℝ) :=
  ⟨branchRealMatrix p j, branchRealMatrix_det p hp j⟩

def castIntegral (g : SL(2, ℤ)) : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g

theorem castIntegral_smul (g : SL(2, ℤ)) (z : ℍ) : castIntegral g • z = g • z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [castIntegral, Matrix.SpecialLinearGroup.map_apply_coe]

/-- The uniform scalar normalization commutes with both sides of actual
integer matrix factorization; the displayed real group equality follows. -/
theorem branchSL_factor (p : ℕ) (hp : 0 < p) (j k : Branch p) (g h : SL(2, ℤ))
    (heq : branchMatrix p j * (g : Matrix (Fin 2) (Fin 2) ℤ) =
      (h : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p k) :
    branchSL p hp j * castIntegral g = castIntegral h * branchSL p hp k := by
  apply Subtype.ext
  change branchRealMatrix p j * ((g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) =
    ((h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) * branchRealMatrix p k
  simp only [branchRealMatrix, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  have hmap := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (Int.castRingHom ℝ)) heq
  simpa only [Matrix.map_mul] using hmap

/-- Actual branch at infinity, in native physical coordinates. -/
theorem branchSL_none_coe (p : ℕ) (hp : 0 < p) (z : ℍ) :
    ((branchSL p hp none • z : ℍ) : ℂ) = (p : ℂ)*(z : ℂ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpR).ne'
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [branchSL, branchRealMatrix, branchMatrix, Matrix.SpecialLinearGroup.coeFn_eq_coe,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_natCast, smul_eq_mul] <;>
    field_simp [hs] <;> ring

/-- Every finite branch has its actual residue representative and its
original physical height divided by p. -/
theorem branchSL_some_coe (p : ℕ) (hp : 0 < p) (b : ZMod p) (z : ℍ) :
    ((branchSL p hp (some b) • z : ℍ) : ℂ) = ((z : ℂ)+(b.val : ℂ))/(p : ℂ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpR).ne'
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [branchSL, branchRealMatrix, branchMatrix, Matrix.SpecialLinearGroup.coeFn_eq_coe,
    Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_natCast, smul_eq_mul] <;>
    field_simp [hs, hpC] <;> ring

/-- Actual native action factorization for the constructed branch
permutation. Every left factor belongs to the original Gamma0 group. -/
theorem actual_branch_action_factor (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    ∃ h : SL(2, ℤ), h ∈ CongruenceSubgroup.Gamma0 N ∧ ∀ z : ℍ,
      branchSL p hp.pos j • (g • z) =
        h • (branchSL p hp.pos (branchPermutation N p hp hpN g hg j) • z) := by
  obtain ⟨h, hh, heq⟩ := branchImage_factor N p hp hpN g hg j
  refine ⟨h, hh, fun z => ?_⟩
  rw [← castIntegral_smul g, ← mul_smul, branchSL_factor p hp.pos j _ g h heq,
    mul_smul, castIntegral_smul]

end
end ImbalancedChen.Part3.ActualPrimeHeckeRealBranch20261026b
