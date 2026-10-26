import ImbalancedChen.Part3ActualPrimeHeckeRightFactor
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Right multiplication by each actual Gamma0(N) matrix permutes the p+1
displayed prime-Hecke branches up to actual left Gamma0(N) factors.
The map and its inverse are derived from the proved factorization and
proved branch separation. Actual finite trace reindexing follows; no
permutation, double-coset decomposition, or trace invariance is assumed.
-/

namespace ImbalancedChen.Part3.ActualPrimeHeckeBranchPermutation20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRightFactor20261026b

def branchImage (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (j : Branch p) : Branch p :=
  Classical.choose (actual_branch_right_factor N p hp hpN g hg j)

theorem branchImage_factor (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    ∃ h : SL(2, ℤ), h ∈ CongruenceSubgroup.Gamma0 N ∧
      branchMatrix p j * (g : Matrix (Fin 2) (Fin 2) ℤ) =
        (h : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p (branchImage N p hp hpN g hg j) :=
  Classical.choose_spec (actual_branch_right_factor N p hp hpN g hg j)

/-- Right multiplication by the actual inverse recovers the original
displayed branch. The proof uses the constructed factors and separation. -/
theorem branchImage_inverse (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    branchImage N p hp hpN g⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hg)
      (branchImage N p hp hpN g hg j) = j := by
  obtain ⟨a, ha, hea⟩ := branchImage_factor N p hp hpN g hg j
  obtain ⟨b, hb, heb⟩ := branchImage_factor N p hp hpN g⁻¹
    ((CongruenceSubgroup.Gamma0 N).inv_mem hg) (branchImage N p hp hpN g hg j)
  apply Eq.symm
  apply branch_eq_of_left_integral p hp j _ (a*b)
  calc
    branchMatrix p j = (branchMatrix p j * (g : Matrix (Fin 2) (Fin 2) ℤ)) *
        ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Matrix.mul_assoc, ← coe_mul, mul_inv_cancel, coe_one, Matrix.mul_one]
    _ = ((a : Matrix (Fin 2) (Fin 2) ℤ) *
        branchMatrix p (branchImage N p hp hpN g hg j)) *
        ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [hea]
    _ = (a : Matrix (Fin 2) (Fin 2) ℤ) *
        ((b : Matrix (Fin 2) (Fin 2) ℤ) *
          branchMatrix p (branchImage N p hp hpN g⁻¹
            ((CongruenceSubgroup.Gamma0 N).inv_mem hg) (branchImage N p hp hpN g hg j))) := by
      rw [Matrix.mul_assoc, heb]
    _ = _ := by rw [← Matrix.mul_assoc, ← coe_mul]

/-- The actual physical branches form a proved permutation. -/
def branchPermutation (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) : Branch p ≃ Branch p where
  toFun := branchImage N p hp hpN g hg
  invFun := branchImage N p hp hpN g⁻¹ ((CongruenceSubgroup.Gamma0 N).inv_mem hg)
  left_inv := branchImage_inverse N p hp hpN g hg
  right_inv := by
    intro j
    simpa only [inv_inv] using branchImage_inverse N p hp hpN g⁻¹
      ((CongruenceSubgroup.Gamma0 N).inv_mem hg) j

/-- Exact finite trace reindexing on the actual integer representative
matrices. Its sole invariance premise is the original left Gamma0 law for F. -/
theorem actual_branch_trace_reindex (N p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (F : Matrix (Fin 2) (Fin 2) ℤ → ℂ)
    (hF : ∀ h : SL(2, ℤ), h ∈ CongruenceSubgroup.Gamma0 N →
      ∀ A : Matrix (Fin 2) (Fin 2) ℤ, F ((h : Matrix (Fin 2) (Fin 2) ℤ)*A) = F A) :
    (∑ j : Branch p, F (branchMatrix p j * (g : Matrix (Fin 2) (Fin 2) ℤ))) =
      ∑ j : Branch p, F (branchMatrix p j) := by
  calc
    _ = ∑ j : Branch p, F (branchMatrix p (branchPermutation N p hp hpN g hg j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨h, hh, heq⟩ := branchImage_factor N p hp hpN g hg j
      exact (congrArg F heq).trans (hF h hh _)
    _ = _ := (branchPermutation N p hp hpN g hg).sum_comp (fun j => F (branchMatrix p j))

end
end ImbalancedChen.Part3.ActualPrimeHeckeBranchPermutation20261026b
