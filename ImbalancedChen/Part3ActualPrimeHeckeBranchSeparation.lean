import ImbalancedChen.Part3Gamma0ActualCusps
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The p+1 physical prime-Hecke representatives are actual integer matrices
of determinant p. Their left SL2(Z) cosets are pairwise distinct, proved
from the displayed entries and determinant-one equation. No abstract
double-coset decomposition or branch-permutation supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualPrimeHeckeBranchSeparation20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups

abbrev Branch (p : ℕ) := Option (ZMod p)

theorem branch_card (p : ℕ) [NeZero p] : Fintype.card (Branch p) = p+1 := by
  simp [Branch]

def branchMatrix (p : ℕ) : Branch p → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some b => !![1, (b.val : ℤ); 0, (p : ℤ)]

theorem branchMatrix_det (p : ℕ) (j : Branch p) : Matrix.det (branchMatrix p j) = (p : ℤ) := by
  cases j <;> simp [branchMatrix, Matrix.det_fin_two_of]

private theorem prime_int_not_dvd_one {p : ℕ} (hp : p.Prime) : ¬ (p : ℤ) ∣ 1 := by
  intro hd
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hd)

/-- Exact separation under actual left multiplication by SL2(Z).
This is stronger than separation under Gamma0(N), for every level N. -/
theorem branch_eq_of_left_integral (p : ℕ) (hp : p.Prime)
    (j k : Branch p) (g : SL(2, ℤ))
    (h : branchMatrix p j = (g : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p k) : j = k := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) h
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
  cases j with
  | none =>
    cases k with
    | none => rfl
    | some c =>
      simp [branchMatrix, Matrix.mul_fin_two] at h00 h10
      have hpd : (p : ℤ) ∣ 1 := by
        refine ⟨g 1 1, ?_⟩
        nlinarith [hdet]
      exact (prime_int_not_dvd_one hp hpd).elim
  | some b =>
    cases k with
    | none =>
      simp [branchMatrix, Matrix.mul_fin_two] at h00
      have hpd : (p : ℤ) ∣ 1 := ⟨g 0 0, by nlinarith [h00]⟩
      exact (prime_int_not_dvd_one hp hpd).elim
    | some c =>
      simp [branchMatrix, Matrix.mul_fin_two] at h00 h10 h01
      have hmod := congrArg (fun z : ℤ => (z : ZMod p)) h01
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
        ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val] at hmod
      have hbc : b = c := by simpa only [← h00, Int.cast_one, one_mul] using hmod
      exact congrArg some hbc

/-- Equality between two actual left-integral factorizations forces the
same physical branch, with no choice of abstract coset representatives. -/
theorem branch_eq_of_two_factorizations (p : ℕ) (hp : p.Prime)
    (j k : Branch p) (g h : SL(2, ℤ))
    (heq : (g : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p j =
      (h : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p k) : j = k := by
  apply branch_eq_of_left_integral p hp j k (g⁻¹*h)
  have hmul := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ =>
    ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * M) heq
  simpa only [← Matrix.mul_assoc, ← coe_mul, inv_mul_cancel, coe_one,
    Matrix.one_mul] using hmul

end
end ImbalancedChen.Part3.ActualPrimeHeckeBranchSeparation20261026b
