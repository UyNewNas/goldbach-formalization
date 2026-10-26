import ImbalancedChen.Part3ActualPrimeHeckeBranchSeparation
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Explicit prime-mod-p factorization A_j gamma = gamma' A_k for the actual
p+1 determinant-p Hecke matrices and gamma in Gamma0(N), p not dividing N.
All four cases construct the integral determinant-one left factor. The
only division by p in the Gamma0 gate is paid by the actual coprimality
of p and N. No branch decomposition or permutation is assumed.
-/

namespace ImbalancedChen.Part3.ActualPrimeHeckeRightFactor20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups
open ActualPrimeHeckeBranchSeparation20261026b Gamma0ActualCuspsSourceOnly

/-- Prime-field inversion produces an actual canonical residue solving
the needed integral divisibility equation. -/
theorem prime_residue_quotient (p : ℕ) (hp : p.Prime) (A B : ℤ)
    (hA : ¬ (p : ℤ) ∣ A) :
    ∃ k : ZMod p, (p : ℤ) ∣ B-A*(k.val : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hAN : (A : ZMod p) ≠ 0 := fun hz =>
    hA ((ZMod.intCast_zmod_eq_zero_iff_dvd A p).mp hz)
  let k : ZMod p := (B : ZMod p)/(A : ZMod p)
  refine ⟨k, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  dsimp [k]
  field_simp [hAN] <;> ring

private theorem level_dvd_prime_quotient (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (c : ℤ) (hNc : (N : ℤ) ∣ c) (hpc : (p : ℤ) ∣ c) : (N : ℤ) ∣ c/(p : ℤ) := by
  have hcop : Nat.Coprime N p := (hp.coprime_iff_not_dvd.mpr hpN).symm
  have hgcd : Int.gcd (N : ℤ) (p : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcop
  apply Int.dvd_of_dvd_mul_right_of_gcd_one (b := (p : ℤ))
  · simpa only [Int.mul_ediv_cancel' hpc] using hNc
  · exact hgcd

theorem infinity_right_factor (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ k : Branch p, ∃ h : SL(2, ℤ), h ∈ CongruenceSubgroup.Gamma0 N ∧
      branchMatrix p none * (g : Matrix (Fin 2) (Fin 2) ℤ) =
        (h : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p k := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hNc : (N : ℤ) ∣ g 1 0 := (gamma0_mem_iff_level_dvd_c N g).mp hg
  by_cases hc : (p : ℤ) ∣ g 1 0
  · have hq : (p : ℤ)*(g 1 0/(p : ℤ)) = g 1 0 := Int.mul_ediv_cancel' hc
    let h : SL(2, ℤ) := ⟨!![g 0 0, (p : ℤ)*g 0 1; g 1 0/(p : ℤ), g 1 1], by
      simp only [Matrix.det_fin_two_of]
      linear_combination hdet - (g 0 1)*hq⟩
    refine ⟨none, h, ?_, ?_⟩
    · rw [gamma0_mem_iff_level_dvd_c]
      exact level_dvd_prime_quotient N p hp hpN (g 1 0) hNc hc
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [branchMatrix, h, Matrix.mul_fin_two] <;> nlinarith [hq]
  · obtain ⟨k, hk⟩ := prime_residue_quotient p hp (g 1 0) (g 1 1) hc
    have hq : (p : ℤ)*((g 1 1-g 1 0*(k.val : ℤ))/(p : ℤ)) =
        g 1 1-g 1 0*(k.val : ℤ) := Int.mul_ediv_cancel' hk
    let h : SL(2, ℤ) :=
      ⟨!![(p : ℤ)*g 0 0, g 0 1-g 0 0*(k.val : ℤ);
        g 1 0, (g 1 1-g 1 0*(k.val : ℤ))/(p : ℤ)], by
        simp only [Matrix.det_fin_two_of]
        linear_combination hdet + (g 0 0)*hq⟩
    refine ⟨some k, h, ?_, ?_⟩
    · rw [gamma0_mem_iff_level_dvd_c]
      exact hNc
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [branchMatrix, h, Matrix.mul_fin_two] <;> nlinarith [hq]

theorem finite_right_factor (N p : ℕ) (hp : p.Prime)
    (b : ZMod p) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ k : Branch p, ∃ h : SL(2, ℤ), h ∈ CongruenceSubgroup.Gamma0 N ∧
      branchMatrix p (some b) * (g : Matrix (Fin 2) (Fin 2) ℤ) =
        (h : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p k := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hNc : (N : ℤ) ∣ g 1 0 := (gamma0_mem_iff_level_dvd_c N g).mp hg
  let A : ℤ := g 0 0+(b.val : ℤ)*g 1 0
  let B : ℤ := g 0 1+(b.val : ℤ)*g 1 1
  by_cases hA : (p : ℤ) ∣ A
  · have hq : (p : ℤ)*(A/(p : ℤ)) = A := Int.mul_ediv_cancel' hA
    let h : SL(2, ℤ) := ⟨!![A/(p : ℤ), B; g 1 0, (p : ℤ)*g 1 1], by
      simp only [Matrix.det_fin_two_of]
      dsimp [A, B] at hq ⊢
      linear_combination hdet + (g 1 1)*hq⟩
    refine ⟨none, h, ?_, ?_⟩
    · rw [gamma0_mem_iff_level_dvd_c]
      exact hNc
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [branchMatrix, h, A, B, Matrix.mul_fin_two] <;>
        dsimp [A, B] at hq <;> nlinarith [hq]
  · obtain ⟨k, hk⟩ := prime_residue_quotient p hp A B hA
    have hq : (p : ℤ)*((B-A*(k.val : ℤ))/(p : ℤ)) = B-A*(k.val : ℤ) :=
      Int.mul_ediv_cancel' hk
    let h : SL(2, ℤ) :=
      ⟨!![A, (B-A*(k.val : ℤ))/(p : ℤ); (p : ℤ)*g 1 0, g 1 1-g 1 0*(k.val : ℤ)], by
        simp only [Matrix.det_fin_two_of]
        dsimp [A, B] at hq ⊢
        linear_combination hdet - (g 1 0)*hq⟩
    refine ⟨some k, h, ?_, ?_⟩
    · rw [gamma0_mem_iff_level_dvd_c]
      exact dvd_mul_of_dvd_right hNc (p : ℤ)
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [branchMatrix, h, A, B, Matrix.mul_fin_two] <;>
        dsimp [A, B] at hq <;> nlinarith [hq]

/-- Every actual branch after right multiplication by an actual Gamma0
matrix has a proved actual Gamma0 left factor and another displayed branch. -/
theorem actual_branch_right_factor (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    ∃ k : Branch p, ∃ h : SL(2, ℤ), h ∈ CongruenceSubgroup.Gamma0 N ∧
      branchMatrix p j * (g : Matrix (Fin 2) (Fin 2) ℤ) =
        (h : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p k := by
  cases j with
  | none => exact infinity_right_factor N p hp hpN g hg
  | some b => exact finite_right_factor N p hp b g hg

end
end ImbalancedChen.Part3.ActualPrimeHeckeRightFactor20261026b
