import ImbalancedChen.Part3ActualHeckeIntersectionSubgroup
import Mathlib.RingTheory.Coprime.Lemmas

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual Gamma0(N) right action is transitive on the p+1 physical
Hecke branches for prime p not dividing N. Each finite branch b is
reached by a displayed integral Gamma0 matrix with lower row
(N,N*b+p), determinant one paid by actual Bezout. No transitivity,
finite-index formula, or covering decomposition is assumed.
-/

namespace ImbalancedChen.Part3.ActualHeckeBranchTransitivity20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualHeckeIntersectionSubgroup20261026b Gamma0ActualCuspsSourceOnly

/-- Actual right-action composition, derived from both actual left
factors and the proved separation of the displayed branches. -/
theorem branchImage_mul (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g h : CongruenceSubgroup.Gamma0 N) (j : Branch p) :
    branchImage N p hp hpN (g*h) (g*h).property j =
      branchImage N p hp hpN h h.property (branchImage N p hp hpN g g.property j) := by
  obtain ⟨a, ha, hea⟩ := branchImage_factor N p hp hpN g g.property j
  obtain ⟨b, hb, heb⟩ := branchImage_factor N p hp hpN h h.property
    (branchImage N p hp hpN g g.property j)
  obtain ⟨c, hc, hec⟩ := branchImage_factor N p hp hpN (g*h) (g*h).property j
  apply branch_eq_of_two_factorizations p hp _ _ c (a*b)
  calc
    _ = branchMatrix p j * (((g*h : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) :
        Matrix (Fin 2) (Fin 2) ℤ) := hec.symm
    _ = (branchMatrix p j * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) *
        ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [Subgroup.coe_mul, coe_mul, Matrix.mul_assoc]
    _ = ((a : Matrix (Fin 2) (Fin 2) ℤ) *
        branchMatrix p (branchImage N p hp hpN g g.property j)) *
        ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [hea]
    _ = (a : Matrix (Fin 2) (Fin 2) ℤ) *
        ((b : Matrix (Fin 2) (Fin 2) ℤ) *
          branchMatrix p (branchImage N p hp hpN h h.property
            (branchImage N p hp hpN g g.property j))) := by
      rw [Matrix.mul_assoc, heb]
    _ = _ := by rw [← Matrix.mul_assoc, ← coe_mul]

/-- Every finite branch has an actual Gamma0 matrix reaching it.
The lower row (N,N*b+p) is primitive by the actual coprimality of N,p. -/
theorem finite_branch_reached (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (b : ZMod p) :
    ∃ g : CongruenceSubgroup.Gamma0 N, branchImage N p hp hpN g g.property none = some b := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime N p := (hp.coprime_iff_not_dvd.mpr hpN).symm
  obtain ⟨u, v, hbez⟩ := hcop.isCoprime
  let g0 : SL(2, ℤ) :=
    ⟨!![v, v*(b.val : ℤ)-u; (N : ℤ), (N : ℤ)*(b.val : ℤ)+(p : ℤ)], by
      simp only [Matrix.det_fin_two_of]
      linear_combination hbez⟩
  have hg0 : g0 ∈ CongruenceSubgroup.Gamma0 N := by
    rw [gamma0_mem_iff_level_dvd_c]
    exact dvd_refl _
  let g : CongruenceSubgroup.Gamma0 N := ⟨g0,hg0⟩
  refine ⟨g, ?_⟩
  have hNZ : (N : ZMod p) ≠ 0 := by
    intro hz
    have hd : (p : ℤ) ∣ (N : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (N : ℤ) p).mp (by simpa only [Int.cast_natCast] using hz)
    exact hpN (Int.natCast_dvd_natCast.mp hd)
  obtain ⟨h, hh, heq⟩ := branchImage_factor N p hp hpN g g.property none
  cases hk : branchImage N p hp hpN g g.property none with
  | none =>
    have hd := (infinity_branch_fixed_iff N p hp hpN g g.property).mp hk
    exact (hpN (Int.natCast_dvd_natCast.mp hd)).elim
  | some k =>
    rw [hk] at heq
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) heq
    have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 1) heq
    simp [branchMatrix, Matrix.mul_fin_two, g, g0] at h10 h11
    rw [← h10] at h11
    have hmod := congrArg (fun z : ℤ => (z : ZMod p)) h11
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      ZMod.natCast_zmod_val, zero_mul, add_zero] at hmod
    have hbk : b = k := mul_left_cancel₀ hNZ hmod
    simpa only [hk] using congrArg some hbk.symm

/-- Actual transitivity, with actual integral matrices and actual level
membership constructed, including the infinity branch. -/
theorem every_branch_reached (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) :
    ∃ g : CongruenceSubgroup.Gamma0 N, branchImage N p hp hpN g g.property none = j := by
  cases j with
  | none =>
    refine ⟨1, (infinity_branch_fixed_iff N p hp hpN 1 (1 : CongruenceSubgroup.Gamma0 N).property).mpr ?_⟩
    simp
  | some b => exact finite_branch_reached N p hp hpN b

end
end ImbalancedChen.Part3.ActualHeckeBranchTransitivity20261026b
