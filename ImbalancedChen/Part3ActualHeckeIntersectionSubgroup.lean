import ImbalancedChen.Part3ActualPrimeHeckeBranchPermutation

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The concrete Hecke intersection subgroup inside Gamma0(N) is exactly
Gamma0(N*p). Its elements are exactly those fixing the infinity Hecke
branch, equivalently those admitting an actual Gamma0(N) left factor at
that same branch. The level product is proved using actual coprimality;
no finite-cover degree or measure identity is assumed.
-/

namespace ImbalancedChen.Part3.ActualHeckeIntersectionSubgroup20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open Gamma0ActualCuspsSourceOnly

def heckeIntersection (N p : ℕ) : Subgroup (CongruenceSubgroup.Gamma0 N) :=
  (CongruenceSubgroup.Gamma0 (N*p)).subgroupOf (CongruenceSubgroup.Gamma0 N)

theorem gamma0_product_prime_mem_iff (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    g ∈ CongruenceSubgroup.Gamma0 (N*p) ↔ (p : ℤ) ∣ g 1 0 := by
  rw [gamma0_mem_iff_level_dvd_c]
  have hNc := (gamma0_mem_iff_level_dvd_c N g).mp hg
  constructor
  · intro hd
    exact dvd_trans (by exact_mod_cast (dvd_mul_left p N)) hd
  · intro hpc
    have hcop : Nat.Coprime N p := (hp.coprime_iff_not_dvd.mpr hpN).symm
    have hNa : N ∣ (g 1 0).natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hNc
    have hpa : p ∣ (g 1 0).natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hpc
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_natCast] using hcop.mul_dvd_of_dvd_of_dvd hNa hpa

/-- The actual branch chosen by the proved decomposition is infinity
exactly when the original lower-left integer entry is divisible by p. -/
theorem infinity_branch_fixed_iff (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    branchImage N p hp hpN g hg none = none ↔ (p : ℤ) ∣ g 1 0 := by
  obtain ⟨h, hh, heq⟩ := branchImage_factor N p hp hpN g hg none
  constructor
  · intro hfix
    rw [hfix] at heq
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) heq
    simp [branchMatrix, Matrix.mul_fin_two] at h10
    exact ⟨h 1 0, by nlinarith [h10]⟩
  · intro hpc
    cases hk : branchImage N p hp hpN g hg none with
    | none => exact hk
    | some b =>
      rw [hk] at heq
      have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 0 0) heq
      have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A 1 0) heq
      simp [branchMatrix, Matrix.mul_fin_two] at h00 h10
      have hd00 : (p : ℤ) ∣ h 0 0 := by
        rw [← h00]
        exact dvd_mul_right _ _
      have hd10 : (p : ℤ) ∣ h 1 0 := by rwa [← h10]
      have hdet : h 0 0*h 1 1-h 0 1*h 1 0 = 1 := by
        simpa only [Matrix.det_fin_two] using h.det_coe
      have hd1 : (p : ℤ) ∣ 1 := hdet ▸ dvd_sub
        (dvd_mul_of_dvd_left hd00 _) (dvd_mul_of_dvd_right hd10 _)
      exact (hp.not_dvd_one (Int.natCast_dvd_natCast.mp hd1)).elim

theorem heckeIntersection_mem_iff_fixed (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CongruenceSubgroup.Gamma0 N) :
    g ∈ heckeIntersection N p ↔ branchImage N p hp hpN g g.property none = none := by
  rw [heckeIntersection, Subgroup.mem_subgroupOf,
    gamma0_product_prime_mem_iff N p hp hpN g g.property,
    infinity_branch_fixed_iff N p hp hpN g g.property]

/-- Concrete finite-cover stabilizer criterion, with ACTUAL integral
Gamma0 matrices on both sides of the determinant-p representative. -/
theorem heckeIntersection_mem_iff_same_branch_factor (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CongruenceSubgroup.Gamma0 N) :
    g ∈ heckeIntersection N p ↔
      ∃ h : SL(2, ℤ), h ∈ CongruenceSubgroup.Gamma0 N ∧
        branchMatrix p none * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
          (h : Matrix (Fin 2) (Fin 2) ℤ) * branchMatrix p none := by
  rw [heckeIntersection_mem_iff_fixed N p hp hpN g]
  constructor
  · intro hfix
    obtain ⟨h, hh, heq⟩ := branchImage_factor N p hp hpN g g.property none
    exact ⟨h, hh, by simpa only [hfix] using heq⟩
  · rintro ⟨h, hh, heq⟩
    obtain ⟨a, ha, hea⟩ := branchImage_factor N p hp hpN g g.property none
    exact branch_eq_of_two_factorizations p hp _ none a h (hea.symm.trans heq)

end
end ImbalancedChen.Part3.ActualHeckeIntersectionSubgroup20261026b
