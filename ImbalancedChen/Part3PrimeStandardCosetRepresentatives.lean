import ImbalancedChen.Part3ActualPrimeHeckeRightFactor
import ImbalancedChen.Part3Gamma0FiniteMeasureCarrier

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Literal standard LEFT Gamma0(p) representatives I and S*T^r, indexed by
the existing Branch p = Option (ZMod p). Since the existing gamma0Classes
are G/Gamma0(p), their quotient labels are the INVERSES of these matrices.
The actual congruence entry test and the existing prime residue-quotient
primitive prove surjectivity. Displayed relative lower-left entries prove
separation. Thus p+1 is derived by a true quotient bijection; no prime
cusp classification, index formula or coset decomposition is an input.
-/

noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.ActualPrimeHeckeBranchSeparation20261026b
open ImbalancedChen.Part3.ActualPrimeHeckeRightFactor20261026b
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z

namespace ImbalancedChen.Part3.PrimeStandardCosets20261026b

def standardRepresentative (p : ℕ) : Branch p → SL(2, ℤ)
  | none => 1
  | some r => ModularGroup.S * ModularGroup.T ^ (r.val : ℤ)

theorem standardRepresentative_some_matrix (p : ℕ) (r : ZMod p) :
    (standardRepresentative p (some r) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![0, -1; 1, (r.val : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [standardRepresentative, Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.coe_S, ModularGroup.coe_T_zpow, Matrix.mul_fin_two]

theorem standard_relative_lower_left (p : ℕ) (j k : Branch p) :
    (standardRepresentative p j * (standardRepresentative p k)⁻¹) 1 0 =
      match j, k with
      | none, none => 0
      | none, some _ => -1
      | some _, none => 1
      | some r, some t => (t.val : ℤ) - (r.val : ℤ) := by
  cases j <;> cases k <;>
    simp [standardRepresentative, Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.coe_S, ModularGroup.coe_T_zpow, Matrix.mul_fin_two, SL2_inv_expl] <;> ring

/-- Genuine prime-mod-p completion of every original matrix into one of
the displayed left cosets, retaining the exact relative matrix. -/
theorem exists_standard_relative (p : ℕ) (hp : p.Prime) (g : SL(2, ℤ)) :
    ∃ j : Branch p, g * (standardRepresentative p j)⁻¹ ∈ CongruenceSubgroup.Gamma0 p := by
  by_cases hc : (p : ℤ) ∣ g 1 0
  · refine ⟨none, ?_⟩
    simpa only [standardRepresentative, inv_one, mul_one] using
      (gamma0_mem_iff_level_dvd_c p g).mpr hc
  · obtain ⟨r, hr⟩ := prime_residue_quotient p hp (g 1 0) (g 1 1) hc
    refine ⟨some r, (gamma0_mem_iff_level_dvd_c p _).mpr ?_⟩
    have hentry : (g * (standardRepresentative p (some r))⁻¹) 1 0 =
        g 1 0 * (r.val : ℤ) - g 1 1 := by
      simp [standardRepresentative, Matrix.SpecialLinearGroup.coe_mul,
        ModularGroup.coe_S, ModularGroup.coe_T_zpow, Matrix.mul_fin_two, SL2_inv_expl]
      <;> ring
    rw [hentry]
    simpa only [neg_sub] using dvd_neg.mpr hr

/-- The inverse orientation is essential: these are labels in G/Gamma0,
whose inverse representatives act on the standard modular cell. -/
def standardClass (p : ℕ) (j : Branch p) : gamma0Classes p :=
  QuotientGroup.mk ((standardRepresentative p j)⁻¹)

theorem standardClass_injective (p : ℕ) (hp : p.Prime) :
    Function.Injective (standardClass p) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro j k h
  have hmem : standardRepresentative p j * (standardRepresentative p k)⁻¹ ∈
      CongruenceSubgroup.Gamma0 p := by
    simpa only [standardClass, inv_inv] using QuotientGroup.eq.mp h
  have hd := (gamma0_mem_iff_level_dvd_c p _).mp hmem
  rw [standard_relative_lower_left] at hd
  cases j with
  | none =>
    cases k with
    | none => rfl
    | some t =>
      have hp1 : (p : ℤ) ∣ 1 := by simpa using hd
      exact (hp.not_dvd_one (Int.natCast_dvd_natCast.mp hp1)).elim
  | some r =>
    cases k with
    | none =>
      have hp1 : (p : ℤ) ∣ 1 := hd
      exact (hp.not_dvd_one (Int.natCast_dvd_natCast.mp hp1)).elim
    | some t =>
      have hz : (((t.val : ℤ) - (r.val : ℤ) : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
      simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] at hz
      exact congrArg some (sub_eq_zero.mp hz).symm

theorem standardClass_surjective (p : ℕ) (hp : p.Prime) :
    Function.Surjective (standardClass p) := by
  intro q
  obtain ⟨j, hj⟩ := exists_standard_relative p hp (Quotient.out q)⁻¹
  refine ⟨j, ?_⟩
  unfold standardClass
  rw [← Quotient.out_eq' q]
  apply QuotientGroup.eq.mpr
  have hi := (CongruenceSubgroup.Gamma0 p).inv_mem hj
  simpa only [mul_inv_rev, inv_inv] using hi

/-- An explicit p+1 family, proved bijective to the ORIGINAL actual class
space. This is not a cusp set or an abstract supplied quotient dictionary. -/
def standardClassEquiv (p : ℕ) (hp : p.Prime) : Branch p ≃ gamma0Classes p :=
  Equiv.ofBijective (standardClass p) ⟨standardClass_injective p hp, standardClass_surjective p hp⟩

theorem prime_actual_coset_card (p : ℕ) (hp : p.Prime) : Nat.card (gamma0Classes p) = p + 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  calc
    _ = Nat.card (Branch p) := (Nat.card_congr (standardClassEquiv p hp)).symm
    _ = p + 1 := by rw [Nat.card_eq_fintype_card]; exact branch_card p

end ImbalancedChen.Part3.PrimeStandardCosets20261026b
