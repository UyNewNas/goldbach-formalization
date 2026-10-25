import ImbalancedChen.Part3LevelPrimitiveComplexEisenstein
import Mathlib.RingTheory.Int.Basic

/-! Actual primitive-row bijections for prime degeneracy. No sum identity is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED. -/

noncomputable section
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a

namespace ImbalancedChen.Part3.PrimeLevelRowDegeneracy20261025a

abbrev GoodRows (p M : ℕ) := {v : LevelPrimitiveRow M // ¬ (p : ℤ) ∣ v.1 1}
abbrev BadRows (p M : ℕ) := {v : LevelPrimitiveRow M // (p : ℤ) ∣ v.1 1}
abbrev ExcludedRows (p M : ℕ) := {v : LevelPrimitiveRow M // ¬ (p : ℤ) ∣ v.1 0}
abbrev IncludedRows (p M : ℕ) := {v : LevelPrimitiveRow M // (p : ℤ) ∣ v.1 0}

theorem prime_int {p : ℕ} (hp : p.Prime) : Prime (p : ℤ) :=
  Int.prime_iff_natAbs_prime.mpr (by simpa using hp)

theorem prime_coprime_of_not_dvd {p : ℕ} (hp : p.Prime) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) :
    IsCoprime (p : ℤ) d :=
  ((prime_int hp).irreducible.isCoprime_or_dvd d).resolve_right hd

theorem primitive_not_both {p : ℕ} (hp : p.Prime) {c d : ℤ}
    (h : IsCoprime c d) (hc : (p : ℤ) ∣ c) : ¬ (p : ℤ) ∣ d := by
  intro hd
  exact (prime_int hp).not_unit (h.isUnit_of_dvd' hc hd)

/-- Multiply the first coordinate; p does not divide the second coordinate. -/
def raiseFirst {p : ℕ} (hp : p.Prime) (M : ℕ) (v : GoodRows p M) :
    LevelPrimitiveRow (p * M) :=
  ⟨![(p : ℤ) * v.1.1 0, v.1.1 1], by
    constructor
    · exact (prime_coprime_of_not_dvd hp v.property).mul_left v.1.property.1
    · simpa only [Nat.cast_mul] using mul_dvd_mul_left (p : ℤ) v.1.property.2⟩

theorem raiseFirst_injective {p : ℕ} (hp : p.Prime) (M : ℕ) :
    Function.Injective (raiseFirst hp M) := by
  intro v w h
  have h₀ := congrArg (fun u : LevelPrimitiveRow (p * M) => u.1 0) h
  have h₁ := congrArg (fun u : LevelPrimitiveRow (p * M) => u.1 1) h
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  apply Subtype.ext
  apply Subtype.ext
  funext i
  fin_cases i
  · exact (mul_left_cancel₀ hp0) h₀
  · exact h₁

theorem raiseFirst_surjective {p : ℕ} (hp : p.Prime) (M : ℕ) :
    Function.Surjective (raiseFirst hp M) := by
  intro v
  obtain ⟨k, hk⟩ := v.property.2
  have hc : v.1 0 = (p : ℤ) * ((M : ℤ) * k) := by
    simpa only [Nat.cast_mul, mul_assoc] using hk
  have hcop : IsCoprime ((M : ℤ) * k) (v.1 1) := by
    have h := v.property.1
    rw [hc] at h
    exact h.of_mul_left_right
  let w : LevelPrimitiveRow M := ⟨![(M : ℤ) * k, v.1 1], hcop, dvd_mul_right _ _⟩
  have hgood : ¬ (p : ℤ) ∣ v.1 1 :=
    primitive_not_both hp v.property.1 ⟨(M : ℤ) * k, hc⟩
  refine ⟨⟨w, hgood⟩, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [raiseFirst, w, hc]

def goodRowsEquiv {p : ℕ} (hp : p.Prime) (M : ℕ) : GoodRows p M ≃ LevelPrimitiveRow (p * M) :=
  Equiv.ofBijective (raiseFirst hp M) ⟨raiseFirst_injective hp M, raiseFirst_surjective hp M⟩

/-- Multiply the second coordinate; p does not divide the first coordinate. -/
def raiseSecond {p : ℕ} (hp : p.Prime) (M : ℕ) (v : ExcludedRows p M) : BadRows p M :=
  ⟨⟨![v.1.1 0, (p : ℤ) * v.1.1 1], by
    constructor
    · exact (prime_coprime_of_not_dvd hp v.property).symm.mul_right v.1.property.1
    · exact v.1.property.2⟩, dvd_mul_right _ _⟩

theorem raiseSecond_injective {p : ℕ} (hp : p.Prime) (M : ℕ) :
    Function.Injective (raiseSecond hp M) := by
  intro v w h
  have h₀ := congrArg (fun u : BadRows p M => u.1.1 0) h
  have h₁ := congrArg (fun u : BadRows p M => u.1.1 1) h
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  apply Subtype.ext
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h₀
  · exact (mul_left_cancel₀ hp0) h₁

theorem raiseSecond_surjective {p : ℕ} (hp : p.Prime) (M : ℕ) :
    Function.Surjective (raiseSecond hp M) := by
  intro v
  obtain ⟨k, hk⟩ := v.property
  have hcop : IsCoprime (v.1.1 0) k := by
    have h := v.1.property.1
    rw [hk] at h
    exact h.of_mul_right_right
  let w : LevelPrimitiveRow M := ⟨![v.1.1 0, k], hcop, v.1.property.2⟩
  have hgood : ¬ (p : ℤ) ∣ v.1.1 0 :=
    primitive_not_both hp v.1.property.1.symm v.property
  refine ⟨⟨w, hgood⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [raiseSecond, w, hk]

def badRowsEquiv {p : ℕ} (hp : p.Prime) (M : ℕ) : ExcludedRows p M ≃ BadRows p M :=
  Equiv.ofBijective (raiseSecond hp M) ⟨raiseSecond_injective hp M, raiseSecond_surjective hp M⟩

/-- At a prime not already in the level, the two simultaneous divisibility
conditions are exactly divisibility by the new level. -/
def includedRowsEquiv {p : ℕ} (hp : p.Prime) (M : ℕ) (hpM : ¬ p ∣ M) :
    IncludedRows p M ≃ LevelPrimitiveRow (p * M) where
  toFun v := ⟨v.1.1, v.1.property.1, by
    have hnot : ¬ (p : ℤ) ∣ (M : ℤ) := by exact_mod_cast hpM
    simpa only [Nat.cast_mul] using
      (prime_coprime_of_not_dvd hp hnot).mul_dvd v.property v.1.property.2⟩
  invFun v := ⟨⟨v.1, v.property.1, by
    have h : (p : ℤ) * (M : ℤ) ∣ v.1 0 := by simpa using v.property.2
    exact dvd_trans (dvd_mul_left _ _) h⟩, by
      have h : (p : ℤ) * (M : ℤ) ∣ v.1 0 := by simpa using v.property.2
      exact dvd_trans (dvd_mul_right _ _) h⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem excludedRows_empty_of_dvd {p M : ℕ} (hpM : p ∣ M) (v : ExcludedRows p M) : False := by
  apply v.property
  exact dvd_trans (by exact_mod_cast hpM) v.1.property.2

end ImbalancedChen.Part3.PrimeLevelRowDegeneracy20261025a
