import ImbalancedChen.Part3RoughAuxiliarySW
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Data.Nat.GCD.BigOperators

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual rough slots use z<p, so their forbidden finite primes are p<=z.
Changing the character level by their genuine prime product gives exactly
the original rough coefficient, including principal characters and primes
dividing the original character level. No SW or zero-free input is used.
-/

namespace ImbalancedChen.Part3.RoughSlotCharacterLift20261026b
noncomputable section
open Classical Finset
open scoped BigOperators

def smallPrimes (z : ℝ) : Finset ℕ :=
  (Finset.range (Nat.floor z+1)).filter Nat.Prime
def smallProduct (z : ℝ) : ℕ := ∏ p ∈ smallPrimes z, p

theorem smallPrimes_prime {z : ℝ} {p : ℕ} (hp : p ∈ smallPrimes z) : Nat.Prime p :=
  (Finset.mem_filter.mp hp).2

theorem mem_smallPrimes {z : ℝ} (hz : 0 ≤ z) {p : ℕ} :
    p ∈ smallPrimes z ↔ Nat.Prime p ∧ (p : ℝ) ≤ z := by
  simp only [smallPrimes,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff,
    Nat.le_floor_iff hz]
  tauto

theorem smallProduct_ne_zero (z : ℝ) : smallProduct z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (smallPrimes_prime hp).ne_zero

theorem smallProduct_primeFactors (z : ℝ) :
    (smallProduct z).primeFactors = smallPrimes z :=
  Nat.primeFactors_prod (fun p hp => smallPrimes_prime hp)

/-- The strict actual rough inequality is equivalent to coprimality with
the finite product including a prime exactly at the cutoff. -/
theorem rough_predicate_iff_coprime {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    (∀ p : ℕ, p.Prime → p ∣ n → z < (p : ℝ)) ↔ n.Coprime (smallProduct z) := by
  rw [smallProduct,Nat.coprime_prod_right_iff]
  constructor
  · intro h p hp
    have hprime := smallPrimes_prime hp
    apply Nat.Coprime.symm
    apply hprime.coprime_iff_not_dvd.mpr
    intro hpn
    exact (not_lt_of_ge ((mem_smallPrimes hz).mp hp).2) (h p hprime hpn)
  · intro h p hp hpn
    by_contra hnot
    have hmem : p ∈ smallPrimes z := (mem_smallPrimes hz).mpr ⟨hp,le_of_not_gt hnot⟩
    exact (hp.coprime_iff_not_dvd.mp (h p hmem).symm) hpn

theorem roughOneSlot_eq_coprime_indicator {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    roughOneSlot z n = if n.Coprime (smallProduct z) then (1 : ℂ) else 0 := by
  simp only [roughOneSlot,rough_predicate_iff_coprime hz]

def roughCharacter {q : ℕ} (chi : DirichletCharacter ℂ q) (z : ℝ) :
    DirichletCharacter ℂ (q*smallProduct z) :=
  DirichletCharacter.changeLevel (dvd_mul_right q (smallProduct z)) chi

/-- Exact coefficient equality, without deleting principal characters or
assuming the argument coprime to either level. -/
theorem roughCharacter_apply {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    roughCharacter chi z n = chi n*roughOneSlot z n := by
  have hlevel : q ∣ q*smallProduct z := dvd_mul_right q _
  rw [roughOneSlot_eq_coprime_indicator hz]
  by_cases hn : n.Coprime (q*smallProduct z)
  · have hnP := (Nat.coprime_mul_iff_right.mp hn).2
    rw [if_pos hnP,mul_one]
    have hu : IsUnit (n : ZMod (q*smallProduct z)) :=
      (ZMod.isUnit_iff_coprime n _).mpr hn
    have he := DirichletCharacter.changeLevel_eq_cast_of_dvd chi hlevel hu.unit
    simpa only [hu.unit_spec,ZMod.cast_natCast hlevel,roughCharacter] using he
  · have hnu : ¬IsUnit (n : ZMod (q*smallProduct z)) :=
      fun hu => hn ((ZMod.isUnit_iff_coprime n _).mp hu)
    have hzchi : roughCharacter chi z n = 0 := MulChar.map_nonunit _ hnu
    rw [hzchi]
    by_cases hnP : n.Coprime (smallProduct z)
    · have hnq : ¬n.Coprime q := fun h => hn (h.mul_right hnP)
      have hzero : chi n = 0 := MulChar.map_nonunit _
        (fun hu => hnq ((ZMod.isUnit_iff_coprime n q).mp hu))
      simp only [hnP,if_true,hzero,zero_mul]
    · simp only [hnP,if_false,mul_zero]

theorem roughMoebius_twist_eq {q : ℕ} (chi : DirichletCharacter ℂ q)
    {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    chi n*roughMoebiusSlot z n =
      roughCharacter chi z n*((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
  rw [roughCharacter_apply chi hz,roughMoebiusSlot]
  ring

/-- Both literal rough twists converge absolutely in the required half
plane. The proof is coefficient domination, not an Euler identity input. -/
theorem rough_twists_LSeriesSummable {q : ℕ} (chi : DirichletCharacter ℂ q)
    (z : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => chi n*roughOneSlot z n) s ∧
      LSeriesSummable (fun n => chi n*roughMoebiusSlot z n) s := by
  constructor
  · apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    rw [norm_mul]
    exact (mul_le_mul (chi.norm_le_one n) (roughOneSlot_norm_le z n)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    rw [norm_mul]
    exact (mul_le_mul (chi.norm_le_one n) (roughMoebiusSlot_norm_le z n)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

end
end ImbalancedChen.Part3.RoughSlotCharacterLift20261026b
