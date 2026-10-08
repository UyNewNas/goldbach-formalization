import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Large-prime-square exceptions, with no floor-loss term

This file counts actual positive integers `1 ≤ n ≤ N` divisible by `p^2`
for at least one prime `p ≥ z`. Each integer is counted once, regardless
of how many such primes or higher powers divide it. The real lower
endpoint is inclusive. The exact finite prime carrier uses `ceil z`.

The proof is elementary and finite: positive multiples of `d` inject into
`Icc 1 (N / d)`, union cardinality is at most the sum of its fibre counts,
and the integer reciprocal-square tail telescopes. There is no additive
one per prime, no square-root floor loss, and no analytic estimate among
the hypotheses. The resulting literal bound is `N / (z - 1)` for `z > 1`.
Zero is deliberately excluded: every square divides zero.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Positive multiples of `d`, retaining the inclusive endpoint `N`. -/
def positiveMultiplesUpTo (N d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => d ∣ n)

@[simp] theorem mem_positiveMultiplesUpTo {N d n : ℕ} :
    n ∈ positiveMultiplesUpTo N d ↔ 1 ≤ n ∧ n ≤ N ∧ d ∣ n := by
  simp only [positiveMultiplesUpTo, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- The quotient map excludes the zero quotient, so there is no `+1`. -/
theorem positiveMultiplesUpTo_card_le_div (N : ℕ) {d : ℕ} (hd : 0 < d) :
    (positiveMultiplesUpTo N d).card ≤ N / d := by
  calc
    (positiveMultiplesUpTo N d).card ≤ (Finset.Icc 1 (N / d)).card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => n / d)
      · intro n hn
        obtain ⟨hn1, hnN, hdvd⟩ := mem_positiveMultiplesUpTo.mp hn
        apply Finset.mem_Icc.mpr
        refine ⟨?_, Nat.div_le_div_right hnN⟩
        apply (Nat.le_div_iff_mul_le hd).mpr
        simpa only [one_mul] using Nat.le_of_dvd (by omega : 0 < n) hdvd
      · intro a ha b hb hab
        have haD := (mem_positiveMultiplesUpTo.mp ha).2.2
        have hbD := (mem_positiveMultiplesUpTo.mp hb).2.2
        change a / d = b / d at hab
        calc
          a = (a / d) * d := (Nat.div_mul_cancel haD).symm
          _ = (b / d) * d := by rw [hab]
          _ = b := Nat.div_mul_cancel hbD
    _ = N / d := by simp

/-- Passing to real division loses no rounding term. -/
theorem positiveMultiplesUpTo_card_cast_le (N : ℕ) {d : ℕ} (hd : 0 < d) :
    ((positiveMultiplesUpTo N d).card : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
  have hmul : (positiveMultiplesUpTo N d).card * d ≤ N :=
    (Nat.mul_le_mul_right d (positiveMultiplesUpTo_card_le_div N hd)).trans
      (Nat.div_mul_le_self N d)
  apply (le_div_iff₀ (Nat.cast_pos.mpr hd : (0 : ℝ) < (d : ℝ))).mpr
  exact_mod_cast hmul

/-- A finite shifted reciprocal-square tail, including its final endpoint. -/
theorem reciprocalSquare_shifted_tail_le (m k : ℕ) (hm : 0 < m) :
    (∑ p ∈ Finset.Icc (m + 1) (m + k), 1 / (p : ℝ) ^ 2) ≤
      1 / (m : ℝ) - 1 / ((m + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega)]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] at ih ⊢
      have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
      have hx : (0 : ℝ) < (m : ℝ) + (k : ℝ) := by positivity
      have hx1 : (0 : ℝ) < (m : ℝ) + (k : ℝ) + 1 := by positivity
      have hcomp : 1 / ((m : ℝ) + (k : ℝ) + 1) ^ 2 ≤
          1 / (((m : ℝ) + (k : ℝ)) * ((m : ℝ) + (k : ℝ) + 1)) := by
        apply (div_le_div_iff₀ (pow_pos hx1 2) (mul_pos hx hx1)).mpr
        nlinarith
      have htel : 1 / (((m : ℝ) + (k : ℝ)) * ((m : ℝ) + (k : ℝ) + 1)) =
          1 / ((m : ℝ) + (k : ℝ)) - 1 / ((m : ℝ) + (k : ℝ) + 1) := by
        field_simp [hx.ne', hx1.ne']
        <;> ring
      rw [htel] at hcomp
      linarith

/-- The elementary integer-tail estimate, valid for every finite upper cap. -/
theorem reciprocalSquare_Icc_tail_le (N : ℕ) {L : ℕ} (hL : 2 ≤ L) :
    (∑ p ∈ Finset.Icc L N, 1 / (p : ℝ) ^ 2) ≤ 1 / ((L : ℝ) - 1) := by
  by_cases hLN : L ≤ N
  · have h := reciprocalSquare_shifted_tail_le (L - 1) (N - (L - 1)) (by omega)
    have hlo : L - 1 + 1 = L := by omega
    have hhi : L - 1 + (N - (L - 1)) = N := by omega
    rw [hlo, hhi, Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one] at h
    exact h.trans (sub_le_self _ (by positivity))
  · rw [Finset.Icc_eq_empty_of_lt (by omega : N < L), Finset.sum_empty]
    have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    exact one_div_nonneg.mpr (by linarith)

/-- Exact finite prime carrier at a natural inclusive lower cutoff. -/
def roughSquarePrimeCarrier (N L : ℕ) : Finset ℕ :=
  (Finset.Icc L N).filter Nat.Prime

/-- Actual exceptional integers at a natural inclusive lower cutoff. -/
def roughSquareExceptionsNat (N L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter
    (fun n => ∃ p : ℕ, Nat.Prime p ∧ L ≤ p ∧ p ^ 2 ∣ n)

@[simp] theorem mem_roughSquareExceptionsNat {N L n : ℕ} :
    n ∈ roughSquareExceptionsNat N L ↔
      1 ≤ n ∧ n ≤ N ∧ ∃ p : ℕ, Nat.Prime p ∧ L ≤ p ∧ p ^ 2 ∣ n := by
  classical
  simp only [roughSquareExceptionsNat, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- This is equality with a finite union, not a multiplicity-weighted definition. -/
theorem roughSquareExceptionsNat_eq_biUnion (N L : ℕ) :
    roughSquareExceptionsNat N L =
      (roughSquarePrimeCarrier N L).biUnion (fun p => positiveMultiplesUpTo N (p ^ 2)) := by
  classical
  ext n
  rw [mem_roughSquareExceptionsNat, Finset.mem_biUnion]
  constructor
  · rintro ⟨hn1, hnN, p, hp, hLp, hdvd⟩
    have hsq : p ^ 2 ≤ n := Nat.le_of_dvd (by omega : 0 < n) hdvd
    have hpSq : p ≤ p ^ 2 := by
      calc
        p = p * 1 := (mul_one p).symm
        _ ≤ p * p := Nat.mul_le_mul_left p hp.one_lt.le
        _ = p ^ 2 := (pow_two p).symm
    have hpN : p ≤ N := hpSq.trans (hsq.trans hnN)
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hLp, hpN⟩, hp⟩, ?_⟩
    exact mem_positiveMultiplesUpTo.mpr ⟨hn1, hnN, hdvd⟩
  · rintro ⟨p, hp, hn⟩
    obtain ⟨hpI, hpprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn1, hnN, hdvd⟩ := mem_positiveMultiplesUpTo.mp hn
    exact ⟨hn1, hnN, p, hpprime, (Finset.mem_Icc.mp hpI).1, hdvd⟩

/-- Union counting followed by exact divisibility counting. -/
theorem roughSquareExceptionsNat_card_le_prime_sum (N L : ℕ) :
    ((roughSquareExceptionsNat N L).card : ℝ) ≤
      (N : ℝ) * ∑ p ∈ roughSquarePrimeCarrier N L, 1 / (p : ℝ) ^ 2 := by
  classical
  have hcard : (roughSquareExceptionsNat N L).card ≤
      ∑ p ∈ roughSquarePrimeCarrier N L, (positiveMultiplesUpTo N (p ^ 2)).card := by
    rw [roughSquareExceptionsNat_eq_biUnion]
    exact Finset.card_biUnion_le
  calc
    ((roughSquareExceptionsNat N L).card : ℝ) ≤
        ∑ p ∈ roughSquarePrimeCarrier N L,
          ((positiveMultiplesUpTo N (p ^ 2)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ p ∈ roughSquarePrimeCarrier N L, (N : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := (Finset.mem_filter.mp hp).2
      simpa only [Nat.cast_pow] using
        positiveMultiplesUpTo_card_cast_le N (pow_pos hpprime.pos 2)
    _ = (N : ℝ) * ∑ p ∈ roughSquarePrimeCarrier N L, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- Owned finite exception bound at any natural lower cutoff `L ≥ 2`. -/
theorem roughSquareExceptionsNat_card_le (N : ℕ) {L : ℕ} (hL : 2 ≤ L) :
    ((roughSquareExceptionsNat N L).card : ℝ) ≤ (N : ℝ) / ((L : ℝ) - 1) := by
  have hsum : (∑ p ∈ roughSquarePrimeCarrier N L, 1 / (p : ℝ) ^ 2) ≤
      ∑ p ∈ Finset.Icc L N, 1 / (p : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p _ _
    positivity
  calc
    ((roughSquareExceptionsNat N L).card : ℝ) ≤
        (N : ℝ) * ∑ p ∈ roughSquarePrimeCarrier N L, 1 / (p : ℝ) ^ 2 :=
      roughSquareExceptionsNat_card_le_prime_sum N L
    _ ≤ (N : ℝ) * (1 / ((L : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (reciprocalSquare_Icc_tail_le N hL))
        (Nat.cast_nonneg N)
    _ = (N : ℝ) / ((L : ℝ) - 1) := by ring

/-- Actual exceptional integers at the manuscript's real inclusive cutoff. -/
def roughSquareExceptions (N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter
    (fun n => ∃ p : ℕ, Nat.Prime p ∧ z ≤ (p : ℝ) ∧ p ^ 2 ∣ n)

@[simp] theorem mem_roughSquareExceptions {N n : ℕ} {z : ℝ} :
    n ∈ roughSquareExceptions N z ↔
      1 ≤ n ∧ n ≤ N ∧ ∃ p : ℕ, Nat.Prime p ∧ z ≤ (p : ℝ) ∧ p ^ 2 ∣ n := by
  classical
  simp only [roughSquareExceptions, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- The ceiling preserves equality at the real cutoff. -/
theorem roughSquareExceptions_eq_nat_ceil (N : ℕ) (z : ℝ) :
    roughSquareExceptions N z = roughSquareExceptionsNat N (Nat.ceil z) := by
  ext n
  simp only [mem_roughSquareExceptions, mem_roughSquareExceptionsNat, Nat.ceil_le]

/-- Literal finite form of the manuscript's large-prime-square error estimate.
No squarefreeness or bound on the number of prime factors is assumed. -/
theorem roughSquareExceptions_card_le (N : ℕ) {z : ℝ} (hz : 1 < z) :
    ((roughSquareExceptions N z).card : ℝ) ≤ (N : ℝ) / (z - 1) := by
  have hceil : 2 ≤ Nat.ceil z := by
    exact Nat.add_one_le_ceil_iff.mpr (by simpa using hz)
  rw [roughSquareExceptions_eq_nat_ceil]
  exact (roughSquareExceptionsNat_card_le N hceil).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by linarith)
      (sub_le_sub_right (Nat.le_ceil z) 1))

/-- For a cutoff at least two the same count is at most `2 N / z`. -/
theorem roughSquareExceptions_card_le_two_mul_div (N : ℕ) {z : ℝ} (hz : 2 ≤ z) :
    ((roughSquareExceptions N z).card : ℝ) ≤ 2 * (N : ℝ) / z := by
  have hrecip : 1 / (z - 1) ≤ 2 / z := by
    apply (div_le_div_iff₀ (by linarith : 0 < z - 1) (by linarith : 0 < z)).mpr
    linarith
  calc
    ((roughSquareExceptions N z).card : ℝ) ≤ (N : ℝ) / (z - 1) :=
      roughSquareExceptions_card_le N (by linarith)
    _ = (N : ℝ) * (1 / (z - 1)) := by ring
    _ ≤ (N : ℝ) * (2 / z) := mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg N)
    _ = 2 * (N : ℝ) / z := by ring

end

end ImbalancedChen
