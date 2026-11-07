import ImbalancedChen.FiniteSieveEuler
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# The omitted center-prime correction

The strict-cap correction in `FiniteSieveEuler` omits the odd prime divisors
of `N` at or above the cap. Their distinct-prime product divides `N`.
Consequently, `N < z^(k+1)` bounds their number by `k`, and bounds their
correction product between one and `(1 + 1/(z-2))^k`.

For the exact natural ceiling of the real fifth root there are at most
five omitted primes. For `N >= 1024`, their product differs from one by
at most `62 / N^(1/5)`. The constant and threshold are explicit and uniform
in `N`. No prime-counting estimate or asymptotic premise is used.
All subtraction in correction factors is real subtraction.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The omitted odd center-primes, complementary to the strict-cap set. -/
def oddPrimeDivisorsTail (N z : ℕ) : Finset ℕ :=
  (oddPrimeDivisors N).filter (fun p : ℕ => z ≤ p)

/-- The actual omitted finite correction. -/
def centerPrimeTailCorrection (N z : ℕ) : ℝ :=
  ∏ p ∈ oddPrimeDivisorsTail N z, ((p : ℝ) - 1) / ((p : ℝ) - 2)

@[simp] theorem mem_oddPrimeDivisorsTail {N z p : ℕ} (hN : N ≠ 0) :
    p ∈ oddPrimeDivisorsTail N z ↔
      Nat.Prime p ∧ 2 < p ∧ p ∣ N ∧ z ≤ p := by
  simp only [oddPrimeDivisorsTail, Finset.mem_filter, mem_oddPrimeDivisors hN,
    and_assoc]

/-- Exact factorization of the full correction, including primes at the
endpoint in the tail rather than in the strict-cap correction. -/
theorem oddPrimeDivisor_product_eq_below_mul_tail
    {N z : ℕ} (hN : N ≠ 0) :
    (∏ p ∈ oddPrimeDivisors N, ((p : ℝ) - 1) / ((p : ℝ) - 2)) =
      (∏ p ∈ oddPrimeDivisorsBelowCap N z,
        ((p : ℝ) - 1) / ((p : ℝ) - 2)) * centerPrimeTailCorrection N z := by
  rw [oddPrimeDivisorsBelowCap_eq_filter hN]
  unfold centerPrimeTailCorrection oddPrimeDivisorsTail
  simpa only [not_lt] using
    (Finset.prod_filter_mul_prod_filter_not (oddPrimeDivisors N)
      (fun p : ℕ => p < z)
      (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2))).symm

/-- The tail consists of distinct prime factors, so their product divides
`N`; no multiplicity bound is assumed. -/
theorem oddPrimeDivisorsTail_prod_dvd (N z : ℕ) :
    (∏ p ∈ oddPrimeDivisorsTail N z, p) ∣ N := by
  have hsub : oddPrimeDivisorsTail N z ⊆ N.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
  exact (Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub).trans
    (Nat.prod_primeFactors_dvd N)

/-- The finite arithmetic bound underlying the count of omitted primes. -/
theorem pow_card_oddPrimeDivisorsTail_le {N z : ℕ} (hN : 0 < N) :
    z ^ (oddPrimeDivisorsTail N z).card ≤ N := by
  calc
    z ^ (oddPrimeDivisorsTail N z).card =
        ∏ _p ∈ oddPrimeDivisorsTail N z, z := (Finset.prod_const z).symm
    _ ≤ ∏ p ∈ oddPrimeDivisorsTail N z, p := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Nat.zero_le z
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
    _ ≤ N := Nat.le_of_dvd hN (oddPrimeDivisorsTail_prod_dvd N z)

/-- General uniform tail-cardinality bound. Only `1 ≤ z` is needed for
this counting statement; the correction estimates below require `2 < z`. -/
theorem oddPrimeDivisorsTail_card_le {N z k : ℕ}
    (hN : 0 < N) (hz : 1 ≤ z) (hpow : N < z ^ (k + 1)) :
    (oddPrimeDivisorsTail N z).card ≤ k := by
  by_contra hcard
  have hk : k + 1 ≤ (oddPrimeDivisorsTail N z).card := by omega
  have hle : z ^ (k + 1) ≤ N :=
    (pow_le_pow_right' hz hk).trans (pow_card_oddPrimeDivisorsTail_le hN)
  exact (not_lt_of_ge hle) hpow

/-- An odd-prime correction is at least one. -/
theorem one_le_centerPrimeFactor {p : ℕ} (hp : 2 < p) :
    (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 2)).mpr
  linarith

/-- Above the cap, each correction is bounded by the cap's correction. -/
theorem centerPrimeFactor_le_cap {p z : ℕ} (hz : 2 < z) (hp : z ≤ p) :
    ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ 1 + 1 / ((z : ℝ) - 2) := by
  have hzr : (2 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hpr : (z : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hzpos : (0 : ℝ) < (z : ℝ) - 2 := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have heq : ((p : ℝ) - 1) / ((p : ℝ) - 2) =
      1 + 1 / ((p : ℝ) - 2) := by
    apply (div_eq_iff hppos.ne').mpr
    field_simp [hppos.ne'] <;> ring
  rw [heq]
  exact add_le_add le_rfl (one_div_le_one_div_of_le hzpos (by linarith))

/-- The tail correction always lies above one, including the empty tail. -/
theorem one_le_centerPrimeTailCorrection (N z : ℕ) :
    1 ≤ centerPrimeTailCorrection N z := by
  apply Finset.one_le_prod
  intro p hp
  exact one_le_centerPrimeFactor
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2

/-- Finite correction bound with the actual number of tail primes. -/
theorem centerPrimeTailCorrection_le_pow_card {N z : ℕ} (hz : 2 < z) :
    centerPrimeTailCorrection N z ≤
      (1 + 1 / ((z : ℝ) - 2)) ^ (oddPrimeDivisorsTail N z).card := by
  unfold centerPrimeTailCorrection
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    exact le_trans zero_le_one (one_le_centerPrimeFactor
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2)
  · intro p hp
    exact centerPrimeFactor_le_cap hz (Finset.mem_filter.mp hp).2

/-- The requested uniform finite statement, with no hidden prime-count or
correction-product hypothesis. -/
theorem centerPrimeTailCorrection_bounds {N z k : ℕ}
    (hN : 0 < N) (hz : 2 < z) (hpow : N < z ^ (k + 1)) :
    (oddPrimeDivisorsTail N z).card ≤ k ∧
      1 ≤ centerPrimeTailCorrection N z ∧
      centerPrimeTailCorrection N z ≤ (1 + 1 / ((z : ℝ) - 2)) ^ k := by
  have hcard := oddPrimeDivisorsTail_card_le hN (by omega : 1 ≤ z) hpow
  have hzr : (2 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hbase : (1 : ℝ) ≤ 1 + 1 / ((z : ℝ) - 2) := by
    have := one_div_pos.mpr (show (0 : ℝ) < (z : ℝ) - 2 by linarith)
    linarith
  exact ⟨hcard, one_le_centerPrimeTailCorrection N z,
    (centerPrimeTailCorrection_le_pow_card hz).trans (pow_le_pow_right₀ hbase hcard)⟩

/-- An elementary uniform bound on a fixed power near one. -/
theorem one_add_pow_le_linear {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k ≤ 1 + ((2 : ℝ) ^ k - 1) * x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hcoeff : 0 ≤ (2 : ℝ) ^ k - 1 :=
        sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      have hxx : x * x ≤ x := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 hx0
      have herror := mul_nonneg hcoeff (sub_nonneg.mpr hxx)
      calc
        (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := pow_succ _ _
        _ ≤ (1 + ((2 : ℝ) ^ k - 1) * x) * (1 + x) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
        _ ≤ 1 + ((2 : ℝ) ^ (k + 1) - 1) * x := by
          rw [pow_succ]
          nlinarith [herror]

/-- With at most five omitted primes, the explicit error is at most `62/z`.
The threshold `4 ≤ z` keeps every denominator uniformly away from zero. -/
theorem centerPrimeTailCorrection_le_one_add_sixtyTwo_div {N z : ℕ}
    (hz : 4 ≤ z) (hcard : (oddPrimeDivisorsTail N z).card ≤ 5) :
    centerPrimeTailCorrection N z ≤ 1 + 62 / (z : ℝ) := by
  have hzr : (4 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  have hzsub : (0 : ℝ) < (z : ℝ) - 2 := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / ((z : ℝ) - 2) := (one_div_pos.mpr hzsub).le
  have hx1 : 1 / ((z : ℝ) - 2) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hzsub).mpr
    linarith
  have hbase : (1 : ℝ) ≤ 1 + 1 / ((z : ℝ) - 2) := by linarith
  have hrecip : 1 / ((z : ℝ) - 2) ≤ 2 / (z : ℝ) := by
    apply (div_le_div_iff₀ hzsub hzpos).mpr
    linarith
  calc
    centerPrimeTailCorrection N z ≤
        (1 + 1 / ((z : ℝ) - 2)) ^ (oddPrimeDivisorsTail N z).card :=
      centerPrimeTailCorrection_le_pow_card (by omega)
    _ ≤ (1 + 1 / ((z : ℝ) - 2)) ^ 5 := pow_le_pow_right₀ hbase hcard
    _ ≤ 1 + 31 * (1 / ((z : ℝ) - 2)) := by
      have hlinear := one_add_pow_le_linear hx0 hx1 5
      norm_num at hlinear
      simpa only [one_div] using hlinear
    _ ≤ 1 + 31 * (2 / (z : ℝ)) := by linarith
    _ = 1 + 62 / (z : ℝ) := by ring

/-- The ceiling never loses the fifth-power inequality. -/
theorem le_ceil_fifthRoot_pow_five (N : ℕ) :
    N ≤ (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) ^ 5 := by
  have hroot : ((N : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hle := pow_le_pow_left₀
    (Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 5 : ℝ))
    (Nat.le_ceil ((N : ℝ) ^ (1 / 5 : ℝ))) 5
  rw [hroot] at hle
  exact_mod_cast hle

/-- A positive center larger than one is strictly below the sixth power
of its actual cap, even if its real fifth root is exactly an integer. -/
theorem lt_ceil_fifthRoot_pow_six {N : ℕ} (hN : 1 < N) :
    N < (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) ^ 6 := by
  let z : ℕ := Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))
  have hle : N ≤ z ^ 5 := le_ceil_fifthRoot_pow_five N
  have hz : 1 < z := by
    by_contra h
    have hzle : z ≤ 1 := by omega
    have hp : z ^ 5 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left' hzle 5
    exact (Nat.not_le_of_lt hN) (hle.trans hp)
  have hp : 0 < z ^ 5 := pow_pos (by omega) 5
  have hstrict : z ^ 5 < z ^ 6 := by
    calc
      z ^ 5 = z ^ 5 * 1 := (mul_one _).symm
      _ < z ^ 5 * z := mul_lt_mul_of_pos_left hz hp
      _ = z ^ 6 := (pow_succ z 5).symm
  exact hle.trans_lt hstrict

/-- At most five omitted odd prime divisors for the manuscript's exact
real fifth-root cutoff. -/
theorem oddPrimeDivisorsTail_actual_cap_card_le_five {N : ℕ} (hN : 0 < N) :
    (oddPrimeDivisorsTail N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)))).card ≤ 5 := by
  by_cases hN1 : N = 1
  · subst N
    simp [oddPrimeDivisorsTail, oddPrimeDivisors]
  · have hNgt : 1 < N := by omega
    have hrootpos : 0 < (N : ℝ) ^ (1 / 5 : ℝ) :=
      Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
    have hz : 1 ≤ Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) :=
      Nat.one_le_ceil_iff.mpr hrootpos
    exact oddPrimeDivisorsTail_card_le hN hz (lt_ceil_fifthRoot_pow_six hNgt)

/-- Literal real-cutoff membership, with equality in the omitted tail. -/
theorem mem_oddPrimeDivisorsTail_actual_cap_iff {N p : ℕ} (hN : N ≠ 0) :
    p ∈ oddPrimeDivisorsTail N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) ↔
      Nat.Prime p ∧ 2 < p ∧ p ∣ N ∧ (N : ℝ) ^ (1 / 5 : ℝ) ≤ (p : ℝ) := by
  rw [mem_oddPrimeDivisorsTail hN, Nat.ceil_le]

/-- An explicit uniform error bound for the actual omitted correction.
This is the quantitative content of `1 + O(N^(-1/5))`, with constant 62
and threshold 1024, independent of the arithmetic structure of `N`. -/
theorem centerPrimeTailCorrection_actual_cap_abs_sub_one_le
    {N : ℕ} (hN : 1024 ≤ N) :
    |centerPrimeTailCorrection N (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))) - 1| ≤
      62 / ((N : ℝ) ^ (1 / 5 : ℝ)) := by
  let z : ℕ := Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ))
  have hNpos : 0 < N := by omega
  have hz : 4 ≤ z := by
    by_contra h
    have hzle : z ≤ 3 := by omega
    have hp := pow_le_pow_left' hzle 5
    have hle : N ≤ z ^ 5 := le_ceil_fifthRoot_pow_five N
    norm_num at hp
    omega
  have hcard : (oddPrimeDivisorsTail N z).card ≤ 5 :=
    oddPrimeDivisorsTail_actual_cap_card_le_five hNpos
  have hupper := centerPrimeTailCorrection_le_one_add_sixtyTwo_div hz hcard
  have hlower := one_le_centerPrimeTailCorrection N z
  have hrootpos : 0 < (N : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hNpos) _
  have hceil : (N : ℝ) ^ (1 / 5 : ℝ) ≤ (z : ℝ) := Nat.le_ceil _
  have hrecip : (62 : ℝ) / (z : ℝ) ≤ 62 / ((N : ℝ) ^ (1 / 5 : ℝ)) :=
    div_le_div_of_nonneg_left (by norm_num) hrootpos hceil
  change |centerPrimeTailCorrection N z - 1| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

end

end ImbalancedChen
