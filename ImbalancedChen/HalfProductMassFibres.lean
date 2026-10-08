import ImbalancedChen.HalfProductSource
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.PrimeCounting

/-!
# Exact prime-counting fibres of the actual half-product mass

The existing ordered-factor uniqueness theorem counts every half-product
once, including prime squares. Projecting onto the smaller prime gives an
exact sum over primes at most `Nat.sqrt N`. The upper endpoint in its
second coordinate is

`min (N / r) (Nat.ceil ((r : ℝ) ^ ((den : ℝ) / num)) - 1)`.

The ceiling-minus-one retains the strict power boundary, even when the
real boundary is an integer. Natural subtraction of prime counts handles
empty intervals. When `0 < num < den`, every outer prime has a nonempty
interval containing its square, so the formula also holds with ordinary
real subtraction. The original real lower cutoff discards at most
`Nat.ceil T` distinct integers, with no analytic hypothesis.

This is a finite bridge for a future mass asymptotic. It does not assume
or prove a prime-counting asymptotic or replace the actual source by an
abstract mass parameter.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The second-prime fibre before converting its strict-power endpoint. -/
def halfProductPrimeFibre (num den N r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc r (N / r)).filter fun q =>
    Nat.Prime q ∧ q ^ num < r ^ den

@[simp] theorem mem_halfProductPrimeFibre {num den N r q : ℕ} :
    q ∈ halfProductPrimeFibre num den N r ↔
      r ≤ q ∧ q ≤ N / r ∧ Nat.Prime q ∧ q ^ num < r ^ den := by
  classical
  simp only [halfProductPrimeFibre, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- A pair in the original ordered source has a smaller prime at most √N. -/
theorem halfProductPairs_fst_mem_primesLE_sqrt {num den N : ℕ} {T : ℝ}
    {a : ℕ × ℕ} (ha : a ∈ halfProductPairs num den N T) :
    a.1 ∈ Nat.primesLE (Nat.sqrt N) := by
  rcases a with ⟨r, q⟩
  obtain ⟨hr, _, hrq, _, _, hN⟩ := mem_halfProductPairs.mp ha
  exact Nat.mem_primesLE.mpr
    ⟨Nat.le_sqrt.mpr ((Nat.mul_le_mul_left r hrq).trans hN), hr⟩

/-- Projection onto the second coordinate is a bijection within a fixed
first-prime fibre. The lower endpoint is closed and includes `q = r`. -/
theorem halfProductPairs_fst_fibre_card {num den N r : ℕ}
    (hr : Nat.Prime r) :
    ((halfProductPairs num den N 0).filter (fun a => a.1 = r)).card =
      (halfProductPrimeFibre num den N r).card := by
  classical
  refine Finset.card_bij (fun a _ => a.2) ?_ ?_ ?_
  · rintro ⟨s, q⟩ ha
    rcases Finset.mem_filter.mp ha with ⟨ha, hs⟩
    dsimp only at hs
    subst s
    obtain ⟨_, hq, hrq, hpow, _, hN⟩ := mem_halfProductPairs.mp ha
    refine mem_halfProductPrimeFibre.mpr ⟨hrq, ?_, hq, hpow⟩
    exact (Nat.le_div_iff_mul_le hr.pos).mpr (by simpa only [Nat.mul_comm] using hN)
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    exact Prod.ext (ha'.trans hb'.symm) hab
  · intro q hq
    obtain ⟨hrq, hqN, hprime, hpow⟩ := mem_halfProductPrimeFibre.mp hq
    refine ⟨(r, q), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    refine mem_halfProductPairs.mpr ⟨hr, hprime, hrq, hpow, ?_, ?_⟩
    · exact Nat.cast_nonneg _
    · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr.pos).mp hqN

/-- Exact summation over the smaller prime, with the original natural
strict-power condition. No exponent positivity is needed for this identity. -/
theorem halfProductSource_card_eq_sum_primeFibre (num den N : ℕ) :
    (halfProductSource num den N 0).card =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N), (halfProductPrimeFibre num den N r).card := by
  classical
  rw [← halfProductPairs_card_eq]
  have hc : (halfProductPairs num den N 0).card =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        ((halfProductPairs num den N 0).filter (fun a => a.1 = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun a ha => halfProductPairs_fst_mem_primesLE_sqrt ha)
  rw [hc]
  apply Finset.sum_congr rfl
  intro r hr
  exact halfProductPairs_fst_fibre_card (Nat.mem_primesLE.mp hr).2

/-- Clearing a positive natural power in a strict inequality gives the
literal reciprocal-exponent boundary, with no rounding or equality loss. -/
theorem nat_pow_lt_iff_lt_reciprocal_rpow {q r num den : ℕ}
    (hnum : 0 < num) :
    q ^ num < r ^ den ↔ (q : ℝ) < (r : ℝ) ^ ((den : ℝ) / (num : ℝ)) := by
  have hnumR : (0 : ℝ) < (num : ℝ) := Nat.cast_pos.mpr hnum
  calc
    q ^ num < r ^ den ↔ (q : ℝ) ^ num < (r : ℝ) ^ den := by norm_cast
    _ ↔ (q : ℝ) < (r : ℝ) ^ ((den : ℝ) / (num : ℝ)) := by
      rw [div_eq_mul_inv, Real.rpow_natCast_mul (Nat.cast_nonneg r),
        Real.lt_rpow_inv_iff_of_pos (Nat.cast_nonneg q)
          (pow_nonneg (Nat.cast_nonneg r) den) hnumR,
        Real.rpow_natCast]

/-- A positive real strict upper bound is represented exactly by its
natural ceiling minus one. Positivity handles the truncation at zero. -/
theorem nat_lt_real_iff_le_ceil_sub_one {q : ℕ} {x : ℝ} (hx : 0 < x) :
    (q : ℝ) < x ↔ q ≤ Nat.ceil x - 1 := by
  have hc : 1 ≤ Nat.ceil x := Nat.one_le_ceil_iff.mpr hx
  rw [← Nat.lt_ceil]
  omega

/-- Inclusive endpoint for the larger prime. The power boundary is strict,
so an integral boundary is rounded down by one, not retained. -/
def halfProductPrimeUpper (num den N r : ℕ) : ℕ :=
  min (N / r) (Nat.ceil ((r : ℝ) ^ ((den : ℝ) / (num : ℝ))) - 1)

/-- Exact combined product and power cutoff, including all strict endpoints. -/
theorem le_halfProductPrimeUpper_iff {num den N r q : ℕ}
    (hnum : 0 < num) (hr : 0 < r) :
    q ≤ halfProductPrimeUpper num den N r ↔
      q ≤ N / r ∧ q ^ num < r ^ den := by
  unfold halfProductPrimeUpper
  rw [le_min_iff, ← nat_lt_real_iff_le_ceil_sub_one
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hr) _),
    ← nat_pow_lt_iff_lt_reciprocal_rpow hnum]

/-- The strict-power prime fibre is precisely a closed natural interval. -/
theorem halfProductPrimeFibre_eq_filter_Icc {num den N r : ℕ}
    (hnum : 0 < num) (hr : 0 < r) :
    halfProductPrimeFibre num den N r =
      (Finset.Icc r (halfProductPrimeUpper num den N r)).filter Nat.Prime := by
  classical
  ext q
  simp only [mem_halfProductPrimeFibre, Finset.mem_filter, Finset.mem_Icc,
    le_halfProductPrimeUpper_iff hnum hr]
  tauto

/-- A prime count on a closed natural interval is a difference of prefix
counts. Truncated natural subtraction gives zero for an empty interval. -/
theorem card_primes_Icc_eq_primeCounting_sub {r Q : ℕ} (hr : 0 < r) :
    ((Finset.Icc r Q).filter Nat.Prime).card =
      Nat.primeCounting Q - Nat.primeCounting (r - 1) := by
  classical
  have heq : (Finset.Icc r Q).filter Nat.Prime =
      Nat.primesLE Q \ Nat.primesLE (r - 1) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hrq, hqQ⟩, hq⟩
      exact ⟨⟨hqQ, hq⟩, by rintro ⟨hqr, _⟩; omega⟩
    · rintro ⟨⟨hqQ, hq⟩, hn⟩
      have hqr : ¬q ≤ r - 1 := fun h => hn ⟨h, hq⟩
      exact ⟨⟨by omega, hqQ⟩, hq⟩
  by_cases h : r - 1 ≤ Q
  · rw [heq, Finset.card_sdiff_of_subset (Nat.primesLE_mono h)]
    simp only [Nat.primesLE_card_eq_primeCounting]
  · have hempty : (Finset.Icc r Q).filter Nat.Prime = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hb := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
      omega
    rw [hempty, Finset.card_empty, Nat.sub_eq_zero_of_le
      (Nat.monotone_primeCounting (by omega : Q ≤ r - 1))]

/-- The exact size of one prime fibre in recognized prime-counting terms. -/
theorem halfProductPrimeFibre_card {num den N r : ℕ}
    (hnum : 0 < num) (hr : 0 < r) :
    (halfProductPrimeFibre num den N r).card =
      Nat.primeCounting (halfProductPrimeUpper num den N r) -
        Nat.primeCounting (r - 1) := by
  rw [halfProductPrimeFibre_eq_filter_Icc hnum hr,
    card_primes_Icc_eq_primeCounting_sub hr]

/-- Exact original-source mass formula. Natural subtraction also covers
empty fibres when the exponent lies outside the manuscript's range. -/
theorem halfProductSource_card_eq_sum_primeCounting {num den N : ℕ}
    (hnum : 0 < num) :
    (halfProductSource num den N 0).card =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        (Nat.primeCounting (halfProductPrimeUpper num den N r) -
          Nat.primeCounting (r - 1)) := by
  rw [halfProductSource_card_eq_sum_primeFibre]
  apply Finset.sum_congr rfl
  intro r hr
  exact halfProductPrimeFibre_card hnum (Nat.mem_primesLE.mp hr).2.pos

/-- In the manuscript's range `num < den`, each outer prime's square lies
inside its fibre, including when `r * r = N`. Thus real subtraction is safe. -/
theorem le_halfProductPrimeUpper_of_mem_primesLE_sqrt {num den N r : ℕ}
    (hnum : 0 < num) (hnumden : num < den)
    (hr : r ∈ Nat.primesLE (Nat.sqrt N)) :
    r ≤ halfProductPrimeUpper num den N r := by
  obtain ⟨hrN, hprime⟩ := Nat.mem_primesLE.mp hr
  apply (le_halfProductPrimeUpper_iff hnum hprime.pos).mpr
  exact ⟨(Nat.le_div_iff_mul_le hprime.pos).mpr (Nat.le_sqrt.mp hrN),
    pow_lt_pow_right₀ hprime.one_lt hnumden⟩

/-- Analytic-facing form of the exact mass identity, using ordinary real
subtraction and the inclusive smaller-prime square-root cutoff. -/
theorem halfProductSource_cast_card_eq_sum_primeCounting {num den N : ℕ}
    (hnum : 0 < num) (hnumden : num < den) :
    ((halfProductSource num den N 0).card : ℝ) =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        ((Nat.primeCounting (halfProductPrimeUpper num den N r) : ℝ) -
          (Nat.primeCounting (r - 1) : ℝ)) := by
  rw [halfProductSource_card_eq_sum_primeCounting hnum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact Nat.cast_sub (Nat.monotone_primeCounting
    ((Nat.sub_le r 1).trans
      (le_halfProductPrimeUpper_of_mem_primesLE_sqrt hnum hnumden hr)))

/-- The original real-cutoff source is a filter of the uncut source. -/
theorem halfProductSource_eq_zero_filter (num den N : ℕ) (T : ℝ) :
    halfProductSource num den N T =
      (halfProductSource num den N 0).filter (fun m => T ≤ (m : ℝ)) := by
  classical
  ext m
  simp only [mem_halfProductSource, Finset.mem_filter]
  constructor
  · rintro ⟨hmN, hT, hm⟩
    exact ⟨⟨hmN, Nat.cast_nonneg m, hm⟩, hT⟩
  · rintro ⟨⟨hmN, _, hm⟩, hT⟩
    exact ⟨hmN, hT, hm⟩

/-- Exactly the integers removed from the original source by the real cutoff. -/
def smallHalfProductSource (num den N : ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (halfProductSource num den N 0).filter (fun m => (m : ℝ) < T)

/-- Exact cutoff partition of the original half-product mass. -/
theorem halfProductSource_zero_card_eq_cutoff_add_small
    (num den N : ℕ) (T : ℝ) :
    (halfProductSource num den N 0).card =
      (halfProductSource num den N T).card + (smallHalfProductSource num den N T).card := by
  classical
  rw [halfProductSource_eq_zero_filter num den N T]
  have h := Finset.card_filter_add_card_filter_not
    (s := halfProductSource num den N 0) (fun m => T ≤ (m : ℝ))
  simpa only [smallHalfProductSource, not_le] using h.symm

/-- The cutoff loses at most its natural ceiling, by an actual injection
of discarded source integers into `[0, ceil T)`. No sign assumption is needed. -/
theorem smallHalfProductSource_card_le_ceil (num den N : ℕ) (T : ℝ) :
    (smallHalfProductSource num den N T).card ≤ Nat.ceil T := by
  classical
  have hs : smallHalfProductSource num den N T ⊆ Finset.range (Nat.ceil T) := by
    intro m hm
    have hcut : (m : ℝ) < T := (Finset.mem_filter.mp hm).2
    exact Finset.mem_range.mpr (Nat.lt_ceil.mpr hcut)
  exact (Finset.card_le_card hs).trans_eq (Finset.card_range _)

/-- An equivalent floor-plus-one bound, also valid for every real cutoff. -/
theorem smallHalfProductSource_card_le_floor_add_one (num den N : ℕ) (T : ℝ) :
    (smallHalfProductSource num den N T).card ≤ Nat.floor T + 1 :=
  (smallHalfProductSource_card_le_ceil num den N T).trans (Nat.ceil_le_floor_add_one T)

/-- The exact original cutoff loss is less than `T + 1` when `T ≥ 0`. -/
theorem smallHalfProductSource_cast_card_lt (num den N : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ((smallHalfProductSource num den N T).card : ℝ) < T + 1 :=
  lt_of_le_of_lt (Nat.cast_le.mpr (smallHalfProductSource_card_le_ceil num den N T))
    (Nat.ceil_lt_add_one hT)

/-- The retained original mass differs from the exact prime-counting sum
by a proved nonnegative error smaller than the real cutoff plus one. -/
theorem halfProductSource_primeCounting_mass_error {num den N : ℕ} {T : ℝ}
    (hnum : 0 < num) (hnumden : num < den) (hT : 0 ≤ T) :
    let S : ℝ := ∑ r ∈ Nat.primesLE (Nat.sqrt N),
      ((Nat.primeCounting (halfProductPrimeUpper num den N r) : ℝ) -
        (Nat.primeCounting (r - 1) : ℝ))
    0 ≤ S - (halfProductSource num den N T).card ∧
      S - (halfProductSource num den N T).card < T + 1 := by
  dsimp only
  rw [← halfProductSource_cast_card_eq_sum_primeCounting hnum hnumden]
  have hpart : ((halfProductSource num den N 0).card : ℝ) =
      ((halfProductSource num den N T).card : ℝ) +
        ((smallHalfProductSource num den N T).card : ℝ) := by
    exact_mod_cast halfProductSource_zero_card_eq_cutoff_add_small num den N T
  have hsmall := smallHalfProductSource_cast_card_lt num den N hT
  have hnonneg : (0 : ℝ) ≤ (smallHalfProductSource num den N T).card := Nat.cast_nonneg _
  constructor <;> linarith

end

end ImbalancedChen
