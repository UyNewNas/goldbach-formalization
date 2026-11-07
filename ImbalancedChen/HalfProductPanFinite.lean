import ImbalancedChen.FiniteSieveModel
import ImbalancedChen.HalfProductMassFibres

/-!
# Finite smaller-prime expansion for the Pan discrepancy

This file rewrites the exact residue-class discrepancy used by the
half-product bounding sieve as a sum over the smaller prime factor.
The inner summand is a count of larger primes in one moving residue
class, with the original real cutoff, inclusive product endpoint,
strict power boundary, and prime-square diagonal all retained.

The final indicator form makes the outer coefficient explicit: it is
the characteristic function of the primes at most the square root of N,
hence is pointwise bounded by one.  This is the finite representation needed
to compare the existing sieve remainder with a bounded-coefficient Pan
estimate.  No distribution estimate is asserted in this file.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The larger-prime fibre with the manuscript's real product cutoff retained. -/
def halfProductPrimeFibreAtCutoff
    (num den N : ℕ) (T : ℝ) (r : ℕ) : Finset ℕ := by
  classical
  exact (halfProductPrimeFibre num den N r).filter
    (fun q : ℕ => T ≤ (r * q : ℕ))

@[simp] theorem mem_halfProductPrimeFibreAtCutoff
    {num den N r q : ℕ} {T : ℝ} :
    q ∈ halfProductPrimeFibreAtCutoff num den N T r ↔
      r ≤ q ∧ q ≤ N / r ∧ Nat.Prime q ∧ q ^ num < r ^ den ∧
        T ≤ (r * q : ℕ) := by
  classical
  simp only [halfProductPrimeFibreAtCutoff, Finset.mem_filter,
    mem_halfProductPrimeFibre]
  tauto

/-- Multiplication followed by projection onto the larger prime is a
bijection on every fixed smaller-prime fibre, after any product predicate. -/
theorem halfProductPairs_filter_fst_fibre_card
    {num den N r : ℕ} {T : ℝ} (P : ℕ → Prop) [DecidablePred P]
    (hr : Nat.Prime r) :
    (((halfProductPairs num den N T).filter
        (fun a => P (a.1 * a.2))).filter (fun a => a.1 = r)).card =
      ((halfProductPrimeFibreAtCutoff num den N T r).filter
        (fun q => P (r * q))).card := by
  classical
  refine Finset.card_bij (fun a _ => a.2) ?_ ?_ ?_
  · rintro ⟨s, q⟩ ha
    rcases Finset.mem_filter.mp ha with ⟨ha, hs⟩
    rcases Finset.mem_filter.mp ha with ⟨ha, hP⟩
    dsimp only at hs
    subst s
    obtain ⟨_, hq, hrq, hpow, hcut, hN⟩ := mem_halfProductPairs.mp ha
    refine Finset.mem_filter.mpr ⟨?_, hP⟩
    refine mem_halfProductPrimeFibreAtCutoff.mpr
      ⟨hrq, ?_, hq, hpow, hcut⟩
    exact (Nat.le_div_iff_mul_le hr.pos).mpr
      (by simpa only [Nat.mul_comm] using hN)
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    exact Prod.ext (ha'.trans hb'.symm) hab
  · intro q hq
    rcases Finset.mem_filter.mp hq with ⟨hq, hP⟩
    obtain ⟨hrq, hqN, hprime, hpow, hcut⟩ :=
      mem_halfProductPrimeFibreAtCutoff.mp hq
    refine ⟨(r, q), Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨?_, hP⟩, rfl⟩, rfl⟩
    refine mem_halfProductPairs.mpr ⟨hr, hprime, hrq, hpow, hcut, ?_⟩
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hr.pos).mp hqN

/-- Every product-filtered source count is exactly a sum of larger-prime
fibre counts over the smaller primes at most the inclusive square root. -/
theorem halfProductSource_filter_card_eq_sum_primeFibreAtCutoff
    (num den N : ℕ) (T : ℝ) (P : ℕ → Prop) [DecidablePred P] :
    ((halfProductSource num den N T).filter P).card =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        ((halfProductPrimeFibreAtCutoff num den N T r).filter
          (fun q => P (r * q))).card := by
  classical
  rw [← halfProductPairs_filter_card_eq num den N T P]
  let s := (halfProductPairs num den N T).filter
    (fun a => P (a.1 * a.2))
  have hc : s.card =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        (s.filter (fun a => a.1 = r)).card :=
    Finset.card_eq_sum_card_fiberwise (fun a ha =>
      halfProductPairs_fst_mem_primesLE_sqrt (Finset.mem_filter.mp ha).1)
  rw [hc]
  apply Finset.sum_congr rfl
  intro r hr
  exact halfProductPairs_filter_fst_fibre_card P
    (Nat.mem_primesLE.mp hr).2

/-- One smaller-prime fibre counted in the moving residue class. -/
def halfProductPrimeFibreAPCount
    (num den N : ℕ) (T : ℝ) (d r : ℕ) : ℝ :=
  (((halfProductPrimeFibreAtCutoff num den N T r).filter
    (fun q : ℕ => Nat.ModEq d (r * q) N)).card : ℝ)

/-- One smaller-prime fibre counted with its product coprime to the modulus. -/
def halfProductPrimeFibreCoprimeMass
    (num den N : ℕ) (T : ℝ) (d r : ℕ) : ℝ :=
  (((halfProductPrimeFibreAtCutoff num den N T r).filter
    (fun q : ℕ => Nat.Coprime (r * q) d)).card : ℝ)

/-- Exact expansion of the actual congruence mass into moving prime fibres. -/
theorem halfProductCongruenceMass_eq_sum_primeFibreAPCount
    (num den N : ℕ) (T : ℝ) (d : ℕ) :
    halfProductCongruenceMass num den N T d =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        halfProductPrimeFibreAPCount num den N T d r := by
  classical
  unfold halfProductCongruenceMass halfProductPrimeFibreAPCount
  rw [halfProductSource_filter_card_eq_sum_primeFibreAtCutoff, Nat.cast_sum]

/-- The exact shifted divisor sum in the bounding sieve has the same
smaller-prime expansion.  This is the direct finite input for a Pan
distribution estimate. -/
theorem halfProductBoundingSieve_multSum_eq_sum_primeFibreAPCount
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) (d : ℕ) :
    (halfProductBoundingSieve num den N T z hN).multSum d =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        halfProductPrimeFibreAPCount num den N T d r := by
  rw [halfProductBoundingSieve_multSum,
    halfProductCongruenceMass_eq_sum_primeFibreAPCount]

/-- Exact expansion of the coprime source mass into the same prime fibres. -/
theorem halfProductCoprimeMass_eq_sum_primeFibreCoprimeMass
    (num den N : ℕ) (T : ℝ) (d : ℕ) :
    halfProductCoprimeMass num den N T d =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        halfProductPrimeFibreCoprimeMass num den N T d r := by
  classical
  unfold halfProductCoprimeMass halfProductPrimeFibreCoprimeMass
  rw [halfProductSource_filter_card_eq_sum_primeFibreAtCutoff, Nat.cast_sum]

/-- The primitive moving-class discrepancy on a single smaller-prime fibre. -/
def halfProductPrimeFibreDiscrepancy
    (num den N : ℕ) (T : ℝ) (d r : ℕ) : ℝ :=
  halfProductPrimeFibreAPCount num den N T d r -
    halfProductPrimeFibreCoprimeMass num den N T d r /
      (Nat.totient d : ℝ)

/-- The existing primitive half-product discrepancy is exactly the sum
of the single-fibre moving-class discrepancies. -/
theorem halfProduct_primitiveDiscrepancy_eq_sum_primeFibre
    (num den N : ℕ) (T : ℝ) (d : ℕ) :
    halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ) =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        halfProductPrimeFibreDiscrepancy num den N T d r := by
  rw [halfProductCongruenceMass_eq_sum_primeFibreAPCount,
    halfProductCoprimeMass_eq_sum_primeFibreCoprimeMass]
  simp only [halfProductPrimeFibreDiscrepancy, Finset.sum_div,
    Finset.sum_sub_distrib]

/-- Indicator form of the congruence expansion. The outer coefficient
is literally zero or one; no factor multiplicity or factor two appears. -/
theorem halfProductCongruenceMass_eq_sum_prime_indicator
    (num den N : ℕ) (T : ℝ) (d : ℕ) :
    halfProductCongruenceMass num den N T d =
      ∑ r ∈ Finset.Ioc 0 (Nat.sqrt N),
        (if Nat.Prime r then (1 : ℝ) else 0) *
          halfProductPrimeFibreAPCount num den N T d r := by
  classical
  rw [halfProductCongruenceMass_eq_sum_primeFibreAPCount,
    Nat.primesLE_eq_filter_Ioc_zero, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hp : Nat.Prime r
  · simp [hp]
  · simp [hp]

/-- The prime-indicator coefficient in the outer Pan sum has absolute
value at most one, uniformly in the smaller-prime variable. -/
theorem abs_primeIndicator_le_one (r : ℕ) :
    |(if Nat.Prime r then (1 : ℝ) else 0)| ≤ 1 := by
  by_cases hp : Nat.Prime r <;> simp [hp]

end

end ImbalancedChen
