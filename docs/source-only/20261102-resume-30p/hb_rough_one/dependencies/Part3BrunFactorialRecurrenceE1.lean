import Mathlib
import ImbalancedChen.Part3TwoLongBrunLiteralDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Reusable B2 factorial payment and the exact finite E1 reindexing.
The factorial theorem below takes the explicit elementary recurrence
(r+1)e_(r+1) <= H e_r, not B2 itself. The recurrence is the finite
pair count from phase four; its proof is still an internal formal gap.
No rough distribution or final discrepancy is an input.
-/

namespace ImbalancedChen.Part3.BrunFactorialRecurrenceE1

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongBrunLiteralDensity

noncomputable section

/-- The factorial payment is a direct induction from the concrete
elementary-symmetric recurrence. -/
theorem factorial_symm_bound_from_recurrence
    (e : ℕ → ℝ) (H : ℝ) (hH : 0 ≤ H) (h0 : e 0 = 1)
    (hrec : ∀ r : ℕ, ((r + 1 : ℕ) : ℝ) * e (r + 1) ≤ H * e r) :
    ∀ r : ℕ, (Nat.factorial r : ℝ) * e r ≤ H ^ r := by
  intro r
  induction r with
  | zero =>
      simp [h0]
  | succ r ih =>
      calc
        (Nat.factorial (r + 1) : ℝ) * e (r + 1)
            = (Nat.factorial r : ℝ) *
                (((r + 1 : ℕ) : ℝ) * e (r + 1)) := by
                  rw [Nat.factorial_succ]
                  push_cast
                  ring
        _ ≤ (Nat.factorial r : ℝ) * (H * e r) :=
          mul_le_mul_of_nonneg_left (hrec r) (Nat.cast_nonneg _)
        _ = H * ((Nat.factorial r : ℝ) * e r) := by ring
        _ ≤ H * H ^ r := mul_le_mul_of_nonneg_left ih hH
        _ = H ^ (r + 1) := by rw [pow_succ]; ring

def survivingHarmonic (P : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ p ∈ survivingPrimes P q, (p : ℝ)⁻¹

def chartHarmonic (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (p : ℝ)⁻¹

/-- The exact q-deleted B2 gap has the factorial bound once its finite
pair-count recurrence is supplied. The remaining input is strictly
elementary and does not mention the final rough theorem. -/
theorem reciprocalGap_factorial_from_pair_count
    (j : ℕ) (P : Finset ℕ) (q : ℕ)
    (hrec : ∀ r : ℕ,
      ((r + 1 : ℕ) : ℝ) * reciprocalSymmetric P q (r + 1) ≤
        survivingHarmonic P q * reciprocalSymmetric P q r) :
    (Nat.factorial (2 * j + 1) : ℝ) *
      (reciprocalUpper j P q - reciprocalLower j P q)
      ≤ survivingHarmonic P q ^ (2 * j + 1) := by
  have hH : 0 ≤ survivingHarmonic P q := by
    unfold survivingHarmonic
    positivity
  have h0 : reciprocalSymmetric P q 0 = 1 := by
    simp [reciprocalSymmetric, reciprocalSubsetMass]
  have h := factorial_symm_bound_from_recurrence
    (reciprocalSymmetric P q) (survivingHarmonic P q) hH h0 hrec
    (2 * j + 1)
  simpa only [reciprocalBrunGap_eq] using h

/-- Uniformity in q follows by deleting nonnegative reciprocal terms.
The source of hrec is the still-open finite pair-count identity, not an
analytic or final distribution estimate. -/
theorem reciprocalGap_factorial_uniform_from_pair_count
    (j : ℕ) (P : Finset ℕ) (q : ℕ)
    (hrec : ∀ r : ℕ,
      ((r + 1 : ℕ) : ℝ) * reciprocalSymmetric P q (r + 1) ≤
        survivingHarmonic P q * reciprocalSymmetric P q r) :
    (Nat.factorial (2 * j + 1) : ℝ) *
      (reciprocalUpper j P q - reciprocalLower j P q)
      ≤ chartHarmonic P ^ (2 * j + 1) := by
  have hHq : 0 ≤ survivingHarmonic P q := by
    unfold survivingHarmonic
    positivity
  have hdel : survivingHarmonic P q ≤ chartHarmonic P := by
    unfold survivingHarmonic chartHarmonic
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p hp hnot
    positivity
  calc
    _ ≤ survivingHarmonic P q ^ (2 * j + 1) :=
      reciprocalGap_factorial_from_pair_count j P q hrec
    _ ≤ chartHarmonic P ^ (2 * j + 1) :=
      pow_le_pow_left₀ hHq hdel _

/-- B2's exact displayed quotient, still conditional only on the
elementary pair-count recurrence. -/
theorem reciprocalGap_le_B2_epsilon_from_pair_count
    (j : ℕ) (P : Finset ℕ) (q : ℕ)
    (hrec : ∀ r : ℕ,
      ((r + 1 : ℕ) : ℝ) * reciprocalSymmetric P q (r + 1) ≤
        survivingHarmonic P q * reciprocalSymmetric P q r) :
    reciprocalUpper j P q - reciprocalLower j P q ≤
      chartHarmonic P ^ (2 * j + 1) /
        (Nat.factorial (2 * j + 1) : ℝ) := by
  have hfac : (0 : ℝ) < (Nat.factorial (2 * j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * j + 1)
  apply (le_div_iff₀ hfac).2
  simpa [mul_comm] using
    reciprocalGap_factorial_uniform_from_pair_count j P q hrec

/-- The literal subset Brun coefficient, before grouping by cardinality.
The subset represents d = product(S); the caller supplies the chart-prime
property to identify it with squarefree integer divisors. -/
def literalSubsetCoefficient (P : Finset ℕ) (n order : ℕ) : ℤ :=
  ∑ S ∈ P.powerset,
    if S.card ≤ order ∧ (∀ p ∈ S, p ∣ n)
    then (-1 : ℤ) ^ S.card else 0

/-- Exact finite E1 reindexing, retaining the literal coprime n-sum.
It is valid for arbitrary complex profiles and every q. The smooth
one-dimensional progression estimate is applied after this identity,
for each fixed subset/divisor separately. -/
theorem literalCoprimeE1_reindex
    (P I : Finset ℕ) (q order : ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ I.filter (fun n => Nat.Coprime n q),
      F n * (literalSubsetCoefficient P n order : ℂ))
      = ∑ S ∈ P.powerset,
          if S.card ≤ order then
            ((-1 : ℤ) ^ S.card : ℂ) *
              (∑ n ∈ (I.filter (fun n => Nat.Coprime n q)).filter
                (fun n => ∀ p ∈ S, p ∣ n), F n)
          else 0 := by
  unfold literalSubsetCoefficient
  simp_rw [Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hcard : S.card ≤ order
  · simp only [if_pos hcard]
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hdiv : ∀ p ∈ S, p ∣ n
    · simp [hcard, hdiv, mul_comm]
    · simp [hcard, hdiv]
  · simp [hcard]

/-- A subset containing a chart prime of q contributes zero to the
exact coprime inner sum. This justifies deleting q-primes from A_q
before the one-dimensional progression estimate. -/
theorem coprimeSubsetInner_zero
    (I S : Finset ℕ) (q p : ℕ) (F : ℕ → ℂ)
    (hpPrime : p.Prime) (hpS : p ∈ S) (hpq : p ∣ q) :
    (∑ n ∈ (I.filter (fun n => Nat.Coprime n q)).filter
      (fun n => ∀ t ∈ S, t ∣ n), F n) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hnI, hdiv⟩ := Finset.mem_filter.mp hn
  have hcop : Nat.Coprime n q := (Finset.mem_filter.mp hnI).2
  have hpn : p ∣ n := hdiv p hpS
  have hp1 : p ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hpn hpq
  exact (hpPrime.ne_one (Nat.dvd_one.mp hp1)).elim

end

end ImbalancedChen.Part3.BrunFactorialRecurrenceE1
