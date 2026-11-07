import ImbalancedChen.P3ActualEvenOriginalPrimeException

/-!
P3.6 / original fine-prime word, full physical integer and the empty-word boundary.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Pinned manuscript: 9731290e8f53cffda44129906cde6a965eaa869b,
completion note §§1, 3 (T), 4 (F).

The actual original fine-prime membership requires p ∤ N. Consequently,
EVERY nonempty residual original-prime tuple has a factor p not dividing N.
For T=N, no outside marked integer r (even or odd) can restore its full
product r * ps.prod to N. This strengthens the earlier parity-only result
without presuming a marked atom compiler or an unsupplied oddness of r.

An EMPTY residual word is different: ps.prod=1, and r=N may contribute.
This boundary is kept visible and is not identified with a unit HB log
slot, or with the absence of an empty Gamma mother-word obligation.
-/

namespace ImbalancedChen.P3ActualNonemptyOriginalPrimeException
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualMarkedOffShiftDivisors

/-- Each factor in the LITERAL sorted fine-prime selector excludes
divisors of its actual target parameter N; no parity or size cutoff
is needed, and positional weights are not rearranged. -/
theorem actual_sorted_prime_not_dvd_N
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ)) (ps : List ℕ)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τ blocks) :
    ∀ p ∈ ps, ¬ p ∣ N := by
  have hbox : ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ) (actualPrimeLabelBlocksWord blocks) :=
    (Finset.mem_filter.mp hps).1
  exact actualPrimeSlotBox_forall
    (actualPrimeFineLabelFinset N τ) (actualPrimeLabelBlocksWord blocks)
    (fun p : ℕ => ¬ p ∣ N)
    (by
      intro i hi p hp
      exact (mem_actualPrimeFineLabelFinset.mp hp).2.1)
    ps hbox

/-- An original fine-prime tuple with at least one residual prime
cannot have complete marked product N, for ANY outside integer r.
The contradiction is literal p ∤ N versus p ∣ r * ps.prod = N. -/
theorem actual_sorted_nonempty_full_product_ne_N
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (r : ℕ) (ps : List ℕ)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τ blocks)
    (hne : ps ≠ []) : r * ps.prod ≠ N := by
  cases ps with
  | nil => exact (hne rfl).elim
  | cons p rest =>
      have hnot : ¬ p ∣ N :=
        actual_sorted_prime_not_dvd_N N τ blocks (p :: rest) hps p (by simp)
      intro hfull
      apply hnot
      refine ⟨r * rest.prod, ?_⟩
      calc
        N = r * (p * rest.prod) := by
          simpa only [List.prod_cons] using hfull.symm
        _ = p * (r * rest.prod) := by ac_rfl

/-- This identifies the ONLY possible full-product=N exception in the
actual original PRIME tuple family: an empty residual tuple.
It does NOT assert that a marked compiler actually produces such a tuple. -/
theorem actual_sorted_exact_full_product_only_empty
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (r : ℕ) (ps : List ℕ)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τ blocks)
    (hfull : r * ps.prod = N) : ps = [] := by
  by_contra hne
  exact (actual_sorted_nonempty_full_product_ne_N
    N τ blocks r ps hps hne) hfull

/-- An empty physical tuple belongs to the original slot box exactly
when the actual original slot word is empty. -/
private theorem nil_mem_original_prime_box_iff
    {ι : Type*} (B : ι → Finset ℕ) (word : List ι) :
    ([] : List ℕ) ∈ actualPrimeSlotBox B word ↔ word = [] := by
  cases word with
  | nil => simp [actualPrimeSlotBox]
  | cons i rest => simp [actualPrimeSlotBox]

/-- With a genuinely nonempty original residual slot word, the entire
complete-product=N exceptional fibre is empty for ANY marked r.
No hypothesis about r being odd or coprime to N is inserted. -/
theorem actual_sorted_nonempty_word_exact_fibre_empty
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ)) (r : ℕ)
    (hword : actualPrimeLabelBlocksWord blocks ≠ []) :
    (actualPrimeFineLabelSortedTuples N τ blocks).filter
      (fun ps => r * ps.prod = N) = ∅ := by
  classical
  ext ps
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  rintro ⟨hps, hfull⟩
  have hnil := actual_sorted_exact_full_product_only_empty N τ blocks r ps hps hfull
  subst ps
  have hbox : ([] : List ℕ) ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ) (actualPrimeLabelBlocksWord blocks) :=
    (Finset.mem_filter.mp hps).1
  exact hword ((nil_mem_original_prime_box_iff
    (actualPrimeFineLabelFinset N τ) (actualPrimeLabelBlocksWord blocks)).mp hbox)

/-- In this precisely delimited real original-prime source (T=N and
nonempty residual slot word), the signed full physical discrepancy
equals the complete NONZERO-shift divisor expression, with the SAME
physical rho, literal modulus q, complete mu(r*n), original arbitrary
positional W, and exact coprime mean. This is only an algebraic
rewriting: no analytic shifted-moment estimate is supplied. -/
theorem weightedSortedPP_target_N_nonempty_word_off_divisors
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ)
    (hword : actualPrimeLabelBlocksWord blocks ≠ []) :
    weightedSortedPP N τ blocks Q rho N r c W =
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τ blocks).filter
          (fun ps => r * ps.prod ≠ N),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps *
          ((if q ∈ (markedShiftAbs r N ps.prod).divisors
              then (1 : ℝ) else 0) -
           (if Nat.Coprime (r * ps.prod) q
              then (Nat.totient q : ℝ)⁻¹ else 0))) := by
  rw [weightedSortedPP_split_full_product]
  rw [actual_sorted_nonempty_word_exact_fibre_empty N τ blocks r hword]
  simpa using (weightedSortedPP_off_divisors N τ blocks Q rho N r c W)

end
end ImbalancedChen.P3ActualNonemptyOriginalPrimeException
