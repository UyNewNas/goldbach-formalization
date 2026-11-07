import ImbalancedChen.P3ActualNonemptyOriginalPrimeException

/-!
P3.6 original PRIME source: exact full-product=N exceptional contribution.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Pinned manuscript: 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion section 4 (F) and section 3 (T).

An expanded empty original prime word admits one empty tuple with product 1,
even when the blocks list contains zero-multiplicity entries. Thus the only
literal full-product=N exception for this source is the singleton residual
tuple with outside marked integer r=N. Its complete q/rho expression retains
the exact coprime mean and positional W. It is NOT an analytic smallness
bound, does NOT classify HB integer atoms, and is not an empty Gamma payment.
-/

namespace ImbalancedChen.P3ActualOriginalEmptyWordExactPayment
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualMarkedOffShiftDivisors
open ImbalancedChen.P3ActualNonemptyOriginalPrimeException

/-- The ACTUAL original strictly decreasing selector has precisely the
unit residual tuple when the expanded original label word is empty. -/
theorem actual_sorted_empty_word_singleton
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (hword : actualPrimeLabelBlocksWord blocks = []) :
    actualPrimeFineLabelSortedTuples N τ blocks =
      ({[]} : Finset (List ℕ)) := by
  simp [actualPrimeFineLabelSortedTuples, hword, actualPrimeSlotBox]

/-- Exact support classification, not a compiler-generated marked-atom
dictionary. Both the empty residual tuple and the real external r=N
are mathematically forced on the exceptional original-prime fibre. -/
theorem actual_sorted_full_target_forces_empty_and_r
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (r : ℕ) (ps : List ℕ)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τ blocks)
    (hfull : r * ps.prod = N) :
    actualPrimeLabelBlocksWord blocks = [] ∧ ps = [] ∧ r = N := by
  have hnil : ps = [] :=
    actual_sorted_exact_full_product_only_empty N τ blocks r ps hps hfull
  have hword : actualPrimeLabelBlocksWord blocks = [] := by
    by_contra hn
    have hzero := actual_sorted_nonempty_word_exact_fibre_empty
      N τ blocks r hn
    have hmem : ps ∈
        (actualPrimeFineLabelSortedTuples N τ blocks).filter
          (fun qs => r * qs.prod = N) :=
      Finset.mem_filter.mpr ⟨hps, hfull⟩
    rw [hzero] at hmem
    exact (Finset.not_mem_empty ps) hmem
  have hr : r = N := by simpa [hnil] using hfull
  exact ⟨hword, hnil, hr⟩

/-- All original fine-prime full-product=N fibres, with empty and
zero-multiplicity word cases included, have size either zero or one. -/
theorem actual_sorted_full_target_fibre_exact
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ)) (r : ℕ) :
    (actualPrimeFineLabelSortedTuples N τ blocks).filter
        (fun ps => r * ps.prod = N) =
      if actualPrimeLabelBlocksWord blocks = [] ∧ r = N then
        ({[]} : Finset (List ℕ)) else ∅ := by
  classical
  by_cases hw : actualPrimeLabelBlocksWord blocks = []
  · rw [actual_sorted_empty_word_singleton N τ blocks hw]
    by_cases hr : r = N
    · simp [hw, hr]
    · simp [hw, hr]
  · rw [actual_sorted_nonempty_word_exact_fibre_empty N τ blocks r hw]
    simp [hw]

/-- The exceptional ORIGINAL source contributes exactly this signed-rho
scalar if and only if the residual word is empty and r=N. No norm bound
on the modulus coefficient or on W is assumed. -/
theorem actual_sorted_full_target_exception_exact
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ)
    (hcop : ∀ q ∈ Q, Nat.Coprime N q) :
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τ blocks).filter
          (fun ps => r * ps.prod = N),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps * fineKernel N q (r * ps.prod)) =
    if actualPrimeLabelBlocksWord blocks = [] ∧ r = N then
      (c * (ArithmeticFunction.moebius N : ℝ) * W []) *
        (∑ q ∈ Q, rho q * (1 - (Nat.totient q : ℝ)⁻¹))
    else 0 := by
  rw [actual_sorted_full_target_fibre_exact N τ blocks r]
  by_cases h : actualPrimeLabelBlocksWord blocks = [] ∧ r = N
  · simp only [if_pos h, Finset.sum_singleton, List.prod_nil, mul_one]
    have hr : r = N := h.2
    rw [hr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [fineKernel_exact N q (hcop q hq)]
    ring
  · simp [h]

/-- Exact same-rho decomposition for EVERY original sorted-prime word.
The only diagonal is the explicit possible singleton; off-diagonal
divisors concern |N-r*ps.prod| with complete coprime mean and same q.
This does not establish the analytic arbitrary-log PP bound. -/
theorem weightedSortedPP_target_N_all_original_words
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ)
    (hcop : ∀ q ∈ Q, Nat.Coprime N q) :
    weightedSortedPP N τ blocks Q rho N r c W =
      (if actualPrimeLabelBlocksWord blocks = [] ∧ r = N then
        (c * (ArithmeticFunction.moebius N : ℝ) * W []) *
          (∑ q ∈ Q, rho q * (1 - (Nat.totient q : ℝ)⁻¹))
       else 0) +
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
  rw [actual_sorted_full_target_exception_exact
    N τ blocks Q rho r c W hcop]
  rw [weightedSortedPP_off_divisors
    N τ blocks Q rho N r c W]

end
end ImbalancedChen.P3ActualOriginalEmptyWordExactPayment
