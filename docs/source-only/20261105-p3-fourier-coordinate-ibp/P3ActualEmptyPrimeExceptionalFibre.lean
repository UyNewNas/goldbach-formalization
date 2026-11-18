import ImbalancedChen.P3ActualNonemptyOriginalPrimeException
import Mathlib.Tactic

/-!
P3.6 / frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2-4 and the exact current-PP coprime mean.

The original fine PRIME source has an exact full-product = N exceptional
fibre only when its *residual slot word is empty* and the unchanged marked
outside integer r equals N. Here we compute that singleton, including its
literal Mobius factor, arbitrary tuple-dependent geometric W, original
SIGNED rho and exact reciprocal-totient subtraction.

This is a FINITE exact-prime-carrier calculation, not a statement about
the rough HB integer-variable source, its empty-Gamma mother words or
the missing arithmetic shift/moment bound. No modulus or source is
changed. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEmptyPrimeExceptionalFibre
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualNonemptyOriginalPrimeException
open ImbalancedChen.P3ActualMarkedOffShiftDivisors

/-- The actual original sorted PRIME carrier with an empty label word is
precisely the singleton empty tuple, including its product 1. -/
theorem sorted_empty_word_singleton
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (hword : actualPrimeLabelBlocksWord blocks = []) :
    actualPrimeFineLabelSortedTuples N τ blocks =
      {([] : List ℕ)} := by
  unfold actualPrimeFineLabelSortedTuples
  rw [hword]
  simp [actualPrimeSlotBox]

/-- Complete physical product r * ps.prod = N: exact source-fibre
dichotomy, including the previously open EMPTY residual slot word.
No parity assumption and no substitution of a residual-only product. -/
theorem sorted_target_exact_fibre
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (r : ℕ) :
    (actualPrimeFineLabelSortedTuples N τ blocks).filter
      (fun ps => r * ps.prod = N) =
    if actualPrimeLabelBlocksWord blocks = [] ∧ r = N
      then {([] : List ℕ)} else ∅ := by
  by_cases hword : actualPrimeLabelBlocksWord blocks = []
  · rw [sorted_empty_word_singleton N τ blocks hword]
    by_cases hr : r = N
    · simp [hword, hr]
    · simp [hword, hr]
  · rw [actual_sorted_nonempty_word_exact_fibre_empty
      N τ blocks r hword]
    simp [hword]

/-- The actual exact-product=N signed PP contribution, retaining
rho(q) in BOTH congruence and coprime mean, is a literal singleton.
The value is not declared small: it still needs physical source payment
if an empty original residual word is actually produced. -/
theorem exact_target_N_signed_mass
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
      ((c * (ArithmeticFunction.moebius N : ℝ)) * W []) *
        (∑ q ∈ Q, rho q * (1 - (Nat.totient q : ℝ)⁻¹))
    else 0 := by
  rw [sorted_target_exact_fibre N τ blocks r]
  split_ifs with h
  · rcases h with ⟨_, rfl⟩
    simp only [Finset.sum_singleton, List.prod_nil, mul_one]
    calc
      (∑ q ∈ Q, rho q *
        ((c * (ArithmeticFunction.moebius N : ℝ)) * W [] *
          fineKernel N q N)) =
        ∑ q ∈ Q,
          ((c * (ArithmeticFunction.moebius N : ℝ)) * W []) *
            (rho q * (1 - (Nat.totient q : ℝ)⁻¹)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [fineKernel_exact N q (hcop q hq)]
          ring
      _ = _ := by rw [Finset.mul_sum]
  · simp

/-- With no empty residual word, or whenever the unchanged marked
outside integer r differs from N, the *exact* fibre is empty. This
particular theorem removes the r != N diagonal WITHOUT demanding a
new condition on the geometric weight or the signed physical rho. -/
theorem sorted_target_exact_fibre_empty_of_marked_ne
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (r : ℕ) (hr : r ≠ N) :
    (actualPrimeFineLabelSortedTuples N τ blocks).filter
      (fun ps => r * ps.prod = N) = ∅ := by
  rw [sorted_target_exact_fibre N τ blocks r]
  simp [hr]

/-- The *entire* physical sorted PRIME discrepancy is then its literal
NONZERO full-shift divisor expression; the exact coprime mean, signed
rho, marked scalar, tuple-dependent W and physical q are untouched.
This does NOT yet bound the off-diagonal arithmetic moment. -/
theorem weightedSortedPP_target_off_if_marked_ne
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ) (hr : r ≠ N) :
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
  rw [sorted_target_exact_fibre_empty_of_marked_ne N τ blocks r hr]
  simpa using (weightedSortedPP_off_divisors N τ blocks
    Q rho N r c W)

end
end ImbalancedChen.P3ActualEmptyPrimeExceptionalFibre
