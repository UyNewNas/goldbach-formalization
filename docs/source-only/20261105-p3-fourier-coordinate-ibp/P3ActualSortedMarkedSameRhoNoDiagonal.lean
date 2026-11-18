import ImbalancedChen.P3ActualOriginalMarkedPrimeNoDiagonal
import ImbalancedChen.P3ActualEmptyPrimeExceptionalFibre

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
manuscript-body.tex eq:current-PP and prime-product completion §§2-4.

The previous sorted-prime residual source left an exceptional r=N
when the residual word is empty.  Here r is NOT arbitrary: it is the
literal product of a marked word drawn from the same original fine-prime
alphabet, at its own scale.  The source alphabet excludes p | N.

The already established marked/residual Cartesian-box no-diagonal
lemma is now transported to the ACTUAL strictly sorted residual selector,
then to the original arbitrary tuple-dependent W and the complete signed
rho sum.  The exact coprime mean is preserved; no replacement density,
new modulus, sorting multiplicity, or additional arithmetic filter.

This is a marked-box / sorted-residual compatibility theorem, NOT a
claim that all the compiler's HB integer-variable atoms lie in this
prime-only box.  Empty Gamma mother words and arithmetic moment remain
separate. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualSortedMarkedSameRhoNoDiagonal
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualOriginalMarkedPrimeNoDiagonal
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualMarkedOffShiftDivisors

/-- Membership of the real original marked-prime box and the
strictly sorted residual-prime carrier excludes product N for N != 1,
including when the entire residual slot word is empty.  Both prime
alphabets use the SAME target N, but can have different fine scales. -/
theorem sorted_marked_full_product_ne_target
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (marked ps : List ℕ)
    (hm : marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τr blocks)
    (hN : N ≠ 1) :
    marked.prod * ps.prod ≠ N := by
  have hrbox : ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τr)
      (actualPrimeLabelBlocksWord blocks) :=
    (Finset.mem_filter.mp hps).1
  have hpair : (marked, ps) ∈
      (actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τm) markedWord).product
      (actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τr)
        (actualPrimeLabelBlocksWord blocks)) :=
    Finset.mem_product.mpr ⟨hm, hrbox⟩
  intro heq
  have hbad : (marked, ps) ∈
      ((actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τm) markedWord).product
       (actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τr)
        (actualPrimeLabelBlocksWord blocks))).filter
        (fun t => t.1.prod * t.2.prod = N) :=
    Finset.mem_filter.mpr ⟨hpair, heq⟩
  rw [marked_residual_target_fibre_empty_of_target_ne_one
    N τm τr markedWord (actualPrimeLabelBlocksWord blocks) hN] at hbad
  exact (Finset.not_mem_empty _) hbad

/-- Actual sorted residual source has no full physical product N when
the unchanged outside marked integer is a product of actual marked
primes, including zero original residual slots. -/
theorem sorted_marked_full_target_fibre_empty
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (marked : List ℕ)
    (hm : marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord)
    (hN : N ≠ 1) :
    (actualPrimeFineLabelSortedTuples N τr blocks).filter
      (fun ps => marked.prod * ps.prod = N) = ∅ := by
  classical
  ext ps
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  rintro ⟨hps, hfull⟩
  exact (sorted_marked_full_product_ne_target
    N τm τr markedWord blocks marked ps hm hps hN) hfull

/-- With genuine original marked-prime membership, the sorted
prime-only discrepancy has precisely its NONZERO integer-shift
divisor representation.  The same signed rho and physical Q appear
in both the count and the exact coprime mean; arbitrary original
tuple-dependent W and the marked scalar are untouched. -/
theorem weightedSortedPP_original_marked_off_divisors
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (marked : List ℕ)
    (hm : marked ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τm) markedWord)
    (hN : N ≠ 1)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (c : ℝ) (W : List ℕ → ℝ) :
    weightedSortedPP N τr blocks Q rho N marked.prod c W =
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τr blocks).filter
          (fun ps => marked.prod * ps.prod ≠ N),
        (c * (ArithmeticFunction.moebius (marked.prod * ps.prod) : ℝ)) *
          W ps *
          ((if q ∈ (markedShiftAbs marked.prod N ps.prod).divisors
              then (1 : ℝ) else 0) -
           (if Nat.Coprime (marked.prod * ps.prod) q
              then (Nat.totient q : ℝ)⁻¹ else 0))) := by
  rw [weightedSortedPP_split_full_product]
  rw [sorted_marked_full_target_fibre_empty
    N τm τr markedWord blocks marked hm hN]
  simpa using
    (weightedSortedPP_off_divisors
      N τr blocks Q rho N marked.prod c W)

/-- Sum over the literal original MARKED word as well.  The outer
marked occurrences are not quotient-normalized, W may depend on BOTH
original labelled words, and rho is still one common signed integer
function over the entire finite marked/residual box. -/
theorem original_marked_box_sorted_same_rho_off_divisors
    (N : ℕ) (τm τr : ℝ) (markedWord : List ℕ)
    (blocks : List (ℕ × ℕ)) (hN : N ≠ 1)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (c : List ℕ → ℝ) (W : List ℕ → List ℕ → ℝ) :
    (∑ marked ∈ actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τm) markedWord,
      weightedSortedPP N τr blocks Q rho N marked.prod
        (c marked) (W marked)) =
    (∑ marked ∈ actualPrimeSlotBox
        (actualPrimeFineLabelFinset N τm) markedWord,
      ∑ q ∈ Q, rho q *
        ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τr blocks).filter
            (fun ps => marked.prod * ps.prod ≠ N),
          ((c marked) *
            (ArithmeticFunction.moebius (marked.prod * ps.prod) : ℝ)) *
            (W marked ps) *
            ((if q ∈ (markedShiftAbs marked.prod N ps.prod).divisors
                then (1 : ℝ) else 0) -
             (if Nat.Coprime (marked.prod * ps.prod) q
                then (Nat.totient q : ℝ)⁻¹ else 0))) := by
  apply Finset.sum_congr rfl
  intro marked hm
  exact weightedSortedPP_original_marked_off_divisors
    N τm τr markedWord blocks marked hm hN Q rho
    (c marked) (W marked)

end
end ImbalancedChen.P3ActualSortedMarkedSameRhoNoDiagonal
