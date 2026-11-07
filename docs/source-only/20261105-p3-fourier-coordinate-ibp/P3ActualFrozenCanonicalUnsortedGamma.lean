import ImbalancedChen.P3ActualFrozenTaggedLabelCompiler
import ImbalancedChen.ActualPrimeFineWordMultiplicity

/-!
P3.6 / pinned manuscript completion section 3 (T) and section 4 (F).
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

An actual physical atom's original-ID fine-label word need NOT be weakly
descending. We sort ONLY the label dictionary used to compute its precise
per-label multiplicities. We never sort or permute its physical ordered prime
tuples, nor the position-dependent Fourier multipliers attached to their IDs.

The canonical dictionary is computed, not an hword/normalization premise.
This does NOT identify all PP atom compilers, prove Fourier inversion,
supply physical rho_T, or pay any arithmetic discrepancy.
-/

namespace ImbalancedChen.P3ActualFrozenCanonicalUnsortedGamma
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P3ActualFrozenComplexGroupGamma

/-- Canonical distinct fine-label blocks for ANY original slot word.
Sorting is restricted to this combinatorial dictionary; it does not
reindex the original physical ordered prime tuple or its Fourier phase. -/
def canonicalFineBlocks (word : List ℕ) : List (ℕ × ℕ) :=
  actualPrimeFineLabelBlocksOfWord (word.mergeSort (· ≥ ·))

/-- The computed canonical dictionary has exactly the same multiset of
label occurrences, including zero-length words and repeated labels. -/
theorem canonicalFineBlocks_word_perm (word : List ℕ) :
    (actualPrimeLabelBlocksWord (canonicalFineBlocks word)).Perm word := by
  change (actualPrimeLabelBlocksWord
    (actualPrimeFineLabelBlocksOfWord (word.mergeSort (· ≥ ·)))).Perm word
  rw [actualPrimeFineLabelBlocksOfWord_word]
  exact List.mergeSort_perm word _

/-- Run-length compression of the sorted dictionary yields pairwise
distinct labels even when the physical source word was unsorted. -/
theorem canonicalFineBlocks_pairwise (word : List ℕ) :
    (canonicalFineBlocks word).Pairwise
      (fun b c => b.1 ≠ c.1) := by
  have hs : (word.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) :=
    List.sortedGE_mergeSort
  exact (actualPrimeFineLabelBlocksOfWord_order _ hs).imp
    (fun h => Nat.ne_of_gt h)

/-- The original literal per-label factorial is invariant under a
permutation of labels. This is NOT an invariance of positional weights. -/
theorem fineWordMultiplicity_perm {u v : List ℕ} (h : u.Perm v) :
    actualPrimeFineWordMultiplicity u =
      actualPrimeFineWordMultiplicity v := by
  unfold actualPrimeFineWordMultiplicity
  have hset : u.toFinset = v.toFinset := by
    ext i
    simpa only [List.mem_toFinset] using
      (h.mem_iff : i ∈ u ↔ i ∈ v)
  rw [hset]
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg Nat.factorial (h.count_eq i)

/-- The canonical dictionary divisor is EXACTLY the original
M_J = product over labels of (occurrence count)!, without an horder
assumption and without using total-slot factorial. -/
theorem canonicalFineBlocks_factorial (word : List ℕ) :
    actualPrimeLabelBlocksFactorial (canonicalFineBlocks word) =
      actualPrimeFineWordMultiplicity word := by
  calc
    _ = actualPrimeFineWordMultiplicity (word.mergeSort (· ≥ ·)) := by
      exact actualPrimeFineLabelBlocksOfWord_factorial _
        List.sortedGE_mergeSort
    _ = actualPrimeFineWordMultiplicity word :=
      fineWordMultiplicity_perm (List.mergeSort_perm word _)

/-- The genuine ID-ordered Fourier coefficient has its original exact
multiset factorial for ARBITRARY label order. Only the dictionary is
canonicalized: the actual prime box and its positional multiplier remain
in the original ID order. -/
theorem canonical_positional_gamma_original_fibre {n : ℕ}
    (B : ℕ → Finset ℕ) (label : Fin n → ℕ)
    (ids : List (Fin n)) (eta U : Fin n → ℝ)
    (product : ℕ) :
    physicalComplexLabelGamma B (ids.map label)
        (canonicalFineBlocks (ids.map label))
        (positionalGroupMode eta U ids) product =
      (∑ ps ∈ (actualPrimeSlotBox
          (fun i : Fin n => B (label i)) ids).filter
          (fun ps => ps.prod = product),
        positionalGroupMode eta U ids ps) /
          (actualPrimeFineWordMultiplicity (ids.map label) : ℂ) := by
  rw [positional_gamma_original_ID_fibre]
  rw [canonicalFineBlocks_factorial]

/-- The literal positional Fourier coefficient is one-bounded on every
integer, for ANY original ID/label order, after exact canonical per-label
factorial normalization. Neither a sorted original source word nor a
permutation invariance of the complex positional mode is assumed. -/
theorem canonical_positional_gamma_norm_le_one {n : ℕ}
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (label : Fin n → ℕ) (ids : List (Fin n))
    (eta U : Fin n → ℝ) (product : ℕ) :
    ‖physicalComplexLabelGamma (actualPrimeFineLabelFinset N τ)
      (ids.map label) (canonicalFineBlocks (ids.map label))
      (positionalGroupMode eta U ids) product‖ ≤ 1 := by
  exact physicalComplexLabelGamma_norm_le_one
    N hN τ hτ (canonicalFineBlocks (ids.map label))
    (canonicalFineBlocks_pairwise (ids.map label))
    (ids.map label) (canonicalFineBlocks_word_perm (ids.map label))
    (positionalGroupMode eta U ids)
    (fun ps _ => positionalGroupMode_norm_le_one eta U ids ps)
    product

/-- All THREE literal frozen physical-ID groups enjoy the one-bound
without requiring weakly descending original fine labels. No tuple
or Fourier weight is reindexed and each group carries its own exact
per-label factorial. The source-to-global-PP-atom compiler and original
global restoring scalar remain separate internal obligations. -/
theorem actual_frozen_unsorted_ID_three_canonical_gamma_bounds {n : ℕ}
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool)
    (label : Fin n → ℕ) (upperLabel : ℕ → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (eta U : Fin n → ℝ) (a b d : ℕ) :
    let groups := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let B := actualPrimeFineLabelFinset N τ
    (‖physicalComplexLabelGamma B (groups.1.map label)
      (canonicalFineBlocks (groups.1.map label))
      (positionalGroupMode eta U groups.1) a‖ ≤ 1) ∧
    (‖physicalComplexLabelGamma B (groups.2.1.map label)
      (canonicalFineBlocks (groups.2.1.map label))
      (positionalGroupMode eta U groups.2.1) b‖ ≤ 1) ∧
    (‖physicalComplexLabelGamma B (groups.2.2.map label)
      (canonicalFineBlocks (groups.2.2.map label))
      (positionalGroupMode eta U groups.2.2) d‖ ≤ 1) := by
  dsimp only
  exact ⟨canonical_positional_gamma_norm_le_one
      N hN τ hτ label _ eta U a,
    canonical_positional_gamma_norm_le_one
      N hN τ hτ label _ eta U b,
    canonical_positional_gamma_norm_le_one
      N hN τ hτ label _ eta U d⟩

end
end ImbalancedChen.P3ActualFrozenCanonicalUnsortedGamma
