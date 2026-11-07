import ImbalancedChen.P3ActualFrozenCanonicalUnsortedGamma
import ImbalancedChen.P3ActualFrozenSlotLabelCounts

/-!
P3.6, pinned manuscript completion §§3 (T), 4 (F).
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Recover the *literal* three-way repeated-label factorial split from the
actual selected-pair output for an ARBITRARILY ORDERED source label word.
Only the multiplicity dictionary is sorted. No prime tuple, original
Fin-ID or positional Fourier multiplier is reordered.

No PP atom source compiler, physical rho, modulus estimate, W_T analytic
admission or target-equivalent assumption is supplied by this file.
-/

namespace ImbalancedChen.P3ActualCanonicalFrozenSplitPayment
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenCanonicalUnsortedGamma
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualFrozenGroupWords
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3ActualFrozenTaggedLabelCompiler
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes

/-- The split size is read from the TRUE frozen output occurrences;
the original canonical block count is *derived* from its permutation
to the literal unsorted input word. No input hword is assumed. -/
theorem canonical_source_split_counts
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ) :
    let word := p 0 :: p 1 :: p 2 :: tail
    let blocks := canonicalFineBlocks word
    let size := actualFrozenSplitSize D A yz upper p tail
    ∀ b ∈ blocks,
      b.2 = size b.1 0 + size b.1 1 + size b.1 2 := by
  let word := p 0 :: p 1 :: p 2 :: tail
  let blocks := canonicalFineBlocks word
  let size := actualFrozenSplitSize D A yz upper p tail
  intro b hb
  have hfirst := original_block_size_eq_word_count
    blocks (canonicalFineBlocks_pairwise word) hb
  have hperm := (canonicalFineBlocks_word_perm word).count_eq b.1
  have hsplit := actualFrozenSplitSize_sum D A yz upper p tail b.1
  exact hfirst.trans (hperm.trans hsplit)

/-- Every actual group is recovered label-by-label from the canonical
source blocks, including a label absent from all groups or split across
several groups. This is not a positional multiplier reindexing. -/
theorem canonical_source_split_word_count
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (i : ℕ) (j : Fin 3) :
    let word := p 0 :: p 1 :: p 2 :: tail
    let blocks := canonicalFineBlocks word
    let size := actualFrozenSplitSize D A yz upper p tail
    (actualPrimeLabelBlocksWord (splitBlocks blocks size j)).count i =
      size i j := by
  let word := p 0 :: p 1 :: p 2 :: tail
  let blocks := canonicalFineBlocks word
  let size := actualFrozenSplitSize D A yz upper p tail
  have hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1) :=
    canonicalFineBlocks_pairwise word
  by_cases hm : ∃ m : ℕ, (i, m) ∈ blocks
  · obtain ⟨m, hmem⟩ := hm
    exact split_word_count_of_member blocks size hpair i m hmem j
  · have haway : ∀ b ∈ blocks, b.1 ≠ i := by
      intro b hb heq
      rcases b with ⟨k, m⟩
      change k = i at heq
      subst k
      exact hm ⟨m, hb⟩
    have hblockzero :
        (actualPrimeLabelBlocksWord blocks).count i = 0 := by
      rw [expanded_word_count]
      exact blockLabelCount_zero_of_away blocks i haway
    have hwordzero : word.count i = 0 :=
      ((canonicalFineBlocks_word_perm word).count_eq i).symm.trans hblockzero
    have hsum : word.count i =
        size i 0 + size i 1 + size i 2 :=
      actualFrozenSplitSize_sum D A yz upper p tail i
    rw [hwordzero] at hsum
    have hz : size i j = 0 := by
      fin_cases j <;> omega
    exact (split_word_count_of_absent blocks size i haway j).trans hz.symm

/-- The three ACTUAL output label words are permutations of their
computed original-label split blocks. The input source word may be
unsorted: hword is not a premise. This does not transport Fourier weights. -/
theorem canonical_source_split_group_perm
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ) (j : Fin 3) :
    let blocks := canonicalFineBlocks (p 0 :: p 1 :: p 2 :: tail)
    let size := actualFrozenSplitSize D A yz upper p tail
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (actualPrimeLabelBlocksWord (splitBlocks blocks size j)).Perm
      (if j = 0 then groups.1 else if j = 1 then groups.2.1
       else groups.2.2) := by
  apply List.perm_iff_count.mpr
  intro i
  have hcount := canonical_source_split_word_count
    D A yz upper p tail i j
  fin_cases j <;> simpa [actualFrozenSplitSize] using hcount

/-- Genuine original M_all and three actual split M_j, not total-slot
factorials. The correction is in [0,1] for every unsorted physical word,
including empty groups and repeated fine labels. -/
theorem canonical_source_split_ratio_mem_Icc
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ) :
    let blocks := canonicalFineBlocks (p 0 :: p 1 :: p 2 :: tail)
    let size := actualFrozenSplitSize D A yz upper p tail
    (((actualPrimeLabelBlocksFactorial (splitBlocks blocks size 0) : ℝ) *
       (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 1) : ℝ) *
       (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 2) : ℝ)) /
       (actualPrimeLabelBlocksFactorial blocks : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  exact split_factorial_ratio_mem_Icc
    (canonicalFineBlocks (p 0 :: p 1 :: p 2 :: tail))
    (actualFrozenSplitSize D A yz upper p tail)
    (canonical_source_split_counts D A yz upper p tail)

/-- Actual original Fin n IDs remain bound to their position-dependent
Fourier multipliers. The genuine label allocator is used only to transfer
the proved group-word permutations, via its noninjective map naturality.
Each normalized group is one-bounded, with the SAME split blocks used
by the restoring scalar above; no arbitrary dictionary is a premise. -/
theorem actual_unsorted_ID_split_three_positional_gamma_bounds {n : ℕ}
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool) (upperLabel : ℕ → ℕ)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n)) (eta U : Fin n → ℝ)
    (a b d : ℕ) :
    let pLabel : Fin 3 → ℕ := fun j => label (p j)
    let tailLabel := tail.map label
    let blocks := canonicalFineBlocks
      (pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel)
    let size := actualFrozenSplitSize D A yz upperLabel pLabel tailLabel
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let B := actualPrimeFineLabelFinset N τ
    (‖physicalComplexLabelGamma B (ids.1.map label)
      (splitBlocks blocks size 0)
      (positionalGroupMode eta U ids.1) a‖ ≤ 1) ∧
    (‖physicalComplexLabelGamma B (ids.2.1.map label)
      (splitBlocks blocks size 1)
      (positionalGroupMode eta U ids.2.1) b‖ ≤ 1) ∧
    (‖physicalComplexLabelGamma B (ids.2.2.map label)
      (splitBlocks blocks size 2)
      (positionalGroupMode eta U ids.2.2) d‖ ≤ 1) := by
  let pLabel : Fin 3 → ℕ := fun j => label (p j)
  let tailLabel := tail.map label
  let word := pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel
  let blocks := canonicalFineBlocks word
  let size := actualFrozenSplitSize D A yz upperLabel pLabel tailLabel
  let ids := actualFrozenSelectedPairSlots D A yz
    (fun i => upperLabel (label i)) p tail
  have hlabel :
      actualFrozenSelectedPairSlots D A yz upperLabel pLabel tailLabel =
        (ids.1.map label, ids.2.1.map label, ids.2.2.map label) := by
    simpa [pLabel, tailLabel, ids] using
      (selected_pair_slots_map label upperLabel D A yz p tail)
  have hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1) :=
    canonicalFineBlocks_pairwise word
  have hp₀ : (actualPrimeLabelBlocksWord
      (splitBlocks blocks size 0)).Perm (ids.1.map label) := by
    have hp := canonical_source_split_group_perm
      D A yz upperLabel pLabel tailLabel 0
    simpa [word, blocks, size, hlabel] using hp
  have hp₁ : (actualPrimeLabelBlocksWord
      (splitBlocks blocks size 1)).Perm (ids.2.1.map label) := by
    have hp := canonical_source_split_group_perm
      D A yz upperLabel pLabel tailLabel 1
    simpa [word, blocks, size, hlabel] using hp
  have hp₂ : (actualPrimeLabelBlocksWord
      (splitBlocks blocks size 2)).Perm (ids.2.2.map label) := by
    have hp := canonical_source_split_group_perm
      D A yz upperLabel pLabel tailLabel 2
    simpa [word, blocks, size, hlabel] using hp
  have h₀ := physicalComplexLabelGamma_norm_le_one N hN τ hτ
    (splitBlocks blocks size 0)
    (splitBlocks_pairwise blocks size 0 hpair)
    (ids.1.map label) hp₀ (positionalGroupMode eta U ids.1)
    (fun ps _ => positionalGroupMode_norm_le_one eta U ids.1 ps) a
  have h₁ := physicalComplexLabelGamma_norm_le_one N hN τ hτ
    (splitBlocks blocks size 1)
    (splitBlocks_pairwise blocks size 1 hpair)
    (ids.2.1.map label) hp₁ (positionalGroupMode eta U ids.2.1)
    (fun ps _ => positionalGroupMode_norm_le_one eta U ids.2.1 ps) b
  have h₂ := physicalComplexLabelGamma_norm_le_one N hN τ hτ
    (splitBlocks blocks size 2)
    (splitBlocks_pairwise blocks size 2 hpair)
    (ids.2.2.map label) hp₂ (positionalGroupMode eta U ids.2.2)
    (fun ps _ => positionalGroupMode_norm_le_one eta U ids.2.2 ps) d
  exact ⟨h₀, h₁, h₂⟩

end
end ImbalancedChen.P3ActualCanonicalFrozenSplitPayment
