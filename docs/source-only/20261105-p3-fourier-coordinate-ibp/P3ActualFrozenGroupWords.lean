import ImbalancedChen.P3ActualFrozenSlotLabelCounts
import ImbalancedChen.P3ActualFineLabelThreeGammaTensor

/-!
P3.6 original frozen SINGLE-occurrence label groups -> reconstructed
per-label split blocks, retaining the ORIGINAL full product and exact
M_all. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The computed frozen lists are fixed from upper endpoints, not from
individual prime values. We prove that each actual output label word
permutes its reconstructed split-block word, even when a repeated
original label is divided among several groups. The remaining equality
of the *physical* input word to the original block expansion is stated
explicitly; it still has to be derived from the full PP compiler.
No assumptions about rho, coprime means, error estimates or (M).
-/

namespace ImbalancedChen.P3ActualFrozenGroupWords
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P3ActualFineLabelThreeGammaTensor

/-- Changing only the multiplicity of each distinct original label
preserves pairwise distinctness of labels in a fixed group. -/
theorem splitBlocks_pairwise
    (blocks : List (ℕ × ℕ)) (size : ℕ → Fin 3 → ℕ)
    (j : Fin 3)
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1)) :
    (splitBlocks blocks size j).Pairwise (fun b c => b.1 ≠ c.1) := by
  induction blocks with
  | nil =>
      simp [splitBlocks]
  | cons hd tl ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      change ((hd.1, size hd.1 j) :: splitBlocks tl size j).Pairwise
        (fun b c => b.1 ≠ c.1)
      apply List.pairwise_cons.mpr
      constructor
      · intro c hc
        rcases List.mem_map.mp hc with ⟨orig, hm, rfl⟩
        exact hhead orig hm
      · exact ih htail

/-- An actual split-block word contains exactly the computed number
of occurrences of an original label. Zero multiplicities are allowed. -/
theorem split_word_count_of_member
    (blocks : List (ℕ × ℕ)) (size : ℕ → Fin 3 → ℕ)
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (i m : ℕ) (hm : (i, m) ∈ blocks) (j : Fin 3) :
    (actualPrimeLabelBlocksWord (splitBlocks blocks size j)).count i =
      size i j := by
  have hsplit :
      (i, size i j) ∈ splitBlocks blocks size j :=
    List.mem_map.mpr ⟨(i, m), hm, rfl⟩
  calc
    _ = blockLabelCount (splitBlocks blocks size j) i :=
      expanded_word_count _ _
    _ = size i j :=
      blockLabelCount_of_pairwise_mem
        (splitBlocks blocks size j)
        (splitBlocks_pairwise blocks size j hpair) hsplit

/-- A label not in the original dictionary is absent from every
reconstructed split-block word. -/
theorem split_word_count_of_absent
    (blocks : List (ℕ × ℕ)) (size : ℕ → Fin 3 → ℕ)
    (i : ℕ) (haway : ∀ b ∈ blocks, b.1 ≠ i) (j : Fin 3) :
    (actualPrimeLabelBlocksWord (splitBlocks blocks size j)).count i = 0 := by
  rw [expanded_word_count]
  apply blockLabelCount_zero_of_away
  intro b hb
  rcases List.mem_map.mp hb with ⟨orig, hm, rfl⟩
  exact haway orig hm

/-- Every reconstructed group has the same per-label counts as the
corresponding ACTUAL frozen group, not only the same total length.

The one remaining dictionary assumption hword identifies the original
expanded label list with the physical frozen allocator input. -/
theorem actual_frozen_split_word_count
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail)
    (i : ℕ) (j : Fin 3) :
    (actualPrimeLabelBlocksWord
      (splitBlocks blocks (actualFrozenSplitSize D A yz upper p tail) j)).count i =
      actualFrozenSplitSize D A yz upper p tail i j := by
  by_cases hmem : ∃ m : ℕ, (i, m) ∈ blocks
  · obtain ⟨m, hm⟩ := hmem
    exact split_word_count_of_member blocks
      (actualFrozenSplitSize D A yz upper p tail)
      hpair i m hm j
  · have haway : ∀ b ∈ blocks, b.1 ≠ i := by
      intro b hb heq
      rcases b with ⟨k, m⟩
      change k = i at heq
      subst k
      exact hmem ⟨m, hb⟩
    have hsourcezero : (actualPrimeLabelBlocksWord blocks).count i = 0 := by
      rw [expanded_word_count]
      exact blockLabelCount_zero_of_away blocks i haway
    have hmass := actualFrozenSplitSize_sum D A yz upper p tail i
    rw [← hword, hsourcezero] at hmass
    have hzero : actualFrozenSplitSize D A yz upper p tail i j = 0 := by
      fin_cases j <;> omega
    calc
      _ = 0 := split_word_count_of_absent blocks
        (actualFrozenSplitSize D A yz upper p tail) i haway j
      _ = actualFrozenSplitSize D A yz upper p tail i j := hzero.symm

/-- Three genuine whole-box output groups, with literal label
multiplicities and positions, are each permutations of the corresponding
computed split-block word. This also covers repeated labels split across
two or three groups. -/
theorem actual_frozen_group_words_perm
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail) :
    let size := actualFrozenSplitSize D A yz upper p tail
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (actualPrimeLabelBlocksWord (splitBlocks blocks size 0)).Perm groups.1 ∧
    (actualPrimeLabelBlocksWord (splitBlocks blocks size 1)).Perm groups.2.1 ∧
    (actualPrimeLabelBlocksWord (splitBlocks blocks size 2)).Perm groups.2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · apply List.perm_iff_count.mpr
    intro i
    simpa [actualFrozenSplitSize] using
      (actual_frozen_split_word_count D A yz upper p tail blocks hpair hword i 0)
  · apply List.perm_iff_count.mpr
    intro i
    simpa [actualFrozenSplitSize] using
      (actual_frozen_split_word_count D A yz upper p tail blocks hpair hword i 1)
  · apply List.perm_iff_count.mpr
    intro i
    simpa [actualFrozenSplitSize] using
      (actual_frozen_split_word_count D A yz upper p tail blocks hpair hword i 2)

/-- The source's *physical* frozen groups preserve the exact original
complete integer product in an arbitrary finite labelled-prime box.
This is a RAW fibre identity; it does not replace the normalized gamma
coefficient or the exact coprime mean. -/
theorem actual_frozen_physical_three_product_sum
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail)
    (H : ℕ → ℝ) :
    let B := actualPrimeFineLabelFinset N τ
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
      H ps.prod) =
    ∑ ps ∈ actualPrimeSlotBox B groups.1,
      ∑ qs ∈ actualPrimeSlotBox B groups.2.1,
        ∑ rs ∈ actualPrimeSlotBox B groups.2.2,
          H (ps.prod * qs.prod * rs.prod) := by
  let B := actualPrimeFineLabelFinset N τ
  have hperm : (actualPrimeLabelBlocksWord blocks).Perm
      ((actualFrozenSelectedPairSlots D A yz upper p tail).1 ++
       (actualFrozenSelectedPairSlots D A yz upper p tail).2.1 ++
       (actualFrozenSelectedPairSlots D A yz upper p tail).2.2) := by
    rw [hword]
    exact (actualFrozenSelectedPairSlots_perm D A yz upper p tail).symm
  rw [actualPrimeSlotBox_product_sum_perm B hperm H]
  rw [actualPrimeSlotBox_product_sum_append]
  simp_rw [actualPrimeSlotBox_product_sum_append]
  simp only [mul_assoc]

end
end ImbalancedChen.P3ActualFrozenGroupWords
