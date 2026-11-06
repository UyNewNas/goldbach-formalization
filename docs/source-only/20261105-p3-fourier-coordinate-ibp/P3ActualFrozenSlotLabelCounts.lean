import ImbalancedChen.P3ActualSplitLabelMultinomial
import Mathlib.Data.List.Count

/-!
P3.6: recover ORIGINAL per-label multiplicities from the ACTUAL frozen
single-occurrence partition, including repeated labels split between groups.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
The frozen allocator acts on individual occurrence labels, not artificially
unsplit prime-label blocks. Its capacity decisions depend on the fixed
upper vector, never on a particular product value or error sign.

A source-level word equality is explicitly required: it identifies the
three frozen input slots and tail with the true original expanded block
word. It is a finite source-dictionary obligation, NOT a PP estimate.
No same-rho arithmetic discrepancy, endpoint or Fourier claim is made.
-/

namespace ImbalancedChen.P3ActualFrozenSlotLabelCounts
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P3ActualFineLabelThreeGammaTensor

/-- Raw multiplicity of a label in original *blocks*. This deliberately
sums all blocks, so no distinct-label premise is hidden in the definition. -/
def blockLabelCount : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (j, m) :: rest, i => (if i = j then m else 0) + blockLabelCount rest i

/-- Expanding the actual repeated-label word preserves each label's exact
occurrence count, including zero-multiplicity blocks. -/
theorem expanded_word_count (blocks : List (ℕ × ℕ)) (i : ℕ) :
    (actualPrimeLabelBlocksWord blocks).count i = blockLabelCount blocks i := by
  induction blocks with
  | nil =>
      simp [actualPrimeLabelBlocksWord, blockLabelCount]
  | cons b rest ih =>
      rcases b with ⟨j, m⟩
      simp only [actualPrimeLabelBlocksWord, List.flatMap_cons,
        List.count_append, List.count_replicate, blockLabelCount]
      rw [ih]

/-- A label absent from every block has zero expanded occurrence mass.
No global distinctness is needed for this elementary fact. -/
theorem blockLabelCount_zero_of_away (blocks : List (ℕ × ℕ)) (i : ℕ)
    (h : ∀ b ∈ blocks, b.1 ≠ i) : blockLabelCount blocks i = 0 := by
  revert h
  induction blocks with
  | nil =>
      intro _
      rfl
  | cons b rest ih =>
      intro h
      rcases b with ⟨j, m⟩
      have hne : i ≠ j := (h (j, m) (by simp)).symm
      have hrest : ∀ b ∈ rest, b.1 ≠ i := by
        intro b hb
        exact h b (List.mem_cons_of_mem (j, m) hb)
      simp [blockLabelCount, hne, ih hrest]

/-- For a genuinely distinct-label block dictionary, an original
(label,m) block contributes exactly m slots of that label. -/
theorem blockLabelCount_of_pairwise_mem
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    {i m : ℕ} (hmem : (i, m) ∈ blocks) :
    blockLabelCount blocks i = m := by
  revert hpair hmem
  induction blocks with
  | nil =>
      intro _ hmem
      cases hmem
  | cons b rest ih =>
      intro hpair hmem
      rcases b with ⟨j, n⟩
      obtain ⟨hcross, htail⟩ := List.pairwise_cons.mp hpair
      rcases List.mem_cons.mp hmem with hhead | hrest
      · cases hhead
        have hz : blockLabelCount rest j = 0 :=
          blockLabelCount_zero_of_away rest j (fun b hb => hcross b hb)
        simp [blockLabelCount, hz]
      · have hij : i ≠ j := by
          intro heq
          exact (hcross (i, m) hrest) heq.symm
        have hr : blockLabelCount rest i = m := ih htail hrest
        simp [blockLabelCount, hij, hr]

/-- The ORIGINAL block multiplicity is recovered from its actual expanded
word. This is stronger than merely preserving total slot length. -/
theorem original_block_size_eq_word_count
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    {i m : ℕ} (hmem : (i, m) ∈ blocks) :
    m = (actualPrimeLabelBlocksWord blocks).count i := by
  rw [expanded_word_count]
  exact (blockLabelCount_of_pairwise_mem blocks hpair hmem).symm

/-- Counts are read from the three ACTUAL output slot lists of the
original, endpoint-frozen selected-pair algorithm. -/
def actualFrozenSplitSize
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (i : ℕ) (j : Fin 3) : ℕ :=
  let g := actualFrozenSelectedPairSlots D A yz upper p tail
  if j = 0 then g.1.count i
  else if j = 1 then g.2.1.count i
  else g.2.2.count i

/-- The real frozen allocator conserves *each* fine-label count.
No per-group count is supplied as an extra hypothesis. -/
theorem actualFrozenSplitSize_sum
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ) (i : ℕ) :
    (p 0 :: p 1 :: p 2 :: tail).count i =
      actualFrozenSplitSize D A yz upper p tail i 0 +
      actualFrozenSplitSize D A yz upper p tail i 1 +
      actualFrozenSplitSize D A yz upper p tail i 2 := by
  simpa [actualFrozenSplitSize] using
    (frozen_occurrence_count_sum D A yz upper p tail i)

/-- SOURCE-DICTIONARY BOUNDARY: the physical input word is exactly
the original fully expanded repeated-label source, not a chosen
subsequence. The given finite equality is NOT a discrepancy hypothesis.
Under this explicit dictionary, actual frozen group counts supply every
per-label multiplicity used in the split factorial lemma. -/
theorem actual_frozen_slot_split_counts
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail) :
    ∀ b ∈ blocks, b.2 =
      actualFrozenSplitSize D A yz upper p tail b.1 0 +
      actualFrozenSplitSize D A yz upper p tail b.1 1 +
      actualFrozenSplitSize D A yz upper p tail b.1 2 := by
  intro b hb
  have hc := original_block_size_eq_word_count blocks hpair hb
  have hf := actualFrozenSplitSize_sum D A yz upper p tail b.1
  rw [← hword] at hf
  exact hc.trans hf

/-- The original signed, full-product prime tensor can now use the
*computed* per-label counts of the actual frozen occurrence partition.
The exact M0*M1*M2/Mall scalar remains present. All prime tuples and
their multiplicities remain in the three gamma convolution.

The sole remaining source-dictionary input is the concrete equality
between the physical frozen input word and the original block expansion.
No caller chooses an arbitrary split-size function. -/
theorem actual_frozen_slot_split_three_gamma_tensor
    (N : ℕ) (τ D A : ℝ) (yz : Bool)
    (upper : ℕ → ℕ) (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail)
    (c : ℝ) (H : ℕ → ℝ) :
    let size := actualFrozenSplitSize D A yz upper p tail
    let B := actualPrimeFineLabelFinset N τ
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
      (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
        H ps.prod) =
      (c * (((actualPrimeLabelBlocksFactorial g₀ : ℝ) *
        (actualPrimeLabelBlocksFactorial g₁ : ℝ) *
        (actualPrimeLabelBlocksFactorial g₂ : ℝ)) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ))) *
      (∑ a ∈ T₀.image List.prod, ∑ b ∈ T₁.image List.prod,
        ∑ d ∈ T₂.image List.prod,
          gamma B g₀ a * gamma B g₁ b * gamma B g₂ d *
          H (a * b * d)) := by
  exact actual_split_three_gamma_tensor N τ blocks
    (actualFrozenSplitSize D A yz upper p tail)
    (actual_frozen_slot_split_counts D A yz upper p tail blocks hpair hword)
    c H

/-- The multinomial correcting scalar for the ACTUAL frozen
single-occurrence groups is paid by the literal split-factorial theorem. -/
theorem actual_frozen_slot_factorial_ratio_mem_Icc
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail) :
    let size := actualFrozenSplitSize D A yz upper p tail
    (((actualPrimeLabelBlocksFactorial (splitBlocks blocks size 0) : ℝ) *
       (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 1) : ℝ) *
       (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 2) : ℝ)) /
       (actualPrimeLabelBlocksFactorial blocks : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  exact split_factorial_ratio_mem_Icc blocks
    (actualFrozenSplitSize D A yz upper p tail)
    (actual_frozen_slot_split_counts D A yz upper p tail blocks hpair hword)

end
end ImbalancedChen.P3ActualFrozenSlotLabelCounts
