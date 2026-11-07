import ImbalancedChen.P3ActualFrozenTaggedPrimeBox
import ImbalancedChen.P3ActualSortedFineSourceGamma

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
The ACTUAL endpoint-frozen selected-pair partition commutes with a
possibly NONINJECTIVE original-slot-ID -> fine-label map, provided the
numeric upper endpoints are pulled back along that same map.

This is not a permutation of positional Fourier weights: only the
underlying slot WORDS are mapped. Original Fin n IDs stay attached to
each frequency in positionalGroupMode. For the genuine weakly ordered
fine-source word, the ORIGINAL run-length blocks are computed rather
than supplied as a circular dictionary hypothesis. The three complex
gamma one-bounds then apply to the actual ID-ordered prime groups.

No assertion covers all high-rank/marked/HB atoms, arbitrary W_T
continuous Fourier inversion, physical rho_T or PP discrepancy.
-/

namespace ImbalancedChen.P3ActualFrozenTaggedLabelCompiler
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualFrozenGroupWords
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- Naturality of the GENUINE selected-pair endpoint allocator, including
both the capacity-success and full-vector-repair branches. No
injectivity of f: repeated labels remain separate source occurrences.
The decisions depend on upper ∘ f, not on prime values or error signs. -/
theorem selected_pair_slots_map {α β : Type*}
    (f : α → β) (upper : β → ℕ)
    (D A : ℝ) (yz : Bool)
    (p : Fin 3 → α) (tail : List α) :
    actualFrozenSelectedPairSlots D A yz upper
        (fun j => f (p j)) (tail.map f) =
      let original := actualFrozenSelectedPairSlots D A yz
        (fun i => upper (f i)) p tail
      (original.1.map f, original.2.1.map f, original.2.2.map f) := by
  cases yz <;>
    simp [actualFrozenSelectedPairSlots, actualTwoCapacityGreedy_map]

/-- A tagged original-ID source computes exactly the same three LABEL
words as running the pinned allocator on the mapped fine-label source.
This is not a claim of injectivity of the original label map. -/
theorem frozen_original_ID_label_words {n : ℕ}
    (D A : ℝ) (yz : Bool) (upperLabel : ℕ → ℕ)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n)) :
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    actualFrozenSelectedPairSlots D A yz upperLabel
        (fun j => label (p j)) (tail.map label) =
      (ids.1.map label, ids.2.1.map label, ids.2.2.map label) := by
  exact selected_pair_slots_map label upperLabel D A yz p tail

/-- On the REAL weakly descending fine-source word, neither a
repeated-label block dictionary nor its permutation is postulated.
Run-length blocks are obtained from the original source itself.

The old physical gamma lemma is applied to the ACTUAL tagged groups
using the exact label-group naturality above. Each Fourier multiplier
retains its ordered original IDs; two equal fine labels can have
different frequencies. This is a local coefficient bound, not PP. -/
theorem actual_sorted_ID_three_positional_gamma_bounds {n : ℕ}
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n))
    (horder : ((p 0 :: p 1 :: p 2 :: tail).map label).Pairwise (· ≥ ·))
    (eta U : Fin n → ℝ) (a b d : ℕ) :
    let pLabel : Fin 3 → ℕ := fun j => label (p j)
    let tailLabel := tail.map label
    let word := pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel
    let blocks := actualPrimeFineLabelBlocksOfWord word
    let upperLabel := actualPrimeFineLabelIntegerUpper N τ
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let size := actualFrozenSplitSize D A yz upperLabel pLabel tailLabel
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
  let tailLabel : List ℕ := tail.map label
  let word : List ℕ := pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel
  let blocks := actualPrimeFineLabelBlocksOfWord word
  let upperLabel := actualPrimeFineLabelIntegerUpper N τ
  let ids := actualFrozenSelectedPairSlots D A yz
    (fun i => upperLabel (label i)) p tail
  have hsorted : word.Pairwise (· ≥ ·) := by
    simpa [word, pLabel, tailLabel, List.map_cons] using horder
  have hpair : blocks.Pairwise (fun x y => x.1 ≠ y.1) :=
    (actualPrimeFineLabelBlocksOfWord_order word hsorted).imp
      (fun h => Nat.ne_of_gt h)
  have hword : actualPrimeLabelBlocksWord blocks =
      pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel := by
    simpa [blocks, word] using actualPrimeFineLabelBlocksOfWord_word word
  have hbound := actual_frozen_three_physical_complex_gamma_bounds
    N hN τ hτ D A yz upperLabel pLabel tailLabel
    blocks hpair hword
    (positionalGroupMode eta U ids.1)
    (positionalGroupMode eta U ids.2.1)
    (positionalGroupMode eta U ids.2.2)
    (by intro ps _; exact positionalGroupMode_norm_le_one eta U ids.1 ps)
    (by intro ps _; exact positionalGroupMode_norm_le_one eta U ids.2.1 ps)
    (by intro ps _; exact positionalGroupMode_norm_le_one eta U ids.2.2 ps)
    a b d
  have hlabelMap :
      actualFrozenSelectedPairSlots D A yz upperLabel pLabel tailLabel =
        (ids.1.map label, ids.2.1.map label, ids.2.2.map label) := by
    simpa [ids, pLabel, tailLabel] using
      (selected_pair_slots_map label upperLabel D A yz p tail)
  rw [hlabelMap] at hbound
  simpa [pLabel, tailLabel, word, blocks, upperLabel, ids]
    using hbound

end
end ImbalancedChen.P3ActualFrozenTaggedLabelCompiler
