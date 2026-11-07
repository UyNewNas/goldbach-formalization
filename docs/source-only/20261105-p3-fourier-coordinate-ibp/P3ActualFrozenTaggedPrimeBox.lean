import ImbalancedChen.P3ActualFrozenTaggedPrimeModes
import ImbalancedChen.P3ActualFrozenComplexGroupGamma

/-!
P3.6 / pinned manuscript §4 (F), SOURCE_ONLY / UNCOMPILED /
KERNEL_UNVERIFIED.

A provenance-preserving bridge from ORIGINAL Fin n prime-slot identifiers
to the full untagged ordered prime box used by physicalComplexLabelGamma.
The bridge is equality of the WHOLE finite boxes, not only of realized
tuples, and never permutes a position-dependent Fourier multiplier.

The prime-label map is supplied explicitly and still needs identification
with the complete original PP atom compiler. No arithmetic estimate, rho
identification, continuous Fourier admission or external input is asserted.
-/

namespace ImbalancedChen.P3ActualFrozenTaggedPrimeBox
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3ActualFrozenComplexGroupGamma

/-- The ordered prime box on original slot IDs is definitionally the
same complete box as the ordered prime box on their original labels.
This is valid for repeated labels and for empty slot words. -/
theorem prime_box_relabel {n : ℕ}
    (B : ℕ → Finset ℕ) (label : Fin n → ℕ)
    (ids : List (Fin n)) :
    actualPrimeSlotBox (fun i : Fin n => B (label i)) ids =
      actualPrimeSlotBox B (ids.map label) := by
  induction ids with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.map_cons, actualPrimeSlotBox, ih]

/-- A genuine assignment satisfying each original slot's prime-label
membership produces an element of the full ordered slot box. Different
original IDs may carry equal prime values. -/
theorem realized_prime_box_mem {n : ℕ}
    (B : Fin n → Finset ℕ) (ids : List (Fin n))
    (values : Fin n → ℕ)
    (hmem : ∀ i ∈ ids, values i ∈ B i) :
    ids.map values ∈ actualPrimeSlotBox B ids := by
  induction ids with
  | nil =>
      simp [actualPrimeSlotBox]
  | cons i rest ih =>
      have hi : values i ∈ B i := hmem i (by simp)
      have hr : ∀ j ∈ rest, values j ∈ B j := by
        intro j hj
        exact hmem j (by simp [hj])
      change (values i :: rest.map values) ∈
        ((B i).product (actualPrimeSlotBox B rest)).image
          (fun pq => pq.1 :: pq.2)
      exact Finset.mem_image.mpr
        ⟨(values i, rest.map values),
          Finset.mem_product.mpr ⟨hi, ih hr⟩, rfl⟩

/-- All three ACTUAL frozen original-ID words give admissible ordered
physical prime tuples under the identical original label map. No tuple
sorting, new group choice or value-level injectivity is used. -/
theorem frozen_realized_three_prime_boxes {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (B : ℕ → Finset ℕ) (label : Fin n → ℕ)
    (values : Fin n → ℕ)
    (hmem : ∀ i, values i ∈ B (label i)) :
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (groups.1.map values ∈ actualPrimeSlotBox B (groups.1.map label)) ∧
    (groups.2.1.map values ∈ actualPrimeSlotBox B (groups.2.1.map label)) ∧
    (groups.2.2.map values ∈ actualPrimeSlotBox B (groups.2.2.map label)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [← prime_box_relabel B label _]
    exact realized_prime_box_mem (fun i => B (label i)) _ values
      (by intro i hi; exact hmem i)
  · rw [← prime_box_relabel B label _]
    exact realized_prime_box_mem (fun i => B (label i)) _ values
      (by intro i hi; exact hmem i)
  · rw [← prime_box_relabel B label _]
    exact realized_prime_box_mem (fun i => B (label i)) _ values
      (by intro i hi; exact hmem i)

/-- The frozen source words have precisely the original full prime
product, without identifying values at distinct source IDs. -/
theorem frozen_realized_complete_product {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (values : Fin n → ℕ) :
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (groups.1.map values).prod *
      (groups.2.1.map values).prod *
        (groups.2.2.map values).prod =
    ((p 0 :: p 1 :: p 2 :: tail).map values).prod := by
  have hp := (actualFrozenSelectedPairSlots_perm
    D A yz upper p tail).map values
  simpa only [List.map_append, List.prod_append, mul_assoc] using hp.prod_eq

/-- The three actual ID words preserve every original label occurrence,
not merely the total number of prime variables. The induced label words
need not be the output of a separately run label-level frozen allocator. -/
theorem frozen_original_labels_perm {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (label : Fin n → ℕ) :
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (groups.1.map label ++ groups.2.1.map label ++
       groups.2.2.map label).Perm
      ((p 0 :: p 1 :: p 2 :: tail).map label) := by
  have hp := (actualFrozenSelectedPairSlots_perm
    D A yz upper p tail).map label
  simpa only [List.map_append] using hp

/-- A physical complex gamma on an untagged label word is EXACTLY the
original-ID ordered prime-box fibre with the constructed positional mode.
No identity between different positional permutations is used. -/
theorem positional_gamma_original_ID_fibre {n : ℕ}
    (B : ℕ → Finset ℕ) (label : Fin n → ℕ)
    (ids : List (Fin n)) (blocks : List (ℕ × ℕ))
    (eta U : Fin n → ℝ) (product : ℕ) :
    physicalComplexLabelGamma B (ids.map label) blocks
      (positionalGroupMode eta U ids) product =
    (∑ ps ∈ (actualPrimeSlotBox
        (fun i : Fin n => B (label i)) ids).filter
        (fun ps => ps.prod = product),
          positionalGroupMode eta U ids ps) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ) := by
  unfold physicalComplexLabelGamma
  rw [← prime_box_relabel B label ids]

/-- Once the honest original repeated-label block word has been
identified with this actual label word, its existing gamma bound applies
directly to the CONSTRUCTED ID-aware Fourier multiplier. That dictionary
equality/permutation is not supplied here for arbitrary PP atoms. -/
theorem positional_gamma_norm_le_one_of_original_dictionary {n : ℕ}
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (label : Fin n → ℕ) (ids : List (Fin n))
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : (actualPrimeLabelBlocksWord blocks).Perm (ids.map label))
    (eta U : Fin n → ℝ) (product : ℕ) :
    ‖physicalComplexLabelGamma (actualPrimeFineLabelFinset N τ)
        (ids.map label) blocks (positionalGroupMode eta U ids) product‖ ≤ 1 := by
  exact physicalComplexLabelGamma_norm_le_one
    N hN τ hτ blocks hpair (ids.map label) hword
    (positionalGroupMode eta U ids)
    (fun ps _ => positionalGroupMode_norm_le_one eta U ids ps) product

end
end ImbalancedChen.P3ActualFrozenTaggedPrimeBox
