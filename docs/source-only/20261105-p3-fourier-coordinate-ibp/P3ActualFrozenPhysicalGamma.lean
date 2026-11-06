import ImbalancedChen.P3ActualFrozenGroupWords

/-!
P3.6: the literal three groups of the ORIGINAL endpoint-frozen
single-occurrence allocator now receive the exact normalized fine-label
gamma weighted sums, with ORIGINAL per-label group factorials.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
The source dictionary `hword` has not yet been produced for every actual
physical PP atom; this file neither assumes nor proves a same-rho PP estimate.
A raw product fibre sum is NOT a relative fibre bound.
-/

namespace ImbalancedChen.P3ActualFrozenPhysicalGamma
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3ActualFrozenGroupWords
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- A permutation of ORIGINAL slot labels transfers its normalized
full-product fibre sum. The divisor is the product of ORIGINAL repeated
label factorials, not the factorial of the total number of slots.
This is an exact finite identity for every test function H. -/
theorem normalized_group_sum_of_word_perm
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ)) (word : List ℕ)
    (hp : (actualPrimeLabelBlocksWord blocks).Perm word)
    (H : ℕ → ℝ) :
    (∑ ps ∈ actualPrimeSlotBox B word, H ps.prod) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ) =
    ∑ n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).image List.prod,
      gamma B blocks n * H n := by
  let T := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  have hperm := actualPrimeSlotBox_product_sum_perm B hp H
  calc
    _ = (∑ ps ∈ T, H ps.prod) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) :=
      congrArg (fun v : ℝ => v / (actualPrimeLabelBlocksFactorial blocks : ℝ))
        hperm.symm
    _ = (∑ n ∈ T.image List.prod,
          (actualPrimeTupleCoefficient T n : ℝ) * H n) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) :=
      congrArg (fun v : ℝ => v / (actualPrimeLabelBlocksFactorial blocks : ℝ))
        (actualPrimeTuple_sum_by_product T H)
    _ = _ := by
      rw [← Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [gamma]
      ring

/-- All three ACTUAL frozen output words have the same normalized
product-sum coefficients as their independently reconstructed split blocks.
Crucially, the denominator in each component is its own genuine M_j.
Equal full products retain their complete finite-fibre multiplicities. -/
theorem actual_frozen_three_group_normalized_sums
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail)
    (F₀ F₁ F₂ : ℕ → ℝ) :
    let B := actualPrimeFineLabelFinset N τ
    let size := actualFrozenSplitSize D A yz upper p tail
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    ((∑ ps ∈ actualPrimeSlotBox B groups.1, F₀ ps.prod) /
        (actualPrimeLabelBlocksFactorial g₀ : ℝ) =
      ∑ n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)).image List.prod,
        gamma B g₀ n * F₀ n) ∧
    ((∑ ps ∈ actualPrimeSlotBox B groups.2.1, F₁ ps.prod) /
        (actualPrimeLabelBlocksFactorial g₁ : ℝ) =
      ∑ n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)).image List.prod,
        gamma B g₁ n * F₁ n) ∧
    ((∑ ps ∈ actualPrimeSlotBox B groups.2.2, F₂ ps.prod) /
        (actualPrimeLabelBlocksFactorial g₂ : ℝ) =
      ∑ n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)).image List.prod,
        gamma B g₂ n * F₂ n) := by
  obtain ⟨h₀, h₁, h₂⟩ :=
    actual_frozen_group_words_perm D A yz upper p tail blocks hpair hword
  dsimp only
  exact ⟨normalized_group_sum_of_word_perm
      (actualPrimeFineLabelFinset N τ) _ _ h₀ F₀,
    normalized_group_sum_of_word_perm
      (actualPrimeFineLabelFinset N τ) _ _ h₁ F₁,
    normalized_group_sum_of_word_perm
      (actualPrimeFineLabelFinset N τ) _ _ h₂ F₂⟩

/-- The THREE LITERAL frozen physical boxes (not arbitrary split-group
surrogates) yield the exact original signed normalized gamma tensor.
Original M_all, the computed M_j, all collisions and the complete
integer product are retained. This does not supply hword for every
physical PP source, any modulus estimate or its exact coprime mean. -/
theorem actual_frozen_physical_three_gamma_tensor
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail)
    (c : ℝ) (H : ℕ → ℝ) :
    let B := actualPrimeFineLabelFinset N τ
    let size := actualFrozenSplitSize D A yz upper p tail
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
      (∑ ps ∈ actualPrimeSlotBox B groups.1,
        ∑ qs ∈ actualPrimeSlotBox B groups.2.1,
          ∑ rs ∈ actualPrimeSlotBox B groups.2.2,
            H (ps.prod * qs.prod * rs.prod)) =
    (c * (((actualPrimeLabelBlocksFactorial g₀ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₁ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₂ : ℝ)) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ))) *
    (∑ a ∈ T₀.image List.prod, ∑ b ∈ T₁.image List.prod,
      ∑ d ∈ T₂.image List.prod,
        gamma B g₀ a * gamma B g₁ b * gamma B g₂ d *
        H (a * b * d)) := by
  have hraw := actual_frozen_physical_three_product_sum
    N τ D A yz upper p tail blocks hword H
  have hgamma := actual_frozen_slot_split_three_gamma_tensor
    N τ D A yz upper p tail blocks hpair hword c H
  exact (congrArg
    (fun v : ℝ => (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) * v)
    hraw).symm.trans hgamma

end
end ImbalancedChen.P3ActualFrozenPhysicalGamma
