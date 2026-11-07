import ImbalancedChen.P3ActualComplexModeFibreTransport
import ImbalancedChen.P3ActualFrozenGroupWords

/-!
P3.6 — genuinely POSITIONAL complex gamma on the ACTUAL frozen group words.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

A permutation of label WORDS does not preserve an arbitrary positional
Fourier multiplier on the corresponding ordered prime tuples.  Consequently
the original reconstructed splitBlocks gamma may NOT be fed a multiplier
defined on a differently ordered physical group.  This file keeps each
actual physical frozen word as its own tuple box, but uses the reconstructed
group's ORIGINAL repeated-label factorial.  The real unweighted fibre
cardinality is transported by the already proved label-word permutation;
the complex positional multiplier itself is never permuted.

This is a strict internal finite group bound, NOT the physical W_T Fourier
representation, a three-mode product tensor, a PP estimate, or an (M) proof.
-/

namespace ImbalancedChen.P3ActualFrozenComplexGroupGamma
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualComplexModeFibreTransport
open ImbalancedChen.P3ActualFrozenGroupWords
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P3ActualFineLabelThreeGammaTensor
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- The physical word, not a surrogate word, determines which ordered
positions a complex Fourier mode sees. Its normalization is the genuine
factorial of the reconstructed per-label blocks. -/
def physicalComplexLabelGamma (B : ℕ → Finset ℕ)
    (word : List ℕ) (blocks : List (ℕ × ℕ))
    (v : List ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ ps ∈ (actualPrimeSlotBox B word).filter
      (fun ps => ps.prod = n), v ps) /
    (actualPrimeLabelBlocksFactorial blocks : ℂ)

/-- Exact physical-word product-fibre transport, without any label
permutation of v or any product-only/symmetric-multiplier premise. -/
theorem physicalComplexLabelGamma_sum_by_product
    (B : ℕ → Finset ℕ) (word : List ℕ)
    (blocks : List (ℕ × ℕ))
    (v : List ℕ → ℂ) (H : ℕ → ℂ) :
    (∑ ps ∈ actualPrimeSlotBox B word, v ps * H ps.prod) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ) =
    ∑ n ∈ (actualPrimeSlotBox B word).image List.prod,
      physicalComplexLabelGamma B word blocks v n * H n := by
  let S := actualPrimeSlotBox B word
  change (∑ ps ∈ S, v ps * H ps.prod) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ) =
    ∑ n ∈ S.image List.prod,
      physicalComplexLabelGamma B word blocks v n * H n
  rw [complex_weighted_sum_by_product S v H, ← Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [physicalComplexLabelGamma]
  ring

/-- The ORIGINAL word permutation controls only the UNWEIGHTED fibre
count. No coordinate permutation of an arbitrary complex v is asserted. -/
theorem physical_fibre_card_eq_of_word_perm
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (word : List ℕ)
    (hp : (actualPrimeLabelBlocksWord blocks).Perm word)
    (n : ℕ) :
    ((actualPrimeSlotBox B word).filter
      (fun ps => ps.prod = n)).card =
    ((actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).filter
      (fun ps => ps.prod = n)).card := by
  let T := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  let S := actualPrimeSlotBox B word
  have htest :=
    actualPrimeSlotBox_product_sum_perm B hp
      (fun m => if m = n then (1 : ℝ) else 0)
  have hreal :
      (((T.filter (fun ps => ps.prod = n)).card : ℝ)) =
      (((S.filter (fun ps => ps.prod = n)).card : ℝ)) := by
    simpa [T, S, Finset.sum_ite] using htest
  exact_mod_cast hreal.symm

/-- Positional COMPLEX physical gamma is dominated by the true original
fine-label gamma. The old unweighted permutation supplies the fibre
cardinality, while the mode remains on the actual ordered physical word. -/
theorem physicalComplexLabelGamma_norm_le_original_gamma
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (word : List ℕ)
    (hp : (actualPrimeLabelBlocksWord blocks).Perm word)
    (v : List ℕ → ℂ)
    (hv : ∀ ps ∈ actualPrimeSlotBox B word, ‖v ps‖ ≤ 1)
    (n : ℕ) :
    ‖physicalComplexLabelGamma B word blocks v n‖ ≤ gamma B blocks n := by
  let S := actualPrimeSlotBox B word
  let F := S.filter (fun ps => ps.prod = n)
  let G := (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).filter
      (fun ps => ps.prod = n)
  have hmass : ‖∑ ps ∈ F, v ps‖ ≤ (F.card : ℝ) := by
    calc
      _ ≤ ∑ ps ∈ F, ‖v ps‖ := norm_sum_le _ _
      _ ≤ ∑ ps ∈ F, (1 : ℝ) :=
        Finset.sum_le_sum (by
          intro ps hps
          exact hv ps (Finset.mem_filter.mp hps).1)
      _ = (F.card : ℝ) := by simp
  have hcount : F.card = G.card := by
    exact physical_fibre_card_eq_of_word_perm B blocks word hp n
  have hM : (0 : ℝ) <
      (actualPrimeLabelBlocksFactorial blocks : ℝ) := by
    exact_mod_cast actualPrimeLabelBlocksFactorial_pos blocks
  have hnormM :
      ‖(actualPrimeLabelBlocksFactorial blocks : ℂ)‖ =
        (actualPrimeLabelBlocksFactorial blocks : ℝ) := by simp
  change ‖(∑ ps ∈ F, v ps) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ)‖ ≤
    (G.card : ℝ) / (actualPrimeLabelBlocksFactorial blocks : ℝ)
  rw [norm_div, hnormM, ← hcount]
  exact (div_le_div_iff_of_pos_right hM).2 hmass

/-- Half-open, disjoint actual prime labels promote the literal positional
complex norm bound to one, even for repeated slots and product collisions. -/
theorem physicalComplexLabelGamma_norm_le_one
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (blocks : List (ℕ × ℕ))
    (hlabels : blocks.Pairwise (fun b d => b.1 ≠ d.1))
    (word : List ℕ)
    (hp : (actualPrimeLabelBlocksWord blocks).Perm word)
    (v : List ℕ → ℂ)
    (hv : ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ) word, ‖v ps‖ ≤ 1)
    (n : ℕ) :
    ‖physicalComplexLabelGamma
      (actualPrimeFineLabelFinset N τ) word blocks v n‖ ≤ 1 := by
  exact (physicalComplexLabelGamma_norm_le_original_gamma
    (actualPrimeFineLabelFinset N τ) blocks word hp v hv n).trans
      (fine_gamma_mem_Icc N hN τ hτ blocks hlabels n).2

/-- All three ACTUAL frozen output lists are bounded with THEIR actual
ordered positional mode and reconstructed M_j. We DO NOT transport any
position-dependent v through the word permutation. -/
theorem actual_frozen_three_physical_complex_gamma_bounds
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ))
    (hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1))
    (hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail)
    (v₀ v₁ v₂ : List ℕ → ℂ)
    (hv₀ : ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualFrozenSelectedPairSlots D A yz upper p tail).1,
        ‖v₀ ps‖ ≤ 1)
    (hv₁ : ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualFrozenSelectedPairSlots D A yz upper p tail).2.1,
        ‖v₁ ps‖ ≤ 1)
    (hv₂ : ∀ ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualFrozenSelectedPairSlots D A yz upper p tail).2.2,
        ‖v₂ ps‖ ≤ 1)
    (n₀ n₁ n₂ : ℕ) :
    let size := actualFrozenSplitSize D A yz upper p tail
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    let B := actualPrimeFineLabelFinset N τ
    (‖physicalComplexLabelGamma B groups.1
      (splitBlocks blocks size 0) v₀ n₀‖ ≤ 1) ∧
    (‖physicalComplexLabelGamma B groups.2.1
      (splitBlocks blocks size 1) v₁ n₁‖ ≤ 1) ∧
    (‖physicalComplexLabelGamma B groups.2.2
      (splitBlocks blocks size 2) v₂ n₂‖ ≤ 1) := by
  obtain ⟨hp₀, hp₁, hp₂⟩ :=
    actual_frozen_group_words_perm D A yz upper p tail
      blocks hpair hword
  dsimp only
  exact ⟨physicalComplexLabelGamma_norm_le_one
      N hN τ hτ _
      (splitBlocks_pairwise blocks
        (actualFrozenSplitSize D A yz upper p tail) 0 hpair)
      _ hp₀ v₀ hv₀ n₀,
    physicalComplexLabelGamma_norm_le_one
      N hN τ hτ _
      (splitBlocks_pairwise blocks
        (actualFrozenSplitSize D A yz upper p tail) 1 hpair)
      _ hp₁ v₁ hv₁ n₁,
    physicalComplexLabelGamma_norm_le_one
      N hN τ hτ _
      (splitBlocks_pairwise blocks
        (actualFrozenSplitSize D A yz upper p tail) 2 hpair)
      _ hp₂ v₂ hv₂ n₂⟩

end
end ImbalancedChen.P3ActualFrozenComplexGroupGamma
