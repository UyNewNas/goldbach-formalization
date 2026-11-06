import ImbalancedChen.ActualFrozenSelectedPairSlots
import ImbalancedChen.P3ActualFineLabelThreeGammaTensor

/-!
P3.6 fixed ORIGINAL whole-box block-occurrence partition -> true fine-label
factorial tensor. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

This finite adapter uses the actual frozen selected-pair algorithm on labelled
BLOCK occurrences, not on tuple-dependent arithmetic fibres. Each block
(i,m) keeps its m original prime slots. In particular, the full repeated-
label factorial M_all is NOT replaced by the product of the three group
factorials. A physical source whose frozen algorithm acts on individual
prime occurrences requires a separate block-to-slot dictionary; this
lemma does not assert that every original PP atom has that dictionary.
No rho, coprime mean, medium estimate (M), or discrepancy is invented.
-/

namespace ImbalancedChen.P3ActualFrozenFineLabelPartition
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3ActualFineLabelThreeGammaTensor
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- The ACTUAL frozen selected-pair rule permutes complete block
occurrences. Expanding every (label,m) block into m prime slots commutes
with this permutation, even if m>1. This discharges the earlier hperm
for this precise class of whole-box block partitions. -/
theorem frozen_block_words_perm
    (D A : ℝ) (yz : Bool) (upper : (ℕ × ℕ) → ℕ)
    (p : Fin 3 → (ℕ × ℕ)) (tail : List (ℕ × ℕ)) :
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (actualPrimeLabelBlocksWord (p 0 :: p 1 :: p 2 :: tail)).Perm
      (actualPrimeLabelBlocksWord groups.1 ++
       actualPrimeLabelBlocksWord groups.2.1 ++
       actualPrimeLabelBlocksWord groups.2.2) := by
  have hb := (actualFrozenSelectedPairSlots_perm D A yz upper p tail).symm
  have hwords := hb.flatMap (fun b : ℕ × ℕ => List.replicate b.2 b.1)
  simpa only [actualPrimeLabelBlocksWord, List.flatMap_append, List.append_assoc]
    using hwords

/-- Distinct original label indices stay distinct inside EACH frozen
group, with no new one-boundedness premise for the three gammas. -/
theorem frozen_block_group_labels_pairwise
    (D A : ℝ) (yz : Bool) (upper : (ℕ × ℕ) → ℕ)
    (p : Fin 3 → (ℕ × ℕ)) (tail : List (ℕ × ℕ))
    (hlabels : (p 0 :: p 1 :: p 2 :: tail).Pairwise
      (fun b d : ℕ × ℕ => b.1 ≠ d.1)) :
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    groups.1.Pairwise (fun b d : ℕ × ℕ => b.1 ≠ d.1) ∧
      groups.2.1.Pairwise (fun b d : ℕ × ℕ => b.1 ≠ d.1) ∧
      groups.2.2.Pairwise (fun b d : ℕ × ℕ => b.1 ≠ d.1) := by
  have hb := actualFrozenSelectedPairSlots_perm D A yz upper p tail
  have hfull : (let groups := actualFrozenSelectedPairSlots D A yz upper p tail
      groups.1 ++ groups.2.1 ++ groups.2.2).Pairwise
        (fun b d : ℕ × ℕ => b.1 ≠ d.1) :=
    hlabels.perm hb.symm (by intro x y h; exact h.symm)
  have hlast := (List.pairwise_append).mp hfull
  have hfirst := (List.pairwise_append).mp hlast.1
  exact ⟨hfirst.1, hfirst.2.1, hlast.2.1⟩

/-- The true fixed block partition supplies hperm itself. The ORIGINAL
full normalized source has signed c/M_all; the three gamma factors
recover exactly M1*M2*M3/M_all, including repeated fine-label slots.
No coefficient or full-product fibre is silently deduplicated. -/
theorem actual_frozen_fine_label_tensor
    (N : ℕ) (τ D A : ℝ) (yz : Bool)
    (upper : (ℕ × ℕ) → ℕ) (p : Fin 3 → (ℕ × ℕ))
    (tail : List (ℕ × ℕ)) (c : ℝ) (H : ℕ → ℝ) :
    let original := p 0 :: p 1 :: p 2 :: tail
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    let B := actualPrimeFineLabelFinset N τ
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord groups.1)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord groups.2.1)
    let T₃ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord groups.2.2)
    (c / (actualPrimeLabelBlocksFactorial original : ℝ)) *
      (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord original),
        H ps.prod) =
      (c * (((actualPrimeLabelBlocksFactorial groups.1 : ℝ) *
        (actualPrimeLabelBlocksFactorial groups.2.1 : ℝ) *
        (actualPrimeLabelBlocksFactorial groups.2.2 : ℝ)) /
        (actualPrimeLabelBlocksFactorial original : ℝ))) *
      (∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod,
        ∑ d ∈ T₃.image List.prod,
          gamma B groups.1 a * gamma B groups.2.1 b *
            gamma B groups.2.2 d * H (a * b * d)) := by
  exact actual_label_three_gamma_tensor
    (actualPrimeFineLabelFinset N τ) (p 0 :: p 1 :: p 2 :: tail)
    (actualFrozenSelectedPairSlots D A yz upper p tail).1
    (actualFrozenSelectedPairSlots D A yz upper p tail).2.1
    (actualFrozenSelectedPairSlots D A yz upper p tail).2.2
    (frozen_block_words_perm D A yz upper p tail) c H

/-- On the original half-open fine-prime alphabet, distinct block labels
in the source imply the product of the THREE frozen gamma factors is
one-bounded at every full-product triple, with no extra bound assumed. -/
theorem actual_frozen_gamma_product_abs_le_one
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool) (upper : (ℕ × ℕ) → ℕ)
    (p : Fin 3 → (ℕ × ℕ)) (tail : List (ℕ × ℕ))
    (hlabels : (p 0 :: p 1 :: p 2 :: tail).Pairwise
      (fun b d : ℕ × ℕ => b.1 ≠ d.1))
    (a b d : ℕ) :
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    |gamma (actualPrimeFineLabelFinset N τ) groups.1 a *
      gamma (actualPrimeFineLabelFinset N τ) groups.2.1 b *
      gamma (actualPrimeFineLabelFinset N τ) groups.2.2 d| ≤ 1 := by
  have h := frozen_block_group_labels_pairwise D A yz upper p tail hlabels
  exact fine_three_gamma_product_abs_le_one N hN τ hτ
    (actualFrozenSelectedPairSlots D A yz upper p tail).1
    (actualFrozenSelectedPairSlots D A yz upper p tail).2.1
    (actualFrozenSelectedPairSlots D A yz upper p tail).2.2
    h.1 h.2.1 h.2.2 a b d

end
end ImbalancedChen.P3ActualFrozenFineLabelPartition
