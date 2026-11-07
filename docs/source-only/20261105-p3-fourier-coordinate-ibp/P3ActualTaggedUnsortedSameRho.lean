import ImbalancedChen.P3ActualCanonicalFrozenSplitPayment
import ImbalancedChen.P3ActualFrozenComplexThreeModes

/-!
P3.6 — original Fin-ID positional Fourier finite modes through the SAME
actual three frozen physical prime boxes, at the SAME integer rho.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
The full unsorted fine-label word, canonical block factorial and all three
split-block factorials are CONSTRUCTED from the actual input, not assumed.
The allocation uses the original ID upper endpoints pulled back from
the actual label upper endpoints; no noninjectivity restriction is imposed.

A finite sum of separated modes is not a continuous Fourier inversion
of W_T. Nor does this file identify a full PP atom compiler, its actual
physical rho_T and Q_T, or establish a complete-modulus discrepancy bound.
-/ 

namespace ImbalancedChen.P3ActualTaggedUnsortedSameRho
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenComplexThreeModes
open ImbalancedChen.P3ActualFrozenTaggedPrimeModes
open ImbalancedChen.P3ActualFrozenTaggedLabelCompiler
open ImbalancedChen.P3ActualFrozenCanonicalUnsortedGamma
open ImbalancedChen.P3ActualCanonicalFrozenSplitPayment
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- A common FINITE mode is evaluated at the original IDs of the true
frozen groups. The labelled box is thereby the actual ID-group label word,
even for noninjective fine labels. Exact M_all and M_j are retained.

No reordering of a positional phase is inferred from a label permutation.
-/ 
theorem actual_tagged_unsorted_finite_modes_tensor {n : ℕ} {κ : Type*}
    (K : Finset κ) (amp : κ → ℂ)
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upperLabel : ℕ → ℕ)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n))
    (eta : κ → Fin n → ℝ) (U : Fin n → ℝ)
    (c : ℂ) (H : ℕ → ℂ) :
    let pLabel : Fin 3 → ℕ := fun j => label (p j)
    let tailLabel := tail.map label
    let blocks := canonicalFineBlocks (pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel)
    let size := actualFrozenSplitSize D A yz upperLabel pLabel tailLabel
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let B := actualPrimeFineLabelFinset N τ
    let S₀ := actualPrimeSlotBox B (ids.1.map label)
    let S₁ := actualPrimeSlotBox B (ids.2.1.map label)
    let S₂ := actualPrimeSlotBox B (ids.2.2.map label)
    (c / (actualPrimeLabelBlocksFactorial blocks : ℂ)) *
      (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        (∑ k ∈ K, amp k *
          (positionalGroupMode (eta k) U ids.1 ps *
            (positionalGroupMode (eta k) U ids.2.1 qs *
              positionalGroupMode (eta k) U ids.2.2 rs))) *
          H (ps.prod * qs.prod * rs.prod)) =
    (c * (((actualPrimeLabelBlocksFactorial
        (splitBlocks blocks size 0) : ℂ) *
      (actualPrimeLabelBlocksFactorial
        (splitBlocks blocks size 1) : ℂ) *
      (actualPrimeLabelBlocksFactorial
        (splitBlocks blocks size 2) : ℂ)) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ))) *
      (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
        ∑ d ∈ S₂.image List.prod,
          (∑ k ∈ K, amp k *
            (physicalComplexLabelGamma B (ids.1.map label)
                (splitBlocks blocks size 0)
                (positionalGroupMode (eta k) U ids.1) a *
              (physicalComplexLabelGamma B (ids.2.1.map label)
                (splitBlocks blocks size 1)
                (positionalGroupMode (eta k) U ids.2.1) b *
               physicalComplexLabelGamma B (ids.2.2.map label)
                (splitBlocks blocks size 2)
                (positionalGroupMode (eta k) U ids.2.2) d))) *
            H (a * b * d)) := by
  let pLabel : Fin 3 → ℕ := fun j => label (p j)
  let tailLabel := tail.map label
  let blocks := canonicalFineBlocks (pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel)
  let ids := actualFrozenSelectedPairSlots D A yz
    (fun i => upperLabel (label i)) p tail
  have hwords :
      actualFrozenSelectedPairSlots D A yz upperLabel pLabel tailLabel =
        (ids.1.map label, ids.2.1.map label, ids.2.2.map label) := by
    simpa [pLabel, tailLabel, ids] using
      (selected_pair_slots_map label upperLabel D A yz p tail)
  have hbase := actual_frozen_three_finite_modes_tensor K amp
    N τ D A yz upperLabel pLabel tailLabel blocks c
    (fun k => positionalGroupMode (eta k) U ids.1)
    (fun k => positionalGroupMode (eta k) U ids.2.1)
    (fun k => positionalGroupMode (eta k) U ids.2.2) H
  dsimp only at hbase ⊢
  rw [hwords] at hbase
  exact hbase

/-- The literal complete-product fineKernel retains its exact congruence
indicator MINUS exact coprime mean at each q; rho(q) multiplies both terms.
The original input ID word may be unsorted with repeated fine labels.
Q and rho are parameters, not claimed to equal the entire physical compiler.
-/ 
theorem actual_tagged_unsorted_finite_modes_same_rho {n : ℕ} {κ : Type*}
    (K : Finset κ) (amp : κ → ℂ)
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upperLabel : ℕ → ℕ)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n))
    (eta : κ → Fin n → ℝ) (U : Fin n → ℝ)
    (c : ℂ) (Q : Finset ℕ) (rho : ℕ → ℤ) (T : ℕ) :
    let pLabel : Fin 3 → ℕ := fun j => label (p j)
    let tailLabel := tail.map label
    let blocks := canonicalFineBlocks (pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel)
    let size := actualFrozenSplitSize D A yz upperLabel pLabel tailLabel
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let B := actualPrimeFineLabelFinset N τ
    let S₀ := actualPrimeSlotBox B (ids.1.map label)
    let S₁ := actualPrimeSlotBox B (ids.2.1.map label)
    let S₂ := actualPrimeSlotBox B (ids.2.2.map label)
    (∑ q ∈ Q, (rho q : ℂ) *
      ((c / (actualPrimeLabelBlocksFactorial blocks : ℂ)) *
        (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
          (∑ k ∈ K, amp k *
            (positionalGroupMode (eta k) U ids.1 ps *
              (positionalGroupMode (eta k) U ids.2.1 qs *
                positionalGroupMode (eta k) U ids.2.2 rs))) *
            ((fineKernel T q (ps.prod * qs.prod * rs.prod) : ℝ) : ℂ)))) =
    ∑ q ∈ Q, (rho q : ℂ) *
      ((c * (((actualPrimeLabelBlocksFactorial
          (splitBlocks blocks size 0) : ℂ) *
        (actualPrimeLabelBlocksFactorial
          (splitBlocks blocks size 1) : ℂ) *
        (actualPrimeLabelBlocksFactorial
          (splitBlocks blocks size 2) : ℂ)) /
        (actualPrimeLabelBlocksFactorial blocks : ℂ))) *
        (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            (∑ k ∈ K, amp k *
              (physicalComplexLabelGamma B (ids.1.map label)
                  (splitBlocks blocks size 0)
                  (positionalGroupMode (eta k) U ids.1) a *
                (physicalComplexLabelGamma B (ids.2.1.map label)
                  (splitBlocks blocks size 1)
                  (positionalGroupMode (eta k) U ids.2.1) b *
                 physicalComplexLabelGamma B (ids.2.2.map label)
                  (splitBlocks blocks size 2)
                  (positionalGroupMode (eta k) U ids.2.2) d))) *
              ((fineKernel T q (a * b * d) : ℝ) : ℂ))) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro q hq
  exact congrArg (fun z : ℂ => (rho q : ℂ) * z)
    (actual_tagged_unsorted_finite_modes_tensor K amp
      N τ D A yz upperLabel label p tail eta U c
      (fun m => ((fineKernel T q m : ℝ) : ℂ)))

/-- The same COMPUTED whole-source blocks pay M0*M1*M2/Mall at most once.
Every finite Fourier mode has the three genuine original-ID positional
gamma coefficients bounded by 1, without any ordering of source labels.
The amplitude sum is NOT declared one-bounded: its L1 is a later budget.
-/ 
theorem actual_tagged_unsorted_mode_gamma_budget {n : ℕ} {κ : Type*}
    (K : Finset κ)
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool) (upperLabel : ℕ → ℕ)
    (label : Fin n → ℕ) (p : Fin 3 → Fin n)
    (tail : List (Fin n))
    (eta : κ → Fin n → ℝ) (U : Fin n → ℝ) :
    let pLabel : Fin 3 → ℕ := fun j => label (p j)
    let tailLabel := tail.map label
    let blocks := canonicalFineBlocks (pLabel 0 :: pLabel 1 :: pLabel 2 :: tailLabel)
    let size := actualFrozenSplitSize D A yz upperLabel pLabel tailLabel
    let ids := actualFrozenSelectedPairSlots D A yz
      (fun i => upperLabel (label i)) p tail
    let B := actualPrimeFineLabelFinset N τ
    (((actualPrimeLabelBlocksFactorial (splitBlocks blocks size 0) : ℝ) *
      (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 1) : ℝ) *
      (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 2) : ℝ)) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ)) ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ k ∈ K, ∀ a b d : ℕ,
      (‖physicalComplexLabelGamma B (ids.1.map label)
        (splitBlocks blocks size 0)
        (positionalGroupMode (eta k) U ids.1) a‖ ≤ 1) ∧
      (‖physicalComplexLabelGamma B (ids.2.1.map label)
        (splitBlocks blocks size 1)
        (positionalGroupMode (eta k) U ids.2.1) b‖ ≤ 1) ∧
      (‖physicalComplexLabelGamma B (ids.2.2.map label)
        (splitBlocks blocks size 2)
        (positionalGroupMode (eta k) U ids.2.2) d‖ ≤ 1) := by
  let pLabel : Fin 3 → ℕ := fun j => label (p j)
  let tailLabel := tail.map label
  constructor
  · exact canonical_source_split_ratio_mem_Icc
      D A yz upperLabel pLabel tailLabel
  · intro k hk a b d
    exact actual_unsorted_ID_split_three_positional_gamma_bounds
      N hN τ hτ D A yz upperLabel label p tail (eta k) U a b d

end
end ImbalancedChen.P3ActualTaggedUnsortedSameRho
