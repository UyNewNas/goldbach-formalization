import ImbalancedChen.P3ActualFrozenPhysicalGamma
import ImbalancedChen.ActualPrimeFineWordSlotRegrouping

/-!
P3.6: the ACTUAL weakly ordered original fine prime-slot word supplies
its own run-length label blocks and the original multiplicity M_J.

The source word equality hword, the distinct-label block dictionary and
the restoring M_all are derived from ActualPrimeFineWordMultiplicity,
not passed as new PP or distribution hypotheses. The literal original
sorted squarefree source is connected to the three normalized gamma
groups selected by the existing endpoint-frozen allocator.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
This is an exact finite SOURCE coefficient identity; the outside integer
r in the Mobius factor is not the physical modulus weight rho_T.
There is no claim about arbitrary physical atoms, global squarefree rho,
coprime mean, analytic errors or the completion of PP.
-/

namespace ImbalancedChen.P3ActualSortedFineSourceGamma
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3ActualFrozenPhysicalGamma
open ImbalancedChen.P3ActualFrozenGroupWords
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- On the literal original weakly descending fine-label word, the
repeated-label blocks and their full factorial are NOT supplied by a
caller. In particular the hword assumption of the earlier physical
three-gamma lemma is discharged by the existing run-length compiler. -/
theorem actual_fine_word_physical_tensor
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (c : ℝ) (F : ℕ → ℝ) :
    let input := p 0 :: p 1 :: p 2 :: tail
    let B := actualPrimeFineLabelFinset N τ
    let blocks := actualPrimeFineLabelBlocksOfWord input
    let size := actualFrozenSplitSize D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    (c / (actualPrimeFineWordMultiplicity input : ℝ)) *
      (∑ ps ∈ actualPrimeSlotBox B input, F ps.prod) =
    (c * (((actualPrimeLabelBlocksFactorial g₀ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₁ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₂ : ℝ)) /
      (actualPrimeFineWordMultiplicity input : ℝ))) *
    (∑ a ∈ T₀.image List.prod, ∑ b ∈ T₁.image List.prod,
      ∑ d ∈ T₂.image List.prod,
        gamma B g₀ a * gamma B g₁ b * gamma B g₂ d *
        F (a * b * d)) := by
  let input := p 0 :: p 1 :: p 2 :: tail
  let B := actualPrimeFineLabelFinset N τ
  let blocks := actualPrimeFineLabelBlocksOfWord input
  let size := actualFrozenSplitSize D A yz upper p tail
  let groups := actualFrozenSelectedPairSlots D A yz upper p tail
  let g₀ := splitBlocks blocks size 0
  let g₁ := splitBlocks blocks size 1
  let g₂ := splitBlocks blocks size 2
  let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
  let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
  let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
  have hpair : blocks.Pairwise (fun b c => b.1 ≠ c.1) :=
    (actualPrimeFineLabelBlocksOfWord_order input horder).imp
      (fun h => Nat.ne_of_gt h)
  have hword : actualPrimeLabelBlocksWord blocks =
      p 0 :: p 1 :: p 2 :: tail := by
    simpa only [blocks, input] using
      actualPrimeFineLabelBlocksOfWord_word input
  have hM : actualPrimeLabelBlocksFactorial blocks =
      actualPrimeFineWordMultiplicity input :=
    actualPrimeFineLabelBlocksOfWord_factorial input horder
  have hraw :
      (∑ ps ∈ actualPrimeSlotBox B input, F ps.prod) =
        ∑ ps ∈ actualPrimeSlotBox B groups.1,
          ∑ qs ∈ actualPrimeSlotBox B groups.2.1,
            ∑ rs ∈ actualPrimeSlotBox B groups.2.2,
              F (ps.prod * qs.prod * rs.prod) := by
    simpa only [input, blocks, B, groups, hword] using
      (actual_frozen_physical_three_product_sum
        N τ D A yz upper p tail blocks hword F)
  have hgamma := actual_frozen_physical_three_gamma_tensor
    N τ D A yz upper p tail blocks hpair hword c F
  calc
    _ = (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox B input, F ps.prod) := by rw [hM]
    _ = (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox B groups.1,
          ∑ qs ∈ actualPrimeSlotBox B groups.2.1,
            ∑ rs ∈ actualPrimeSlotBox B groups.2.2,
              F (ps.prod * qs.prod * rs.prod)) :=
      congrArg
        (fun v : ℝ => (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) * v)
        hraw
    _ = _ := by
      simpa only [B, blocks, size, groups, g₀, g₁, g₂, T₀, T₁, T₂,
        hM] using hgamma

/-- The actual ORIGINAL sorted-squarefree source, with the unchanged
external integer r in mu(r*n), is represented using precisely the three
original fine-label gamma coefficients and the correct multinomial
restoring scalar. This eliminates hword and manually supplied M_J on the
weakly ordered physical-word domain; it does NOT pay any modulus sum. -/
theorem actual_sorted_fine_source_gamma
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (r : ℕ) (c : ℝ) (H : ℕ → ℝ) :
    let input := p 0 :: p 1 :: p 2 :: tail
    let B := actualPrimeFineLabelFinset N τ
    let blocks := actualPrimeFineLabelBlocksOfWord input
    let size := actualFrozenSplitSize D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    c * (∑ n ∈ ((actualPrimeSlotBox B input).filter
        List.SortedGT).image List.prod,
          (ArithmeticFunction.moebius (r * n) : ℝ) * H n) =
    (c * (((actualPrimeLabelBlocksFactorial g₀ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₁ : ℝ) *
      (actualPrimeLabelBlocksFactorial g₂ : ℝ)) /
      (actualPrimeFineWordMultiplicity input : ℝ))) *
    (∑ a ∈ T₀.image List.prod, ∑ b ∈ T₁.image List.prod,
      ∑ d ∈ T₂.image List.prod,
        gamma B g₀ a * gamma B g₁ b * gamma B g₂ d *
        ((ArithmeticFunction.moebius (r * (a * b * d)) : ℝ) *
          H (a * b * d))) := by
  let input := p 0 :: p 1 :: p 2 :: tail
  have hraw := actualPrimeFineWord_original_scalar
    hN hτ input horder r c H
  have hphys := actual_fine_word_physical_tensor
    N τ D A yz upper p tail horder c
      (fun n => (ArithmeticFunction.moebius (r * n) : ℝ) * H n)
  exact hraw.symm.trans hphys

end
end ImbalancedChen.P3ActualSortedFineSourceGamma
