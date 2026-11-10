import ImbalancedChen.P4AOriginalFull87RemainingBoxGapLower
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Complete the complementary 40 original full87 continuous-source cells:
15 descending, 13 ascendingPair and 12 H3 first-failure cells.
The exact improvement rows are respectively 16, 18 and 19.
These are rows of the EXISTING archived literal arrays, not a new mask,
policy, cap or unproven uniform gap hypothesis.

The previous packet proved a stronger 1/20000 ideal cap-gap lower on
47 remaining-family boxes. The local exact 40-family affine certificates
give 1/125000 on their genuine common radius 1e-8 boxes. Taken together,
the 87 original ideal kernels inherit a pointwise bound, not a saved
numerical integral, actual dynamic parent, or physical signed gain.
-/

namespace ImbalancedChen.P4AOriginalFull87Other40BoxGapLower
noncomputable section

open scoped Classical BigOperators
open VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87QuantitativeGapIntegral
open P4AOriginalFull87StrictPositiveSourceIntegral
open P4AOriginalFull87RemainingBoxGapLower

/-- Descending's REAL exported row #16, with the same old winner and
new selected cap used in the original Source dictionary. -/
private theorem desc_improvement_row_eq_gap
    (i : Fin 15) (t : Point) :
    OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
       (OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i 16) t =
      newCap (.descending i) t - comparison (.descending i) t := by
  rw [OriginalDescendingFifteenLiteralAffineRows.exportedRow_eval_eq_semanticSlack]
  change OriginalDescendingFifteenLiteralAffineRows.evaluate
    (OriginalDescendingFifteenLiteralAffineRows.newExpr -
     OriginalDescendingFifteenLiteralAffineRows.oldExpr) t =
       newCap (.descending i) t - comparison (.descending i) t
  simp [OriginalDescendingFifteenLiteralAffineRows.evaluate,
    OriginalDescendingFifteenLiteralAffineRows.newExpr,
    OriginalDescendingFifteenLiteralAffineRows.oldExpr,
    OriginalDescendingFifteenLiteralAffineRows.K,
    OriginalDescendingFifteenLiteralAffineRows.X,
    newCap, comparison, P2OriginalDescendingEighthLogSemantics.newCap,
    P2OriginalDescendingEighthLogSemantics.oldRaw,
    P2OriginalDescendingEighthLogSemantics.selectedSum,
    P2OriginalDescendingEighthLogSemantics.d,
    P2OriginalDescendingEighthLogSemantics.eta,
    VariableEnvelope.C] <;> ring

/-- Ascending pair's REAL exported row #18, without imposing the
descending family mask on its original cell. -/
private theorem pair_improvement_row_eq_gap
    (i : Fin 13) (t : Point) :
    OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
      (OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i 18) t =
      newCap (.ascendingPair i) t - comparison (.ascendingPair i) t := by
  rw [OriginalAscendingThirteenLiteralAffineRows.exportedRow_eval_eq_semanticSlack]
  change OriginalDescendingFifteenLiteralAffineRows.evaluate
    (OriginalAscendingThirteenLiteralAffineRows.newExpr -
     OriginalAscendingThirteenLiteralAffineRows.oldExpr) t =
       newCap (.ascendingPair i) t - comparison (.ascendingPair i) t
  simp [OriginalDescendingFifteenLiteralAffineRows.evaluate,
    OriginalAscendingThirteenLiteralAffineRows.newExpr,
    OriginalAscendingThirteenLiteralAffineRows.oldExpr,
    OriginalDescendingFifteenLiteralAffineRows.K,
    OriginalDescendingFifteenLiteralAffineRows.X,
    newCap, comparison, P2OriginalThirdMinorantLogDictionarySourceOnly.newCap,
    P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap,
    P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum,
    P2OriginalThirdMinorantLogDictionarySourceOnly.eta,
    VariableEnvelope.A] <;> ring

/-- H3's REAL first-failure row #19, identified through the already
proved 37-row semantic dictionary instead of any guessed new guard. -/
private theorem h3_improvement_row_eq_gap
    (i : Fin 12) (t : Point) :
    P4AOriginalFirstFailureH3Literal.evalAffine
      (P4AOriginalFirstFailureH3Literal.sourceAffineRows i
        (P4AOriginalFirstFailureH3SourceSemantics.commonRow 19)).2 t =
      newCap (.h3 i) t - comparison (.h3 i) t := by
  rw [P4AOriginalFirstFailureH3SourceSemantics.source_common_row]
  rfl

/-- All fifteen actual descending source inner boxes: the genuine row
#16 is bounded using its original 96-row rational margin certificate. -/
theorem original_desc15_gap_lower
    (i : Fin 15) (t : Point)
    (ht : t ∈ sourceInnerBox (.descending i)) :
    (1 / 125000 : ℝ) ≤
      newCap (.descending i) t - comparison (.descending i) t := by
  have hc : ∀ j : Fin 8,
      |t j - P4AOriginalFull87DescAscPairInteriors.originalDescPoint i j| ≤
        (1 / 100000000 : ℝ) := by
    intro j
    simpa [sourceInnerBox, commonRadius,
      P4AOriginalFull87KernelPositiveWitness.originalCentre]
      using (ht j).le
  have h := P4AOriginalFull87DescAscPairInteriors.all15_original_desc_rows_box_slack
    i t hc (16 : Fin 96)
  rwa [desc_improvement_row_eq_gap] at h

/-- All thirteen actual ascending-pair cells, on their original row #18. -/
theorem original_pair13_gap_lower
    (i : Fin 13) (t : Point)
    (ht : t ∈ sourceInnerBox (.ascendingPair i)) :
    (1 / 125000 : ℝ) ≤
      newCap (.ascendingPair i) t - comparison (.ascendingPair i) t := by
  have hc : ∀ j : Fin 8,
      |t j - P4AOriginalFull87DescAscPairInteriors.originalPairPoint i j| ≤
        (1 / 100000000 : ℝ) := by
    intro j
    simpa [sourceInnerBox, commonRadius,
      P4AOriginalFull87KernelPositiveWitness.originalCentre]
      using (ht j).le
  have h := P4AOriginalFull87DescAscPairInteriors.all13_original_pair_rows_box_slack
    i t hc (18 : Fin 97)
  rwa [pair_improvement_row_eq_gap] at h

/-- All twelve actual H3 failure cells; row #19 is literally M8-R6. -/
theorem original_h3_12_gap_lower
    (i : Fin 12) (t : Point)
    (ht : t ∈ sourceInnerBox (.h3 i)) :
    (1 / 125000 : ℝ) ≤
      newCap (.h3 i) t - comparison (.h3 i) t := by
  have hc : ∀ j : Fin 8,
      |t j - P4AOriginalFull87H3Interiors.originalH3Point i j| ≤
        (1 / 100000000 : ℝ) := by
    intro j
    simpa [sourceInnerBox, commonRadius,
      P4AOriginalFull87KernelPositiveWitness.originalCentre]
      using (ht j).le
  have h := P4AOriginalFull87H3Interiors.all12_original_h3_rows_box_slack
    i t hc (P4AOriginalFirstFailureH3SourceSemantics.commonRow 19)
  rwa [h3_improvement_row_eq_gap] at h

/-- A single rational original cap-gap lower over all 87 genuine
Cell constructors, but only INSIDE their already certified inner boxes. -/
theorem original_full87_inner_box_gap_lower
    (c : Cell) (t : Point) (ht : t ∈ sourceInnerBox c) :
    (1 / 125000 : ℝ) ≤ newCap c t - comparison c t := by
  cases c with
  | remaining d =>
      exact (by norm_num : (1 / 125000 : ℝ) ≤ 1 / 20000).trans
        (original_remaining47_gap_lower d t ht)
  | descending i => exact original_desc15_gap_lower i t ht
  | ascendingPair i => exact original_pair13_gap_lower i t ht
  | h3 i => exact original_h3_12_gap_lower i t ht

/-- Same original eighth residual kernel, on the same actual original
continuous source box. No numerical archive endpoint is inserted. -/
theorem original_full87_inner_box_kernel_lower
    (c : Cell) (t : Point) (ht : t ∈ sourceInnerBox c) :
    (4 / (9 * mu ^ 10)) * (1 / 125000 : ℝ) ≤ kernel c t := by
  have hs : Source c t := innerBox_mem_original_source c t ht
  have hfactor : 0 ≤ (4 / (9 * mu ^ 10) : ℝ) := by
    have hmu : (0 : ℝ) < mu := by norm_num [VariableEnvelope.mu]
    positivity
  have hscaled : (4 / (9 * mu ^ 10)) * (1 / 125000 : ℝ) ≤
      scaledCapGap c t := by
    exact mul_le_mul_of_nonneg_left (original_full87_inner_box_gap_lower c t ht)
      hfactor
  exact hscaled.trans (scaledCapGap_le_kernel hs)

end
end ImbalancedChen.P4AOriginalFull87Other40BoxGapLower
