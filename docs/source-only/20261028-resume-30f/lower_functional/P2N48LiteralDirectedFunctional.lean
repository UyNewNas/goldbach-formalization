import ImbalancedChen.P2N48RetainedPriorityRemainder
import ImbalancedChen.OriginalPairedN48RequiredRowQ112Bridge

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original high-row J112 weights, global raw omega queries and the original
Q112/Q80 max-floor source proposals feed the actual retained row recost.
The whole negative functional still includes the excluded archive parents
and the domain outside this crop. No hOld/hZ/hCertificate is a premise.

The terminal upper-bound declarations are SOURCE PROPOSALS because their
closed producer/log/decoder/floor finite decisions have NOT been run.
They supply no numerical upper bound for the explicit remaining costs.
-/
namespace ImbalancedChen.P2N48LiteralDirectedFunctional
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48SelectedFunctionalRemainder P2N48ActualGeometricKeyDecoder
open P2N48OriginalQ80DirectedRowSoundness
open P2N48RetainedPriorityRemainder
open OriginalPairedN48RequiredRowQ112Bridge
open P5Z.U11Canonical

def retainedLiteralUpper : ℝ :=
  (∑ r∈actualRetainedRows,savedParent r (parentUnweightedMass (fullParent r)))-
    ∑ r∈actualRetainedRows,rowGainLower r

def excludedActualCost : ℝ :=
  ∑ r∈excludedRawRows,parentCost ImbalancedChen.currentK (selectedParent r actualMask)

def wholeLiteralUpper : ℝ := retainedLiteralUpper+excludedActualCost+outsideRawCropCost

/-- No real endpoint or old-cost licence is supplied by the caller.
The exact frozen finite proof proposals remain unexecuted dependencies. -/
theorem retained_actual_cost_upper_proposal :
    (∑ r∈actualRetainedRows,
      parentCost ImbalancedChen.currentK (selectedParent r actualMask))≤retainedLiteralUpper := by
  apply actual_archived_selected_rows_current_cost actual_retained_massLower_sound
  intro r hr _ _
  exact actual_required_all_row_old_cost_proposal r hr

/-- The actual whole negative coefficient, retaining every missing cost.
This is not a claim that the retained method-zero rows cover its domain. -/
theorem whole_actual_coefficient_upper_proposal :
    P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient≤wholeLiteralUpper := by
  rw [actual_coefficient_exact_three_costs]
  unfold wholeLiteralUpper excludedActualCost
  exact add_le_add_right (add_le_add_right retained_actual_cost_upper_proposal _) _

/-- Correct signed direction when this original negative occurrence is
inserted into the lower functional; the unresolved costs retain minus signs. -/
theorem signed_actual_coefficient_lower_proposal :
    -retainedLiteralUpper-excludedActualCost-outsideRawCropCost≤
      -P2N48ActualSelectedRhoCoefficient.actualSelectedCoefficient := by
  have h := whole_actual_coefficient_upper_proposal
  dsimp [wholeLiteralUpper] at h
  linarith only [h]

/-- The original native joint harmonic supplier, with its fixed adopted
deletionMask before N, reaches the exact same three costs. This uses the
prior real mean theorem and actual geometric ownership, not row floors. -/
theorem tendsto_negative_nativeJoint_exact_three_costs :
    Tendsto (fun N : ℕ =>
      -(P5Z.U1011OriginalJointHarmonic.nativeJoint N
        (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))
        P5Z.U1011OriginalJointHarmonic.actualMinimum)) atTop
      (𝓝 (-(∑ r∈actualRetainedRows,
        parentCost ImbalancedChen.currentK (selectedParent r actualMask))-
          excludedActualCost-outsideRawCropCost)) := by
  have h := tendsto_negative_nativeJoint_rows_uncovered actualRetainedRows
    actualRetainedRows_distinctGeometricKeys
  rw [uncoveredCost_exact_excluded_and_outside] at h
  convert h using 1 <;> dsimp [excludedActualCost] <;> congr 1 <;> ring

end
end ImbalancedChen.P2N48LiteralDirectedFunctional
