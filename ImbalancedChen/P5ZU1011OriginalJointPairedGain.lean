import ImbalancedChen.P5ZU1011OriginalJointOuterFibre
import ImbalancedChen.P5ZU1011OriginalSixteenPairedFibreGain

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual signed +U6-JOINT coefficient uses the SAME last-pair mask.
The genuine low U10 integral is present and NEVER deleted; its exact
cancellation in the change is proved from disjoint real band integration.
Only the high U11 band contributes to the deleted gain integral. Both
original signs occur once and no root1/4 is inserted. No moving-mask,
cardinality, AP or table-feedback license is asserted.
-/

namespace ImbalancedChen.P5Z.U1011OriginalJointPairedGain

noncomputable section

open Set MeasureTheory Classical
open U11Integral U11Canonical
open U1011OriginalSixteenOuterFibre (Outer ascendingMask measurableSet_ascendingMask)
open U1011OriginalJointOuterFibre
open U1011OriginalSixteenPairedFibreGain
open P5U6RetainedAdoptedIntegralSourceOnly

def jointRetainedIntegral (M : Set Outer) : ℝ :=
  ∫ v in U1011OriginalJointOuterFibre.jointDomain M,jointKernel v*harmonicDensity v
def lowIntegral : ℝ := U1011OriginalSixteenU10FullHarmonic.integral10
def jointPairedRetained (M : Set Outer) : ℝ := retainedU6 M-jointRetainedIntegral M
def jointSignedGainDensity (q : Outer) : ℝ := jointOuterCost q-u6Density q

/-- Actual unmasked low U10 plus the retained original high U11.
This is a proved disjoint integral split, not D10-subset-D11. -/
theorem jointRetainedIntegral_eq_low_add_high (M : Set Outer) (hM : MeasurableSet M) :
    jointRetainedIntegral M=lowIntegral+
      ∫ v in originalDomain M,jointKernel v*harmonicDensity v := by
  exact setIntegral_union (U1011OriginalJointHarmonic.domain10_disjoint_originalDomain M)
    (measurableSet_originalDomain M hM) U1011OriginalJointHarmonic.integrableOn_weighted_D10
      (U1011OriginalJointHarmonic.integrableOn_weighted_D11 M)

theorem jointRetainedIntegral_eq_low_add_retainedU11 (M : Set Outer) (hM : MeasurableSet M) :
    jointRetainedIntegral M=lowIntegral+retainedU11 M := by
  rw [jointRetainedIntegral_eq_low_add_high M hM,retainedU11_eq_original_integral M hM]
  rfl

/-- The low band actually occurs in each full joint integral, then
cancels exactly because the SAME low source is unmasked in both. -/
theorem low_band_cancels_in_change (M : Set Outer) (hM : MeasurableSet M) :
    jointRetainedIntegral M-jointRetainedIntegral ∅=retainedU11 M-retainedU11 ∅ := by
  rw [jointRetainedIntegral_eq_low_add_retainedU11 M hM,
    jointRetainedIntegral_eq_low_add_retainedU11 ∅ measurableSet_empty]
  ring

theorem jointPairedRetained_eq_old_sub_low (M : Set Outer) (hM : MeasurableSet M) :
    jointPairedRetained M=pairedRetained M-lowIntegral := by
  rw [jointPairedRetained,jointRetainedIntegral_eq_low_add_retainedU11 M hM,pairedRetained]
  ring

theorem jointSignedGainDensity_eq_raw_high_gain (q : Outer) :
    jointSignedGainDensity q=signedPairGainDensity q := by
  rw [jointSignedGainDensity,jointOuterCost_eq_raw_old,signedPairGainDensity]

theorem integrableOn_jointSignedGainDensity : IntegrableOn jointSignedGainDensity pairRectangle := by
  have heq : jointSignedGainDensity=signedPairGainDensity := funext jointSignedGainDensity_eq_raw_high_gain
  rw [heq]
  exact integrableOn_signedPairGainDensity

/-- TRUE original same-mask +U6-JOINT change, including the real low-band
cancellation. No hypothetical high-only joint coefficient is substituted. -/
theorem jointPaired_change_eq_deleted_gain (M : Set Outer) (hM : MeasurableSet M) :
    jointPairedRetained M-jointPairedRetained ∅=
      ∫ q in pairRectangle ∩ M,jointSignedGainDensity q := by
  rw [jointPairedRetained_eq_old_sub_low M hM,jointPairedRetained_eq_old_sub_low ∅ measurableSet_empty]
  calc
    _ = pairedRetained M-pairedRetained ∅ := by ring
    _ = ∫ q in pairRectangle ∩ M,signedPairGainDensity q := pairedRetained_change_eq_deleted_gain M hM
    _ = _ := by simp only [jointSignedGainDensity_eq_raw_high_gain]

/-- The deleted density uses the ONE joint raw first-pair fibre, with the
TRUE corrected U6 product gate and complete original R denominator. -/
theorem jointSignedGainDensity_eq_original_formula {q : Outer} (hq : q ∈ pairRectangle) :
    jointSignedGainDensity q=jointFibreCost q/(q.1*q.2)-
      (if q.1+q.2≤(833/2500 : ℝ) then
        4*(Real.log (runboProfile q-1)+
          Part5OriginalUpsilon5CausalDictionary.adoptedH248Floor (runboProfile q))/
            (runboResidual q*q.2*q.1) else 0) := by
  rw [jointSignedGainDensity,jointOuterCost,u6Density_eq_product_indicator hq]

/-- Natural last-pair E(p3,p4) reads E(y,x) exactly once. The negative
integral includes all low fourth-prime labels, regardless of E. -/
theorem original_ascending_joint_change_eq_deleted_gain (E : Set Outer) (hE : MeasurableSet E) :
    (retainedEstimatorIntegral (fun p : U6Point => (p 0,p 1) ∈ E) 0-
      jointRetainedIntegral (ascendingMask E))-
    (retainedEstimatorIntegral (fun _ : U6Point => False) 0-jointRetainedIntegral ∅)=
      ∫ q in pairRectangle ∩ ascendingMask E,jointSignedGainDensity q := by
  have h := jointPaired_change_eq_deleted_gain (ascendingMask E) (measurableSet_ascendingMask E hE)
  unfold jointPairedRetained at h
  rw [retainedU6_eq_original_adopted E hE] at h
  have hempty : ascendingMask (∅ : Set Outer)=∅ := by ext q; simp [ascendingMask]
  have h6 := retainedU6_eq_original_adopted (∅ : Set Outer) measurableSet_empty
  rw [hempty] at h6
  rw [h6] at h
  simpa only [mem_empty_iff_false] using h

/-- Exact attachment to the already proved original JOINT native mean,
without repeating that independent arithmetic/PNT construction. -/
theorem jointRetainedIntegral_actual_rows (S : Finset U1011OriginalJointHarmonic.Row) :
    jointRetainedIntegral (U1011OriginalPairedFixedMaskHarmonic.outerUnion S)=
      U1011OriginalJointHarmonic.jointIntegral S := rfl

end

end ImbalancedChen.P5Z.U1011OriginalJointPairedGain
