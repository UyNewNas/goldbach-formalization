import ImbalancedChen.P5OriginalPhysicalBufferedU6NativeMain
import ImbalancedChen.P5ZU1011OriginalJointHarmonic
import ImbalancedChen.P5OriginalSameMaskPairedNativeGain

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Literal buffered positive U6 minus the ORIGINAL JOINT negative U10+U11
native harmonic main. U10 remains entirely unmasked; U11 keeps the SAME
actual17572-row deletion mask as U6. The product buffer is fixed before N.
Its lower bound is supplied by the actual closed physical selector,
retained boundary sums and uniform buffer theorem, not an hBuffer input.
The coefficient change is the actual same-outer-mask gain integral.
No quotient-cardinality bound, AP/H248 license or root1/4 is supplied.
-/
namespace ImbalancedChen.P5OriginalBufferedJointSignedMainSourceOnly

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open P5Z.U11Integral
open P5Z.U1011OriginalPairedRowPrimeTests
open P5Z.U1011OriginalPairedFixedMaskHarmonic (outerUnion outerUnion_all e0Rows e1Rows)
open P5U6OriginalPairedMaskNativeHarmonicSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly
open P5OriginalPhysicalBufferedU6NativeMainSourceOnly
open P5OriginalSameMaskPairedNativeGainSourceOnly
open P5Z.U1011OriginalSixteenPairedFibreGain
open Certificates.PairedV2

def signedCoefficient (S : Finset Row) : ℝ :=
  retainedEstimatorIntegral (fun x => x ∈ ascendingPointMask S) 0 -
    P5Z.U1011OriginalJointHarmonic.jointIntegral S

def bufferedJointMain (S : Finset Row) (eta : ℝ) (N : ℕ) : ℝ :=
  closedMain S N eta - P5Z.U1011OriginalJointHarmonic.nativeJoint N
    (nativeMask (outerUnion S) N) P5Z.U1011OriginalJointHarmonic.actualMinimum

/-- The actual low U10 band is present once and is never masked. This
identity also fixes the signs before any asymptotic estimate is applied. -/
theorem bufferedJointMain_eq_literal_bands {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (eta : ℝ) :
    bufferedJointMain S eta N = closedMain S N eta -
      P5Z.U1011OriginalSixteenU10Geometry.native10 N P5Z.U1011OriginalJointHarmonic.actualMinimum -
      P5Z.U1011OriginalSixteenNativeHarmonic.nativeHarmonicSum N
        (nativeMask (outerUnion S) N) P5Z.U1011OriginalJointHarmonic.actualMinimum := by
  rw [bufferedJointMain, P5Z.U1011OriginalJointHarmonic.nativeJoint_eq_native10_add_native11 hN]
  ring

/-- The SAME coefficient and mask, one fixed positive physical eta, then
all sufficiently large N. All harmonic and buffer suppliers are proved. -/
theorem exists_fixed_buffered_signed_main (S : Finset Row) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ N : ℕ in atTop,
      signedCoefficient S - epsilon ≤ bufferedJointMain S eta N := by
  have hhalf : 0 < epsilon / 2 := by positivity
  obtain ⟨eta, heta, h6⟩ := exists_fixed_buffered_physical_lower S hhalf
  refine ⟨eta, heta, ?_⟩
  have hjoint := (P5Z.U1011OriginalJointHarmonic.tendsto_nativeJoint_staticRows S).eventually
    (gt_mem_nhds (lt_add_of_pos_right _ hhalf))
  filter_upwards [h6, hjoint] with N h6N hjointN
  unfold signedCoefficient bufferedJointMain
  linarith only [h6N, hjointN]

/-- Exact coefficient, including the unmasked U10 integral. It differs
from the paired U6-U11 coefficient by that SAME fixed U10 term. -/
theorem signedCoefficient_eq_paired_minus_u10 (S : Finset Row) :
    signedCoefficient S = pairedRetained (outerUnion S) -
      P5Z.U1011OriginalSixteenU10FullHarmonic.integral10 := by
  have h11 : (∫ v in originalDomain (outerUnion S),
      P5Z.U1011OriginalJointHarmonic.weighted v) = retainedU11 (outerUnion S) := by
    simpa only [P5Z.U1011OriginalJointHarmonic.weighted,
      P5Z.U1011OriginalJointHarmonic.actualMinimum,
      P5Z.U1011OriginalPairedFixedMaskHarmonic.weighted,
      P5Z.U1011OriginalPairedFixedMaskHarmonic.actualMinimum] using
      u11_integral_eq_actual_outer S
  unfold signedCoefficient
  rw [P5Z.U1011OriginalJointHarmonic.jointIntegral_eq_band_sum,
    u6_integral_eq_actual_outer S, h11]
  unfold pairedRetained
  ring

/-- The unmasked U10 term cancels in a SAME-mask coefficient change.
The remaining gain is the genuine original outer-fibre signed density. -/
theorem signedCoefficient_change_eq_actual_gain (S : Finset Row) :
    signedCoefficient S - signedCoefficient ∅ =
      ∫ q in pairRectangle ∩ outerUnion S, signedPairGainDensity q := by
  have hg := pairedRetained_change_eq_deleted_gain (outerUnion S)
    (measurableSet_actual_outerUnion S)
  rw [signedCoefficient_eq_paired_minus_u10, signedCoefficient_eq_paired_minus_u10,
    outerUnion_empty]
  linarith only [hg]

def actualAdoptedBufferedJointMain (eta : ℝ) (N : ℕ) : ℝ :=
  closedMain (Finset.univ : Finset Row) N eta -
    P5Z.U1011OriginalJointHarmonic.nativeJoint N
      (FullMask.P1E0E1.deletionMask (N : ℝ)) P5Z.U1011OriginalJointHarmonic.actualMinimum

/-- Concrete original all-E0/E1 buffered main. The closed product wall
and all original prime/centre/band data are those of closedSelector. -/
theorem exists_actual_adopted_buffered_joint_main {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ᶠ N : ℕ in atTop,
      signedCoefficient (Finset.univ : Finset Row) - epsilon ≤
        actualAdoptedBufferedJointMain eta N := by
  simpa only [actualAdoptedBufferedJointMain, bufferedJointMain,
    outerUnion_all, nativeMask_actual_adopted] using
    exists_fixed_buffered_signed_main (Finset.univ : Finset Row) hepsilon

theorem actual_adopted_coefficient_change :
    signedCoefficient (Finset.univ : Finset Row) - signedCoefficient ∅ =
      ∫ q in pairRectangle ∩ FullMask.P1E0E1.pairRegion, signedPairGainDensity q := by
  simpa only [outerUnion_all] using
    signedCoefficient_change_eq_actual_gain (Finset.univ : Finset Row)

theorem actual_e0_coefficient_change : signedCoefficient e0Rows - signedCoefficient ∅ =
    ∫ q in pairRectangle ∩ FullMask.P1E0E1.e0PairRegion, signedPairGainDensity q := by
  simpa only [P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_e0] using
    signedCoefficient_change_eq_actual_gain e0Rows

theorem actual_e1_coefficient_change : signedCoefficient e1Rows - signedCoefficient ∅ =
    ∫ q in pairRectangle ∩ FullMask.P1E0E1.e1PairRegion, signedPairGainDensity q := by
  simpa only [P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_e1] using
    signedCoefficient_change_eq_actual_gain e1Rows

end
end ImbalancedChen.P5OriginalBufferedJointSignedMainSourceOnly
