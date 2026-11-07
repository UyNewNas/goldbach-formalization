import ImbalancedChen.P5U6OriginalPairedMaskNativeHarmonic
import ImbalancedChen.P5ZU1011OriginalSixteenPairedFibreGain

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Concrete SAME-original-mask native harmonic supplier for +U6-U11, once
each, with no root1/4 normalization inserted. U6 is the corrected Runbo
R-denominator estimator; U11 is the actual original full16 nonlinear cost.
The actual adopted17572-row native deletion mask is shared by both terms.
The limiting signed change is bound to the genuine outer-fibre gain
integral, not to a supplied hMaskMean or a selected cardinality estimate.
All row families are STATIC choices preceding N. Moving-mask identities
elsewhere do not imply a moving-mask limit here.
-/
namespace ImbalancedChen.P5OriginalSameMaskPairedNativeGainSourceOnly

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open P5Z.U11Integral P5Z.U11Canonical
open P5Z.U1011OriginalPairedRowPrimeTests
open P5Z.U1011OriginalSixteenNativeHarmonic
open P5U6OriginalPairedMaskNativeHarmonicSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly
open Certificates.PairedV2
open P5Z.U1011OriginalPairedFixedMaskHarmonic (outerUnion outerUnion_all e0Rows e1Rows)
open P5Z.U1011OriginalSixteenPairedFibreGain

theorem measurableSet_actual_pairCell (r : Row) :
    MeasurableSet (FullMask.P1E0E1.pairCell r) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)))

theorem measurableSet_actual_outerUnion (S : Finset Row) : MeasurableSet (outerUnion S) :=
  Finset.measurableSet_biUnion S (fun r _ => measurableSet_actual_pairCell r)

/-- An ascending real mask used ONLY to apply the already proved exact
U6 transpose integral identity. The concrete native mask is unchanged. -/
def ascendingRealMask (S : Finset Row) : Set (ℝ × ℝ) := Prod.swap ⁻¹' outerUnion S

theorem measurableSet_ascendingRealMask (S : Finset Row) :
    MeasurableSet (ascendingRealMask S) :=
  (measurableSet_actual_outerUnion S).preimage measurable_swap

theorem ascending_twice_actual (S : Finset Row) :
    P5Z.U1011OriginalSixteenOuterFibre.ascendingMask (ascendingRealMask S) = outerUnion S := by
  ext q
  simp [P5Z.U1011OriginalSixteenOuterFibre.ascendingMask, ascendingRealMask]

/-- Exact original R-denominator retained U6 integral in decreasing
outer coordinates, with both transposes explicitly discharged. -/
theorem u6_integral_eq_actual_outer (S : Finset Row) :
    retainedEstimatorIntegral (fun x => x ∈ ascendingPointMask S) 0 = retainedU6 (outerUnion S) := by
  have h := retainedU6_eq_original_adopted (ascendingRealMask S)
    (measurableSet_ascendingRealMask S)
  rw [ascending_twice_actual] at h
  simpa only [ascendingRealMask, ascendingPointMask, mem_preimage,
    Prod.swap_prod_mk, mem_setOf_eq] using h.symm

/-- The two independently named kernels are literally the same full16
original bank and switched fallback, not two assumed matching means. -/
theorem actual_kernel_identity :
    P5Z.U1011OriginalPairedFixedMaskHarmonic.actualMinimum =
      P5Z.U1011OriginalSixteenOuterFibre.actualMinimum := rfl

theorem u11_integral_eq_actual_outer (S : Finset Row) :
    (∫ v in originalDomain (outerUnion S),
      P5Z.U1011OriginalPairedFixedMaskHarmonic.weighted v) = retainedU11 (outerUnion S) := by
  simpa only [P5Z.U1011OriginalPairedFixedMaskHarmonic.weighted, actual_kernel_identity] using
    (retainedU11_eq_original_integral (outerUnion S) (measurableSet_actual_outerUnion S)).symm

/-- Both signs read EXACTLY nativeMask(outerUnion S) N on their native
last prime pair. S is fixed outside N and contains only original rows. -/
def pairedNative (S : Finset Row) (N : ℕ) : ℝ := nativeU6 S 0 N -
  nativeHarmonicSum N (nativeMask (outerUnion S) N)
    P5Z.U1011OriginalPairedFixedMaskHarmonic.actualMinimum

/-- All analytic harmonic suppliers and all SAME-mask identifications
are concrete proved sources. No hMaskMean/hCellMean premise remains. -/
theorem tendsto_pairedNative (S : Finset Row) :
    Tendsto (pairedNative S) atTop (𝓝 (pairedRetained (outerUnion S))) := by
  have h6 := tendsto_nativeU6 S 0 (by norm_num)
  have h11 := P5Z.U1011OriginalPairedFixedMaskHarmonic.tendsto_native_staticRows S
  have ht := h6.sub h11
  rw [u6_integral_eq_actual_outer S, u11_integral_eq_actual_outer S] at ht
  exact ht

theorem outerUnion_empty : outerUnion (∅ : Finset Row) = ∅ := by
  ext q
  simp [outerUnion]

/-- True native harmonic change equals the REAL original deleted gain
integral. No four-tuple mask or independently selected E is inserted. -/
theorem tendsto_pairedNative_change (S : Finset Row) :
    Tendsto (fun N : ℕ => pairedNative S N - pairedNative ∅ N) atTop
      (𝓝 (∫ q in pairRectangle ∩ outerUnion S, signedPairGainDensity q)) := by
  have ht := (tendsto_pairedNative S).sub (tendsto_pairedNative ∅)
  rw [outerUnion_empty,
    pairedRetained_change_eq_deleted_gain (outerUnion S) (measurableSet_actual_outerUnion S)] at ht
  exact ht

/-- Literal original all-E0/E1 native pair functional. The correction
has R=.5-u-t; both terms use the actual adopted native deletion predicate. -/
def actualAdoptedPairedNative (N : ℕ) : ℝ :=
  nativeU6 (Finset.univ : Finset Row) 0 N - nativeHarmonicSum N
    (FullMask.P1E0E1.deletionMask (N : ℝ))
    P5Z.U1011OriginalPairedFixedMaskHarmonic.actualMinimum

theorem actualAdoptedPairedNative_eq (N : ℕ) :
    actualAdoptedPairedNative N = pairedNative (Finset.univ : Finset Row) N := by
  simp only [actualAdoptedPairedNative, pairedNative, outerUnion_all, nativeMask_actual_adopted]

theorem tendsto_actual_adopted_paired_native :
    Tendsto actualAdoptedPairedNative atTop (𝓝 (pairedRetained FullMask.P1E0E1.pairRegion)) := by
  have ht := tendsto_pairedNative (Finset.univ : Finset Row)
  rw [outerUnion_all] at ht
  exact ht.congr' (Eventually.of_forall (fun N => (actualAdoptedPairedNative_eq N).symm))

theorem tendsto_actual_adopted_paired_native_gain :
    Tendsto (fun N : ℕ => actualAdoptedPairedNative N - pairedNative ∅ N) atTop
      (𝓝 (∫ q in pairRectangle ∩ FullMask.P1E0E1.pairRegion, signedPairGainDensity q)) := by
  have ht := tendsto_pairedNative_change (Finset.univ : Finset Row)
  rw [outerUnion_all] at ht
  exact ht.congr' (Eventually.of_forall (fun N => by rw [actualAdoptedPairedNative_eq]))

/-- The independently source-tagged actual E0 and E1 subfamilies also
have concrete SAME-mask paired limits; no numerical endpoint is asserted. -/
theorem tendsto_actual_e0_paired_native :
    Tendsto (pairedNative e0Rows) atTop
      (𝓝 (pairedRetained FullMask.P1E0E1.e0PairRegion)) := by
  simpa only [P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_e0] using tendsto_pairedNative e0Rows

theorem tendsto_actual_e1_paired_native :
    Tendsto (pairedNative e1Rows) atTop
      (𝓝 (pairedRetained FullMask.P1E0E1.e1PairRegion)) := by
  simpa only [P5Z.U1011OriginalPairedFixedMaskHarmonic.outerUnion_e1] using tendsto_pairedNative e1Rows

end
end ImbalancedChen.P5OriginalSameMaskPairedNativeGainSourceOnly
