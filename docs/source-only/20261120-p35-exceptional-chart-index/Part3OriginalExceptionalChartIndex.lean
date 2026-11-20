import ImbalancedChen.Part3OriginalSignedExceptionalMode

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Exact reindexing of the exceptional chart from the endpoint-corrected
positive-level union to the original chartLevels of the trace source. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalExceptionalChartIndex20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest actualCoeff)
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open ActualCuspBasisWhittakerCoefficients20261102
open ActualOppositeBesselTransform20261112 (kTransform)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusCuspInput20261102
open OriginalFullModulusAssembly20261102
open OriginalExceptionalJNativeCompletion20261110 (exceptional originalLevels original_level_occurs)
open OriginalExceptionalPostRemovalPair20261113 (levels Slots)
open OriginalNativeCuspFunctionals20261102
open OriginalPositiveRawCauchy20261120 (rawSlot)
open OriginalOppositeRawChart20261120 (oppositeRawSlot)
open OriginalSignedExceptionalChart20261120 (signedRawSlot)
open OriginalSignedExceptionalMode20261120 (signedExceptionalMode)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

theorem level_mem_chart (D : OriginalData) (k : BlockKey) (upper : Bool)
    (z : ↥(levels D k upper)) : z.val.val ∈ chartLevels D k upper := by
  rcases Finset.mem_union.mp z.property with h | h <;> exact (Finset.mem_filter.mp h).2

/-- No physical level is lost or added when the two printed intervals
are used to index the occupied original chart. -/
theorem levels_image_eq_chart (D : OriginalData) (k : BlockKey) (upper : Bool) :
    (levels D k upper).image (fun z : ℕ+ => z.val) = chartLevels D k upper := by
  ext n
  constructor
  · intro hn
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
    exact level_mem_chart D k upper ⟨z,hz⟩
  · intro hn
    let z : ℕ+ := ⟨n,(levelCarrier_licensed D k (chartLevels_subset D k upper hn)).1⟩
    have hz : z ∈ levels D k upper := by
      exact Finset.mem_union.mpr (original_level_occurs D k upper hn)
    exact Finset.mem_image.mpr ⟨z,hz,rfl⟩

/-- A proof-irrelevant identification, preserving the actual level value. -/
def chartLevelEquiv (D : OriginalData) (k : BlockKey) (upper : Bool) :
    ↥(levels D k upper) ≃ ↥(chartLevels D k upper) where
  toFun z := ⟨z.val.val,level_mem_chart D k upper z⟩
  invFun z := ⟨⟨z.val,(levelCarrier_licensed D k (chartLevels_subset D k upper z.property)).1⟩,
    Finset.mem_union.mpr (original_level_occurs D k upper z.property)⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

theorem chartLevelEquiv_symm_val (D : OriginalData) (k : BlockKey) (upper : Bool)
    (z : ↥(chartLevels D k upper)) :
    ((chartLevelEquiv D k upper).symm z).val.val = z.val := rfl

/-- The same signed raw slot indexed by the literal trace chart level. -/
def chartSignedSlot (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (Y : ℝ)
    (z : ↥(chartLevels D k upper))
    (i : ↥(exceptional ((chartLevelEquiv D k upper).symm z).val)) : ℂ :=
  signedRawSlot D r k upper negativeM J j ell Y ⟨(chartLevelEquiv D k upper).symm z,i⟩

/-- The false branch is the actual native positive transform and row. -/
theorem chart_slot_positive (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (Y : ℝ)
    (z : ↥(chartLevels D k upper))
    (i : ↥(exceptional ((chartLevelEquiv D k upper).symm z).val))
    (hs : traceNegative D k negativeM = false) :
    let q := ((chartLevelEquiv D k upper).symm z).val
    chartSignedSlot D r k upper negativeM J j ell Y z i =
      nativeWeight q.val (spectralTest ell Y) i.val *
        (star (originalMFunctional J j ell q.val q.property i.val) *
          originalNFunctional D r k upper negativeM ell q.val q.property i.val) := by
  simp only [chartSignedSlot,signedRawSlot,hs,Bool.false_eq_true,if_false,rawSlot]

/-- The true branch is the actual eight-times K transform and raw row. -/
theorem chart_slot_opposite (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (Y : ℝ)
    (z : ↥(chartLevels D k upper))
    (i : ↥(exceptional ((chartLevelEquiv D k upper).symm z).val))
    (hs : traceNegative D k negativeM = true) :
    let q := ((chartLevelEquiv D k upper).symm z).val
    chartSignedSlot D r k upper negativeM J j ell Y z i =
      (8*kTransform (basisOrder q.val q.property i.val) (spectralTest ell Y)) *
        (star (originalMFunctional J j ell q.val q.property i.val) *
          originalNFunctional D r k upper negativeM ell q.val q.property i.val) := by
  simp only [chartSignedSlot,signedRawSlot,hs,if_true,oppositeRawSlot]

/-- Exact finite sum reindexing, including every strict exceptional
multiplicity at every original occupied chart level. -/
theorem signed_sum_eq_original_chart_sum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ) (Y : ℝ) :
    (∑ a : Slots D k upper, signedRawSlot D r k upper negativeM J j ell Y a) =
      ∑ z : ↥(chartLevels D k upper),
        ∑ i : ↥(exceptional ((chartLevelEquiv D k upper).symm z).val),
          chartSignedSlot D r k upper negativeM J j ell Y z i := by
  classical
  rw [Fintype.sum_sigma]
  refine Fintype.sum_equiv (chartLevelEquiv D k upper) _ _ ?_
  intro z
  simp only [chartSignedSlot,Equiv.symm_apply_apply]

/-- Restore the already-defined original test scale and both outer
scalars while changing only the exceptional chart indexing. -/
theorem signed_mode_eq_original_chart_sum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (M N : ℝ) (ell : D4 → ℤ) :
    signedExceptionalMode D r k upper negativeM J j M N ell =
      actualCoeff ((2^j:ℕ)*M/N) (if negativeM then -1 else 1) ell *
        (((M*Real.sqrt (fixedZ D upper):ℝ):ℂ) *
          ∑ z : ↥(chartLevels D k upper),
            ∑ i : ↥(exceptional ((chartLevelEquiv D k upper).symm z).val),
              chartSignedSlot D r k upper negativeM J j ell (chartY0 D k upper j N) z i) := by
  unfold signedExceptionalMode
  rw [signed_sum_eq_original_chart_sum]

end ImbalancedChen.Part3.OriginalExceptionalChartIndex20261120
end
