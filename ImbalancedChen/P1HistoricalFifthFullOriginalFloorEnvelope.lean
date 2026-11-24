import ImbalancedChen.P1HistoricalFifthRemainingChildFacts
import ImbalancedChen.P5FullArchiveOwnerIntegralAssembly
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
import ImbalancedChen.P5OriginalFourthFifthSourceInputs

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original full subdivision run processes all292633 source parents.
Use the already proved arbitrary-mask Jensen receiver at every position,
including the complement of the earlier mask5/6 THIRD-owner subfamily.
Original stored new/old fields, source masks and64 child positions are
unchanged. The old-branch defect and actual child-owner reserve remain
explicitly subtracted; no assertion that either fits a budget is made.

The fourth input is O's independent original byte-backed originalRows4
with its actual originalAdmission4 filter. Geometry is derived from that
filter. No geometry licence, parent equality or desired integral bound
is a caller premise. This does not certify the full sixth/eighth policy.

The new child-fact bodies, G's stored replacement body, all inherited
archive guards and O's byte elaboration remain UNEVALUATED.
-/
namespace ImbalancedChen.P1HistoricalFifthFullOriginalFloorEnvelope
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalVariableFourthContinuation P2OriginalFourthCapProducerInterface
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthUnitBoxGainDecomposition P1FifthUnitBoxLiteralGainLower
open P1FifthPositivePartActualOwner P1ActualVariableFifthProfiles
open P1ActualVariableFifthUntruncatedDomination
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P5OriginalGenericWireFloorReceiver P5HistoricalMask56FullSourceChildren
open P5LicensedRawOwnerActualGain P5FullStoredParentSameOwnerBinding
open P5FullArchiveOwnerIntegralAssembly P5OriginalFifthArchiveActualMean
open P5OriginalFourthFifthSourceInputs P1HistoricalFifthRemainingChildFacts

/-- Every source index supplies its own physical old fourth ancestor.
The earlier mask56 hypothesis was used only to obtain base geometry;
the independent full typed base theorem now supplies it for every i. -/
theorem original_positive_surrogate_le_actual_owner
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    literalPositiveRawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j ≤
      rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j
        originalRows4 originalAdmission4 := by
  have hg := archiveRow_baseGeometry i
  apply setIntegral_mono_on
    (integrableOn_literalPositiveRawKernel_rawOwner (archiveRow i) hg.1 hg.2.2.1
      e chi (refinedMesh q) omega j)
    (integrableOn_licensed_rawOwner i e he q chi omega hw hwr j hj
      originalRows4 originalAdmission4)
    (rawOwnerDomain_measurable (archiveRow i) e chi (refinedMesh q) omega j)
  intro t ht
  exact literalPositiveRawKernel_le_rawOwnerKernel e (by exact_mod_cast he)
    chi (refinedMesh q) omega originalRows4 originalAdmission4
    (fun r _hr hlic => originalAdmission4_geometry r hlic)
    (licensedOwners i e q chi omega) j
    (licensedOwner_selected_buffer i e q chi omega j hj) (archiveRow i) t ht

/-- The generic original Jensen proof is reused for the complete64-child
family. The new complementary source facts close its actual finite inputs;
no floor or real-integral estimate is hypothesized. -/
theorem each_original_parent_wire_floor_sub_reserve
    (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (indexedWireFloor64 i : ℝ) - indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        literalPositiveRawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j := by
  have hg := archiveRow_baseGeometry i
  have hs := original_parent64_wire_floor_sub_reserve (archiveRow i) hg.1 hg.2.2.1
    (archiveRow_all_child_facts i) e chi (refinedMesh q) omega
    (licensedOwners i e q chi omega)
  rw [selected_strict_owners_eq i e q chi omega] at hs
  simpa [indexedWireFloor64, indexedActualReserve64] using hs

/-- Each stored parent is compared to its own actual dynamic parent
integral, using BOTH original stored fields and exactly one64-child sum.
The old Jensen/Taylor branch is not paid by the child proof. -/
theorem each_original_parent_stored_floor_envelope
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    (storedNewQ i : ℝ) - (oldBranchDefectQ i : ℝ) -
        indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j
          originalRows4 originalAdmission4 := by
  have heq : (storedNewQ i : ℝ) - (oldBranchDefectQ i : ℝ) =
      (indexedWireFloor64 i : ℝ) := by
    exact_mod_cast stored_minus_old_defect_eq_wire64 i
  rw [heq]
  exact (each_original_parent_wire_floor_sub_reserve i e q chi omega).trans
    (Finset.sum_le_sum (fun j hj =>
      original_positive_surrogate_le_actual_owner i e he q chi omega hw hwr j hj))

/-- Exact H source-index/owner assembly into the independently defined
full original analytic integral. The source sum is now all ArchiveIndex,
not mask56Indices; no owner count, factor64, or duplicate old gain occurs. -/
theorem full_original_stored_floor_envelope
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    (∑ i : ArchiveIndex, (storedNewQ i : ℝ)) -
      (∑ i : ArchiveIndex, (oldBranchDefectQ i : ℝ)) -
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q chi omega) ≤
      archiveFifthIntegral originalRows4 originalAdmission4 e q chi omega := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ArchiveIndex))
    (fun i _hi => each_original_parent_stored_floor_envelope i e he q chi omega hw hwr)
  have hsum := archiveFifthIntegral_eq_indexed_owner_sum
    originalRows4 originalAdmission4 e q chi omega
  rw [licensedIndices_eq_univ] at hsum
  rw [hsum]
  simpa only [Finset.sum_sub_distrib] using hs

end
end ImbalancedChen.P1HistoricalFifthFullOriginalFloorEnvelope
