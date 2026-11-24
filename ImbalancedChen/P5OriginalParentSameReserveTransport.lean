import ImbalancedChen.P5HistoricalActualReserve64Budget
import ImbalancedChen.P1HistoricalFifthFullOriginalFloorEnvelope

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original whole-parent positive integral and the complete64 certificate
use exactly the SAME actual reserve.  The retained domain here is the
buffered domain at e, not its zero-buffer counterpart.  Splitting the
parent into this retained domain and its actual complement, and then
using the existing kernel modulus on the retained domain, charges the
original mass/modulus expression exactly once.  No B13 domain-motion
error, second eta, oldBranchDefect, or assumed floor licence is added.

The final comparison uses the original fourth producer and the actual
licensed owner of each source index.  This module supplies transport of
the independently defined parent integral, not the missing old stored
Jensen/Taylor certificate itself.
-/
namespace ImbalancedChen.P5OriginalParentSameReserveTransport
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1FifthUnitBoxGainDecomposition
open P1FifthUnitBoxLiteralGainLower P1FifthPositivePartActualOwner
open P1LiteralVariableFifthCompactSupplier P1OriginalFifthLiteralKernelModulus
open P1OriginalFifthActualB13IntegralError P1OriginalFifthMovingMeshFubiniBridge
open P1OriginalFifthAdoptedOwnerBank P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthIndexedBankError P1HistoricalFifthTypedBaseGeometry
open P5AllChildrenReserveReassembly P5HistoricalMask56FullSourceChildren
open P5HistoricalActualReserve64Budget P5OriginalFourthFifthSourceInputs
open P1HistoricalFifthFullOriginalFloorEnvelope

/-- Exact source-index union: each retained point is integrated once.
The literal positive kernel and the B13 positive kernel are definitionally
the same max(0,signed kernel), not two different source policies. -/
theorem indexedIntegral_eq_same_positive_owner_sum
    (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    indexedIntegral i e q chi omega e =
      ∑ j ∈ licensedOwners i e q chi omega,
        literalPositiveRawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j := by
  have hg := archiveRow_baseGeometry i
  unfold indexedIntegral indexedDomain ownerUnion
  change (∫ t in ⋃ j ∈ licensedOwners i e q chi omega,
      rawOwnerDomain (archiveRow i) e chi (refinedMesh q) omega j,
      literalPositiveRawKernel (e : ℝ) (archiveRow i) t) = _
  rw [integral_biUnion_finset (licensedOwners i e q chi omega)
    (fun j _ => rawOwnerDomain_measurable (archiveRow i) e chi (refinedMesh q) omega j)
    (show Set.PairwiseDisjoint (licensedOwners i e q chi omega : Set (Label5 (refinedMesh q)))
      (fun j => rawOwnerDomain (archiveRow i) e chi (refinedMesh q) omega j) from by
        intro j _hj k _hk hjk
        apply Set.disjoint_left.mpr
        intro t htj htk
        exact hjk (logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96)
          htj.2.2.2.1 htk.2.2.2.1))
    (fun j _ => integrableOn_literalPositiveRawKernel_rawOwner
      (archiveRow i) hg.1 hg.2.2.1 e chi (refinedMesh q) omega j)]
  rfl

/-- A whole-parent positive integral loses at most the actual complete64
reserve, with its original omitted set and original retained volume.
This is valid before imposing the small-buffer/common-mesh schedule. -/
theorem original_parentIntegral_sub_reserve_le_indexedIntegral
    (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    parentIntegral (archiveRow i) - indexedActualReserve64 i e q chi omega ≤
      indexedIntegral i e q chi omega e := by
  let S := indexedDomain i e q chi omega e
  let D := (archiveRow i).originalBox \ S
  have hg := archiveRow_baseGeometry i
  have hS : MeasurableSet S := ownerUnion_measurable _ _ _ _ _ _
  have hSparent : S ⊆ (archiveRow i).originalBox := by
    intro t ht
    exact (indexedDomain_subset_parent i e q chi omega e ht).1
  have hparentCube : (archiveRow i).originalBox ⊆
      positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ) := by
    rw [← archive_fixedParent_eq_raw i]
    exact fixedParent_subset_positiveCube (archiveRow i) hg.1 hg.2.2.1
  have hSCube := hSparent.trans hparentCube
  have hDparent : D ⊆ (archiveRow i).originalBox := sdiff_subset
  have hparentFinite : volume (archiveRow i).originalBox < ∞ := by
    rw [rawBox_volume _ hg.1]
    exact ENNReal.ofReal_lt_top
  have hSFinite : volume S < ∞ := (measure_mono hSparent).trans_lt hparentFinite
  have hDFinite : volume D < ∞ := (measure_mono hDparent).trans_lt hparentFinite
  have hparentInt := positiveKernel_integrableOn_of_subset
    (archiveRow i) 0 (archiveRow i).originalBox hparentCube
  have hsplit : (∫ t in D, positiveKernel (archiveRow i) 0 t) =
      parentIntegral (archiveRow i) - ∫ t in S, positiveKernel (archiveRow i) 0 t := by
    simpa only [parentIntegral, archive_fixedParent_eq_raw] using
      setIntegral_sdiff hS hparentInt hSparent
  have hlost : (∫ t in D, positiveKernel (archiveRow i) 0 t) ≤
      rowMassBound (archiveRow i) * volume.real D := by
    have hn := norm_setIntegral_le_of_norm_le_const hDFinite (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left 0 _)]
      exact positive_kernel_le_rowMassBound (archiveRow i) 0 (by norm_num) t
        (hparentCube (hDparent ht)))
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, Measure.real] using hn)
  have hmotion := (abs_le.mp (positiveKernel_integral_motion_le
    (archiveRow i) (e : ℝ) S hSCube hSFinite)).1
  have hD : rawOmitted (archiveRow i) e chi (refinedMesh q) omega
      (licensedOwners i e q chi omega) = D := by
    rw [rawOmitted, archive_rawRetained_eq_indexedDomain]
  rw [indexedActualReserve64_eq_one_parent, hD]
  change parentIntegral (archiveRow i) -
      (rowMassBound (archiveRow i) * volume.real D +
        rowModulus (archiveRow i) (e : ℝ) * volume.real S) ≤
      ∫ t in S, positiveKernel (archiveRow i) (e : ℝ) t
  dsimp only [Measure.real] at hlost ⊢
  linarith

/-- Both original choices of lower bound (the old whole-parent floor
and the complete64 floor) can now be compared to the SAME actual owner
sum after subtracting this one reserve.  No actual ancestor is replaced
by an equality with the all-fifteen upper envelope. -/
theorem original_parentIntegral_sub_reserve_le_actual_owner_sum
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    parentIntegral (archiveRow i) - indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j
          originalRows4 originalAdmission4 := by
  have hp := original_parentIntegral_sub_reserve_le_indexedIntegral i e q chi omega
  rw [indexedIntegral_eq_same_positive_owner_sum] at hp
  exact hp.trans (Finset.sum_le_sum (fun j hj =>
    original_positive_surrogate_le_actual_owner i e he q chi omega hw hwr j hj))

end
end ImbalancedChen.P5OriginalParentSameReserveTransport
