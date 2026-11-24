import ImbalancedChen.P5OriginalParentJensenIntegral
import ImbalancedChen.P5OriginalTaylorActualMidpointIntegral
import ImbalancedChen.P5OriginalStoredOldArchiveBinding
import ImbalancedChen.P5OriginalStoredFifthEndpoint
import ImbalancedChen.P5HistoricalActualReserve64Schedule

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual292633 stored parent maxima, with their original Jensen/Taylor
old branch, feed the actual full original fifth integral.  The Taylor
finite facts are extracted from the ORIGINAL stored-old binding when
that branch is strictly above Jensen.  The closed original parent Jensen
geometry, full weighted Hessian and genuine five-dimensional midpoint
theorems discharge the analytic lower bounds.  No saved-floor inequality
or target-equivalent licence is a hypothesis.

The maximum is taken separately at every source position BEFORE summing.
Both alternatives subtract exactly the same indexedActualReserve64,
already paid by R05.  The fixed oldBranchDefect is absent: it is not
claimed zero, small, or absorbed by rounding.  Its actual old branch is
proved by the original argument.  No policy change or added old saving,
factor64, ordering factorial, Chen quarter or second reserve is used.
-/
namespace ImbalancedChen.P5OriginalFullFifthFloorIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P1OriginalFifthGrid400RefinedFullBoxCover P1FifthUnitBoxGainDecomposition
open P1FifthUnitBoxLiteralGainLower P1LiteralVariableFifthCompactSupplier
open P1OriginalFifthActualB13IntegralError P1OriginalFifthAdoptedOwnerBank
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P5OriginalParentJensenRawFields P5OriginalParentJensenIntegral
open P5OriginalTaylorActualSignedKernel P5OriginalTaylorAffineBranchBinding
open P5OriginalTaylorAffineRatioDerivatives P5OriginalTaylorRationalData
open P5OriginalTaylorActualMidpointIntegral P5OriginalStoredOldArchiveBinding
open P5OriginalParentSameReserveTransport P5OriginalStoredFifthEndpoint
open P5FullStoredParentSameOwnerBinding P5HistoricalMask56FullSourceChildren
open P1HistoricalFifthFullOriginalFloorEnvelope P5FullArchiveOwnerIntegralAssembly
open P5OriginalFifthArchiveActualMean P5OriginalFourthFifthSourceInputs
open P5HistoricalActualReserve64Budget P5HistoricalActualReserve64Schedule
open ImbalancedChen.Certificates.P2DirectedLogRounding

/-- The signed Taylor profile agrees with the original signed literal
kernel on its ACTUAL finite smooth box, including argument-two endpoints.
Only afterwards is the original positive-part parent used as a majorant. -/
theorem original_Taylor_signedIntegral_le_parentIntegral
    (i : ArchiveIndex) (h : TaylorFiniteFacts (archiveRow i)) :
    (∫ t in (archiveRow i).originalBox,
      originalTaylorSignedKernel (archiveRow i) t) ≤ parentIntegral (archiveRow i) := by
  have hb := branchFacts (archiveRow i) h.2.2.1
  have heq (t : Fin 5 → ℝ) (ht : t ∈ (archiveRow i).originalBox) :
      originalTaylorSignedKernel (archiveRow i) t = literalRawKernel 0 (archiveRow i) t := by
    have hclosed := originalBox_subset_rawClosedBox (archiveRow i) ht
    rcases actual_ranges (archiveRow i) h t hclosed with
      ⟨h4, ha2, hao, hon, hn4, _hnMax, _hoMax, _hdelta⟩
    have hn : originalTaylorNewArgument (archiveRow i) t =
        affineArgument (newAffine (archiveRow i)) t := by
      unfold originalTaylorNewArgument
      rw [original_new_eq_affine (archiveRow i) (newSide (archiveRow i)) hb.new_active t hclosed]
      rfl
    have ho : originalTaylorOldArgument t = affineArgument (oldAffine (archiveRow i)) t := by
      unfold originalTaylorOldArgument
      rw [original_old_eq_selected_affine (archiveRow i) (newSide (archiveRow i))
        (oldSides (archiveRow i)) (selected (archiveRow i)) hb t hclosed]
      rfl
    apply originalTaylorSignedKernel_eq_literal (archiveRow i) t h4
    · rw [hn]
      exact ⟨ha2.trans (hao.trans hon.le), hn4⟩
    · rw [ho]
      exact ⟨ha2.trans hao, hon.le.trans hn4⟩
  have hInt : (∫ t in (archiveRow i).originalBox,
      originalTaylorSignedKernel (archiveRow i) t) =
      ∫ t in (archiveRow i).originalBox, literalRawKernel 0 (archiveRow i) t :=
    setIntegral_congr_fun (measurableSet_originalBox (archiveRow i)) heq
  have hg := archiveRow_baseGeometry i
  have hCube : (archiveRow i).originalBox ⊆
      positiveCube (1 / 400 : ℝ) (19 / 96 : ℝ) := by
    rw [← archive_fixedParent_eq_raw i]
    exact fixedParent_subset_positiveCube (archiveRow i) hg.1 hg.2.2.1
  have hL := ((continuousOn_literalRawKernel 0 (1 / 400) (19 / 96)
      (by norm_num) (archiveRow i)).integrableOn_compact
        (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc))).mono_set hCube
  have hP := positiveKernel_integrableOn_of_subset
    (archiveRow i) 0 (archiveRow i).originalBox hCube
  rw [hInt, parentIntegral, archive_fixedParent_eq_raw]
  exact setIntegral_mono_on hL hP (measurableSet_originalBox (archiveRow i))
    (fun _ _ => le_max_right 0 _)

/-- Actual downward Q80 rounding of the original rational Taylor bound.
The rounding is used once, with its sign valid even for a negative input. -/
theorem original_Taylor_floor_le_parentIntegral
    (i : ArchiveIndex) (h : TaylorFiniteFacts (archiveRow i)) :
    ((taylorFloorZ (archiveRow i) : ℝ) / (dyadicScale 80 : ℝ)) ≤
      parentIntegral (archiveRow i) := by
  have hfloorQ : (taylorFloorZ (archiveRow i) : ℚ) / dyadicScale 80 ≤
      taylorLowerQ (archiveRow i) := by
    simpa only [roundDown, taylorFloorZ, dyadicScale, mul_comm] using
      roundDown_le 80 (taylorLowerQ (archiveRow i))
  have hfloorR : (taylorFloorZ (archiveRow i) : ℝ) / (dyadicScale 80 : ℝ) ≤
      (taylorLowerQ (archiveRow i) : ℝ) := by exact_mod_cast hfloorQ
  exact hfloorR.trans ((original_taylorLowerQ_le_signedIntegral (archiveRow i) h).trans
    (original_Taylor_signedIntegral_le_parentIntegral i h))

/-- The complete actual saved OLD floor is now below its true positive
parent integral. The archive supplies Taylor finite facts only when its
saved old numerator is strictly above the original Jensen numerator. -/
theorem original_stored_old_floor_le_parentIntegral (i : ArchiveIndex) :
    ((storedAt i).oldQ80 : ℝ) / (dyadicScale 80 : ℝ) ≤ parentIntegral (archiveRow i) := by
  by_cases hj : (storedAt i).oldQ80 ≤ originalParentJensenFloorZ (archiveRow i)
  · have hjQ := div_le_div_of_nonneg_right
      (show ((storedAt i).oldQ80 : ℚ) ≤ (originalParentJensenFloorZ (archiveRow i) : ℚ) by
        exact_mod_cast hj) (dyadicScale_pos 80).le
    have hjR : ((storedAt i).oldQ80 : ℝ) / (dyadicScale 80 : ℝ) ≤
        (originalParentJensenFloorQ (archiveRow i) : ℝ) := by
      dsimp only [originalParentJensenFloorQ]
      exact_mod_cast hjQ
    exact hjR.trans (original_parent_Jensen_floor_le_parentIntegral i)
  · have ht : originalParentJensenFloorZ (archiveRow i) < (storedAt i).oldQ80 :=
      lt_of_not_ge hj
    rw [strict_stored_old_eq_original_taylor_floor i ht]
    exact original_Taylor_floor_le_parentIntegral i (strict_stored_taylor_primitive_facts i ht)

/-- Original complete64 integer normalization, before choosing the saved
parent maximum. All children retain their original source position. -/
theorem childSumZ_div_scale_eq_wire64 (i : ArchiveIndex) :
    (childSumZ i : ℚ) / dyadicScale 80 = indexedWireFloor64 i := by
  simp only [childSumZ, indexedWireFloor64,
    P5OriginalGenericWireFloorReceiver.rowFloorQ, Int.cast_sum, Finset.sum_div]

/-- Every ACTUAL saved new floor, including its stronger old Taylor/Jensen
branch, is attached to its own actual owner integral. The common reserve
is subtracted from either alternative once, then the actual max is taken. -/
theorem each_original_stored_floor_sub_reserve
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    (storedNewQ i : ℝ) - indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j
          originalRows4 originalAdmission4 := by
  by_cases hc : (storedAt i).oldQ80 ≤ childSumZ i
  · have hnew : storedNewQ i = indexedWireFloor64 i := by
      rw [storedNewQ, proposed_all_stored_parent_replacements i, max_eq_right hc]
      exact childSumZ_div_scale_eq_wire64 i
    rw [hnew]
    exact (each_original_parent_wire_floor_sub_reserve i e q chi omega).trans
      (Finset.sum_le_sum (fun j hj =>
        original_positive_surrogate_le_actual_owner i e he q chi omega hw hwr j hj))
  · have hnew : (storedNewQ i : ℝ) =
        ((storedAt i).oldQ80 : ℝ) / (dyadicScale 80 : ℝ) := by
      simp only [storedNewQ, proposed_all_stored_parent_replacements i,
        max_eq_left (le_of_not_ge hc), Rat.cast_div, Rat.cast_intCast]
    rw [hnew]
    exact (sub_le_sub_right (original_stored_old_floor_le_parentIntegral i) _).trans
      (original_parentIntegral_sub_reserve_le_actual_owner_sum i e he q chi omega hw hwr)

/-- The whole original yellow node: all292633 true saved parent floors
feed the independently defined actual original total fifth integral.
There is no oldBranchDefect, old-floor licence, finite checker hypothesis,
mask restriction, target integral field or assumed actual total bound. -/
theorem full_original_stored_floor_sub_reserve
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    (∑ i : ArchiveIndex, (storedNewQ i : ℝ)) -
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q chi omega) ≤
      archiveFifthIntegral originalRows4 originalAdmission4 e q chi omega := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ArchiveIndex))
    (fun i _ => each_original_stored_floor_sub_reserve i e he q chi omega hw hwr)
  have hsum := archiveFifthIntegral_eq_indexed_owner_sum
    originalRows4 originalAdmission4 e q chi omega
  rw [licensedIndices_eq_univ] at hsum
  rw [hsum]
  simpa only [Finset.sum_sub_distrib] using hs

/-- Universal actual endpoint, usable on any further refined common
schedule. Only the original parameters occur; the exact reserve remains
observable and is supplied by R05 or its compatible refined schedule. -/
theorem original_fifth_endpoint_sub_reserve
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    (3037921066812732539869 / 302231454903657293676544 : ℝ) -
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q chi omega) ≤
      archiveFifthIntegral originalRows4 originalAdmission4 e q chi omega := by
  simpa only [original_stored_fifth_endpoint] using
    full_original_stored_floor_sub_reserve e he q chi omega hw hwr

open P5HistoricalUniformExtraGatePayment P5HistoricalCanonicalFilterReserve
open P5HistoricalIndexedTrimGeometry P4AAll22OriginalKLedger20261024zSourceOnly

/-- Original safe fifth saving, with one e/q, the original density u_d/8
allocation, the unchanged exact endpoint, and the original fourth source.
The child reserve is paid once; no separate old-literal error is spent. -/
theorem exists_original_fifth_safe_integral
    (omega : ℝ) (homega : 0 < omega) (hw : omega ≤ 1 / 800) :
    ∃ e : ℚ, ∃ q : ℕ, 0 < (e : ℝ) ∧ (e : ℝ) < 3 / 51200 ∧
      e ≤ archiveGateMargin / 4 ∧ 0 < q ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ (e : ℝ) / 20 ∧
      logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      canonicalHistoryBankCost q ((e : ℝ) / 20) omega = 0 ∧
      gateRejectedBankCost e q ((e : ℝ) / 20) omega = 0 ∧
      (∑ i : ArchiveIndex, indexedActualReserve64 i e q ((e : ℝ) / 20) omega) <
        densityReserve / 8 ∧
      (10051 / 1000000 : ℝ) <
        archiveFifthIntegral originalRows4 originalAdmission4 e q ((e : ℝ) / 20) omega := by
  obtain ⟨e, q, he, hemax, hem, hq, hstep, hrough, hhistory, hgate, hbudget, hmargin⟩ :=
    exists_original_safe_fifth_margin_payment omega homega hw
  have heQ : (0 : ℚ) ≤ e := by exact_mod_cast he.le
  have hwr : omega < (19 / 96 : ℝ) := by linarith
  have hwhole := original_fifth_endpoint_sub_reserve e heQ q ((e : ℝ) / 20) omega homega hwr
  exact ⟨e, q, he, hemax, hem, hq, hstep, hrough, hhistory, hgate, hbudget, by linarith⟩

end
end ImbalancedChen.P5OriginalFullFifthFloorIntegral
