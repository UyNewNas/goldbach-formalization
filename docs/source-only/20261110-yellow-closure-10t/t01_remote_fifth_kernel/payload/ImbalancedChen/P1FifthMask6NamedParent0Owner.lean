import ImbalancedChen.P1FifthMask6RawOwnerLicence

-- Proposed target: ImbalancedChen/P1FifthMask6NamedParent0Owner.lean
-- SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT / HELD / NOT_ROOT_ACCEPTED.
-- The literal row is saved parent index 0 of the pinned accepted-witness NPZ.
-- A source-to-Lean byte equality is deliberately an explicit input below.

namespace ImbalancedChen.P1FifthMask6NamedParent0Owner
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1FifthMask6RawOwnerLicence

def selectedParent0 : FifthWireRow :=
  { grid := 400
    lo := ![31, 30, 27, 26, 25]
    mask := 28
    vertexGapSum := 5984
    ratioA := 3200
    ratioB := 800 }

-- These are the two independent certificate questions.  The original
-- fifth mask 28 in the saved row is unrelated to which old third branch
-- supplies the original history.
theorem selectedParent0_exact_margins :
    ascendingThirdNumerator selectedParent0 = 1320 ∧
    descendingThirdNumerator selectedParent0 = 1932 ∧
    ascendingPairNumerator selectedParent0 = 1704 ∧
    descendingPairNumerator selectedParent0 = 2316 := by
  norm_num [selectedParent0, ascendingThirdNumerator, descendingThirdNumerator,
    ascendingPairNumerator, descendingPairNumerator]

theorem selectedParent0_whole_raw_check :
    mask6WholeRawCheck selectedParent0 = true := by
  decide

noncomputable section
open Set
open scoped Classical

-- The row's YZ pair gate is proved at every genuinely contained decoded
-- cell, with the inclusive e<=yzGap test from the original fullGamma.
theorem selectedParent0_decoded_yz_gate
    (e : ℚ) (hemax : e ≤ 3 / 51200) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent0 m) :
    yzCellGateCheck e m r.cell = true :=
  decoded_yz_gate_of_wholeCheck selectedParent0 selectedParent0_whole_raw_check
    e hemax m r hr

-- This is the actual retained old-fifth owner domain.  The selected-cell
-- context and schedule remain explicit, so no raw data field is mistaken
-- for firstStop, third history, or a current fourth cap.
theorem selectedParent0_cell_mem_rawOwnerDomain
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (J5 : Finset (Label5 m))
    (r : FifthRow m) (hr : r ∈ decodeFifthRows selectedParent0 m)
    (hJ : r.cell ∈ J5) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5 ∧
      t ∈ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
        selectedParent0 e chi m omega r.cell := by
  have hwhole := selectedParent0_whole_raw_check
  have hcore := (Bool.and_eq_true.mp hwhole).1
  have hgate := selectedParent0_decoded_yz_gate e hemax m r hr
  have hfull := decoded_mask6_fullCell selectedParent0 hcore e he hemax chi omega
    hchi m hstep hw J5 r hr hJ t ht hgate
  have hraw := (decodeFifthRows_source_geometry selectedParent0 m r hr t ht).2.2.2
  exact ⟨hfull.1, hraw, hfull.2⟩

-- The frozen source row is literal data, but the selected-stream payload
-- has no accepted Lean byte-binding theorem.  This statement exposes the
-- exact missing bridge rather than identifying an arbitrary loaded row.
theorem source_bound_parent0_cell_mem_rawOwnerDomain
    (archiveRow0 : FifthWireRow) (hsource : archiveRow0 = selectedParent0)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (J5 : Finset (Label5 m))
    (r : FifthRow m) (hr : r ∈ decodeFifthRows archiveRow0 m)
    (hJ : r.cell ∈ J5) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5 ∧
      t ∈ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
        archiveRow0 e chi m omega r.cell := by
  subst archiveRow0
  exact selectedParent0_cell_mem_rawOwnerDomain e he hemax chi omega hchi
    m hstep hw J5 r hr hJ t ht

end
end ImbalancedChen.P1FifthMask6NamedParent0Owner
