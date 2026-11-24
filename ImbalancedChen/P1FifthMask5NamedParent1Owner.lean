import ImbalancedChen.P1FifthMask5RawOwnerLicence

-- Proposed target: ImbalancedChen/P1FifthMask5NamedParent1Owner.lean
-- SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT / HELD / NOT_ROOT_ACCEPTED.
-- The literal row is saved parent index 1 of the pinned accepted-witness NPZ.
-- A source-to-Lean byte equality is deliberately an explicit input below.

namespace ImbalancedChen.P1FifthMask5NamedParent1Owner
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1FifthMask5RawOwnerLicence

def selectedParent1 : FifthWireRow :=
  { grid := 400
    lo := ![30, 29, 28, 26, 25]
    mask := 28
    vertexGapSum := 5232
    ratioA := 3192
    ratioB := 800 }

-- The fifth row mask 28 is independent of the old third XZ branch.
-- In particular positive thirdgap and positive XZ pair gate are
-- separately checked rational facts for this one stored row.
theorem selectedParent1_exact_margins :
    ascendingThirdNumerator selectedParent1 = 1312 ∧
    descendingThirdNumerator selectedParent1 = 1892 ∧
    ascendingPairNumerator selectedParent1 = 1760 ∧
    descendingPairNumerator selectedParent1 = 2340 := by
  norm_num [selectedParent1, ascendingThirdNumerator, descendingThirdNumerator,
    ascendingPairNumerator, descendingPairNumerator]

theorem selectedParent1_whole_raw_check :
    mask5WholeRawCheck selectedParent1 = true := by
  decide

noncomputable section
open Set
open scoped Classical

theorem selectedParent1_decoded_xz_gate
    (e : ℚ) (hemax : e ≤ 3 / 51200) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent1 m) :
    xzCellGateCheck e m r.cell = true :=
  decoded_xz_gate_of_wholeCheck selectedParent1 selectedParent1_whole_raw_check
    e hemax m r hr

-- The raw box is attached to the actual original fifth owner only on
-- cells licensed by the inherited firstStop/third history and original
-- e/chi/omega schedule.  The row's saved score fields supply none of these.
theorem selectedParent1_cell_mem_rawOwnerDomain
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (J5 : Finset (Label5 m))
    (r : FifthRow m) (hr : r ∈ decodeFifthRows selectedParent1 m)
    (hJ : r.cell ∈ J5) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5 ∧
      t ∈ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
        selectedParent1 e chi m omega r.cell := by
  have hwhole := selectedParent1_whole_raw_check
  have hcore := (Bool.and_eq_true.mp hwhole).1
  have hgate := selectedParent1_decoded_xz_gate e hemax m r hr
  have hfull := decoded_mask5_fullCell selectedParent1 hcore e he hemax chi omega
    hchi m hstep hw J5 r hr hJ t ht hgate
  have hraw := (decodeFifthRows_source_geometry selectedParent1 m r hr t ht).2.2.2
  exact ⟨hfull.1, hraw, hfull.2⟩

-- Missing actual archive-byte binding remains visible at the call site.
theorem source_bound_parent1_cell_mem_rawOwnerDomain
    (archiveRow1 : FifthWireRow) (hsource : archiveRow1 = selectedParent1)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (J5 : Finset (Label5 m))
    (r : FifthRow m) (hr : r ∈ decodeFifthRows archiveRow1 m)
    (hJ : r.cell ∈ J5) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5 ∧
      t ∈ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
        archiveRow1 e chi m omega r.cell := by
  subst archiveRow1
  exact selectedParent1_cell_mem_rawOwnerDomain e he hemax chi omega hchi
    m hstep hw J5 r hr hJ t ht

end
end ImbalancedChen.P1FifthMask5NamedParent1Owner
