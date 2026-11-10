import ImbalancedChen.P1FifthMask6NamedParent0Owner
import ImbalancedChen.P1FifthMask5NamedParent1Owner

-- Proposed target: ImbalancedChen/P1FifthNamedParentsConcreteJ5.lean
-- SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT / HELD / NOT_ROOT_ACCEPTED.
-- A concrete, finite, source-row selected table fixed before omega and N.
-- This is a permitted local choice, not an identity with the historical
-- full adopted table or its numerical saving.

namespace ImbalancedChen.P1FifthNamedParentsConcreteJ5
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalCoarseFifthContinuation
open P1FifthMask6NamedParent0Owner
open P1FifthMask5NamedParent1Owner

noncomputable section
open scoped Classical

def namedJ5 (m : ℕ) : Finset (Label5 m) :=
  ((decodeFifthRows selectedParent0 m).image FifthRow.cell) ∪
    ((decodeFifthRows selectedParent1 m).image FifthRow.cell)

theorem parent0_cell_mem_namedJ5 (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent0 m) : r.cell ∈ namedJ5 m := by
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

theorem parent1_cell_mem_namedJ5 (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent1 m) : r.cell ∈ namedJ5 m := by
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨r, hr, rfl⟩

-- The original third-owner theorem supplies firstStop, whole-box order,
-- mesh width and rough lower-endpoint tests after the concrete table
-- membership. No raw fifth statistic is used as an inherited cap.
theorem parent0_mem_selected_namedJ5
    (e : ℚ) (hemax : e ≤ 3 / 51200) (chi omega : ℝ)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent0 m) :
    r.cell ∈ selectedFifthCells e chi m omega (namedJ5 m) := by
  have hcore := (Bool.and_eq_true.mp selectedParent0_whole_raw_check).1
  have hkey := P1FifthMask6RawOwnerLicence.mask6HistoryCheck_thirdOwnerKeyCheck
    selectedParent0 hcore
  exact P1FifthRawKeyThirdOwnerPersistence.decoded_third_owner_selected
    selectedParent0 hkey e hemax chi omega m hstep hw (namedJ5 m)
    r hr (parent0_cell_mem_namedJ5 m r hr)

theorem parent1_mem_selected_namedJ5
    (e : ℚ) (hemax : e ≤ 3 / 51200) (chi omega : ℝ)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent1 m) :
    r.cell ∈ selectedFifthCells e chi m omega (namedJ5 m) := by
  have hcore := (Bool.and_eq_true.mp selectedParent1_whole_raw_check).1
  have hkey := P1FifthMask5RawOwnerLicence.mask5HistoryCheck_thirdOwnerKeyCheck
    selectedParent1 hcore
  exact P1FifthRawKeyThirdOwnerPersistence.decoded_third_owner_selected
    selectedParent1 hkey e hemax chi omega m hstep hw (namedJ5 m)
    r hr (parent1_cell_mem_namedJ5 m r hr)

theorem parent0_original_stop_and_rough
    (e : ℚ) (hemax : e ≤ 3 / 51200) (chi omega : ℝ)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent0 m) :
    historicalPrefixProject (by omega : 3 ≤ 5) r.cell ∈
        HistoricalThirdCoarse.cells (e : ℝ) chi m ∧
      omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 5) r.cell) 2 : ℝ) :=
  ((mem_selectedFifthCells e chi m omega (namedJ5 m) r.cell).mp
    (parent0_mem_selected_namedJ5 e hemax chi omega m hstep hw r hr)).2

theorem parent1_original_stop_and_rough
    (e : ℚ) (hemax : e ≤ 3 / 51200) (chi omega : ℝ)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent1 m) :
    historicalPrefixProject (by omega : 3 ≤ 5) r.cell ∈
        HistoricalThirdCoarse.cells (e : ℝ) chi m ∧
      omega ≤ (qLogPrimeMeshLo 0 (19 / 96) m
        (historicalPrefixProject (by omega : 3 ≤ 5) r.cell) 2 : ℝ) :=
  ((mem_selectedFifthCells e chi m omega (namedJ5 m) r.cell).mp
    (parent1_mem_selected_namedJ5 e hemax chi omega m hstep hw r hr)).2

theorem parent0_namedJ5_rawOwnerDomain
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent0 m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    t ∈ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
      selectedParent0 e chi m omega r.cell := by
  exact (selectedParent0_cell_mem_rawOwnerDomain e he hemax chi omega hchi
    m hstep hw (namedJ5 m) r hr (parent0_cell_mem_namedJ5 m r hr) t ht).2

theorem parent1_namedJ5_rawOwnerDomain
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi)
    (hw : omega ≤ 1 / 400) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows selectedParent1 m)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell) :
    t ∈ P1FifthUnitBoxGainDecomposition.rawOwnerDomain
      selectedParent1 e chi m omega r.cell := by
  exact (selectedParent1_cell_mem_rawOwnerDomain e he hemax chi omega hchi
    m hstep hw (namedJ5 m) r hr (parent1_cell_mem_namedJ5 m r hr) t ht).2

end
end ImbalancedChen.P1FifthNamedParentsConcreteJ5
