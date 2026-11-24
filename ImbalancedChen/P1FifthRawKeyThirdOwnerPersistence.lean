import ImbalancedChen.P1OriginalFifthPositiveBufferSchedule
import ImbalancedChen.P1OriginalFifthRawBoxSelectorEquivalence

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / HELD DEPENDENCIES.
-- Finite INTEGER endpoint checks imply actual projected third-owner
-- selection for every contained decoded cell of the positive schedule.
-- The archived full-table verdict is unexecuted. This does not assert
-- fullCell membership or any Gamma/third-history integral bound.
namespace ImbalancedChen.P1FifthRawKeyThirdOwnerPersistence

open P1OriginalPrefixRowDecodeSoundness

-- These are primitive archived fields, not an assumed gate margin or
-- an assumed selectedFifthCells result. The mask statistics are unused.
def thirdOwnerKeyCheck (raw : FifthWireRow) : Bool :=
  decide (raw.grid = 400 ∧ 0 ≤ raw.mask ∧ 1 ≤ raw.lo 2 ∧
    raw.lo 2 + 1 ≤ raw.lo 1 ∧ raw.lo 1 + 1 ≤ raw.lo 0 ∧ raw.lo 0 ≤ 78)

noncomputable section
open scoped Classical
open VariableEnvelope HistoricalThirdCoarse
open P1OriginalVariableFifthContinuation
open P1OriginalFifthQuantitativeGateRefinement
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1OriginalFifthPositiveBufferSchedule

theorem thirdOwnerKeyCheck_sound (raw : FifthWireRow)
    (hc : thirdOwnerKeyCheck raw = true) :
    raw.grid = 400 ∧ 0 ≤ raw.mask ∧ 1 ≤ raw.lo 2 ∧
      raw.lo 2 + 1 ≤ raw.lo 1 ∧ raw.lo 1 + 1 ≤ raw.lo 0 ∧ raw.lo 0 ≤ 78 :=
  of_decide_eq_true hc

-- rho minus the largest permitted saved unit upper endpoint is exactly
-- 1/2400. The universal positive-e schedule spends less than this reserve.
theorem endpoint_stop_reserve : (19 / 96 : ℚ) - 79 / 400 = 1 / 2400 := by norm_num

theorem positive_stop_surplus (e : ℚ) (he : e ≤ 3 / 51200) :
    (79 / 400 : ℚ) + 7 / 38400 ≤ 19 / 96 - 4 * e := by linarith

theorem decoded_third_owner_selected
    (raw : FifthWireRow) (hc : thirdOwnerKeyCheck raw = true)
    (e : ℚ) (he : e ≤ 3 / 51200) (chi omega : ℝ) (m : ℕ)
    (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi) (hw : omega ≤ 1 / 400)
    (J5 : Finset (Label5 m)) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows raw m) (hJ : r.cell ∈ J5) :
    r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5 := by
  have hk := thirdOwnerKeyCheck_sound raw hc
  obtain ⟨_hg, _hmask, j, hcontained, hrj⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
  subst r
  have h01 : raw.upper 1 ≤ raw.lower 0 := by
    have hi : (raw.lo 1 : ℚ) + 1 ≤ raw.lo 0 := by exact_mod_cast hk.2.2.2.2.1
    simp only [FifthWireRow.upper, FifthWireRow.lower, hk.1]
    push_cast
    linarith
  have h12 : raw.upper 2 ≤ raw.lower 1 := by
    have hi : (raw.lo 2 : ℚ) + 1 ≤ raw.lo 1 := by exact_mod_cast hk.2.2.2.1
    simp only [FifthWireRow.upper, FifthWireRow.lower, hk.1]
    push_cast
    linarith
  have hlow : (1 / 400 : ℚ) ≤ raw.lower 2 := by
    have hi : (1 : ℚ) ≤ raw.lo 2 := by exact_mod_cast hk.2.2.1
    simp only [FifthWireRow.lower, hk.1]
    push_cast
    linarith
  have hhigh : raw.upper 0 ≤ (79 / 400 : ℚ) := by
    have hi : (raw.lo 0 : ℚ) ≤ 78 := by exact_mod_cast hk.2.2.2.2.2
    simp only [FifthWireRow.upper, hk.1]
    push_cast
    linarith
  let l := qLogPrimeMeshLo 0 (19 / 96) m j
  let u := qLogPrimeMeshHi 0 (19 / 96) m j
  have hlu (i : Fin 5) : l i ≤ u i := by
    change qLogPrimeMeshLo 0 (19 / 96) m j i ≤ qLogPrimeMeshHi 0 (19 / 96) m j i
    rw [mesh_upper_eq_lower_add_step]
    linarith [meshStepQ_pos m]
  have hthird : historicalPrefixProject (by omega : 3 ≤ 5) j ∈ cells (e : ℝ) chi m := by
    apply (mem_cells (e : ℝ) chi m _).mpr
    have hwidth : (box m (historicalPrefixProject (by omega : 3 ≤ 5) j)).width = meshStepQ m := by
      change max 0 (max (u 0 - l 0) (max (u 1 - l 1) (u 2 - l 2))) = meshStepQ m
      have hs (i : Fin 5) : u i - l i = meshStepQ m := by
        dsimp only [u, l]
        rw [mesh_upper_eq_lower_add_step]
        ring
      rw [hs 0, hs 1, hs 2]
      simp only [max_self, max_eq_right (meshStepQ_pos m).le]
    refine ⟨⟨hlu 0, hlu 1, hlu 2⟩, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ l 2
      exact (by norm_num : (0 : ℚ) ≤ 1 / 400).trans (hlow.trans (hcontained 2).1)
    · change u 2 ≤ l 1
      exact (hcontained 2).2.trans (h12.trans (hcontained 1).1)
    · change u 1 ≤ l 0
      exact (hcontained 1).2.trans (h01.trans (hcontained 0).1)
    · change (u 0 : ℝ) ≤ extendedFirstStop - 4 * (e : ℝ)
      have hu : (u 0 : ℝ) ≤ 79 / 400 := by
        exact_mod_cast (hcontained 0).2.trans hhigh
      have heR : (e : ℝ) ≤ 3 / 51200 := by exact_mod_cast he
      norm_num [extendedFirstStop] at *
      linarith
    · rw [hwidth, cast_meshStepQ]
      exact hstep
  apply (P1OriginalCoarseFifthContinuation.mem_selectedFifthCells e chi m omega J5 j).mpr
  refine ⟨hJ, hthird, ?_⟩
  change omega ≤ (l 2 : ℝ)
  have hl : (1 / 400 : ℝ) ≤ (l 2 : ℝ) := by
    exact_mod_cast hlow.trans (hcontained 2).1
  exact hw.trans hl

-- The entire decoded-owner image is preserved by the ACTUAL selected
-- original-third filter. No ancestor membership is supplied as a premise.
theorem scheduled_selected_owner_image_eq
    (records : Finset FifthWireRow) (delta : ℚ) (hd : 0 < delta)
    (hzero : ∀ raw ∈ records, correlatedRawBoxGateCheck 0 raw = true)
    (hkeys : ∀ raw ∈ records, thirdOwnerKeyCheck raw = true) :
    let q := scheduleQ records delta
    let J5 := (decodedFamily records q).image FifthRow.cell
    P1OriginalCoarseFifthContinuation.selectedFifthCells (bufferQ records delta)
      (P1OriginalFifthPositiveBufferSchedule.chi records delta) (refinedMesh q)
      (P1OriginalFifthPositiveBufferSchedule.omega records delta) J5 = J5 := by
  have hp := positive_parameters records delta hd hzero
  have hgates := scheduled_all_decoded_gates records delta hd hzero
  have he : bufferQ records delta ≤ (3 / 51200 : ℚ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have heR : (bufferQ records delta : ℝ) ≤ 3 / 51200 := by exact_mod_cast he
  have hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh (scheduleQ records delta)) ≤
      P1OriginalFifthPositiveBufferSchedule.chi records delta := by
    linarith [hgates.1, hp.2.2.1]
  have hw : P1OriginalFifthPositiveBufferSchedule.omega records delta ≤ 1 / 400 := by
    have hm : P1OriginalFifthPositiveBufferSchedule.omega records delta ≤
        P1OriginalFifthPositiveBufferSchedule.chi records delta / 1000 := min_le_left _ _
    dsimp only [P1OriginalFifthPositiveBufferSchedule.chi] at hm
    linarith
  dsimp only
  apply Finset.Subset.antisymm
  · exact Finset.filter_subset _ _
  · intro j hj
    obtain ⟨r, hr, hrj⟩ := Finset.mem_image.mp hj
    obtain ⟨raw, hraw, hdecode⟩ := (mem_decodedFamily records (scheduleQ records delta) r).mp hr
    subst j
    exact decoded_third_owner_selected raw (hkeys raw hraw) (bufferQ records delta) he
      (P1OriginalFifthPositiveBufferSchedule.chi records delta)
      (P1OriginalFifthPositiveBufferSchedule.omega records delta)
      (refinedMesh (scheduleQ records delta)) hstep hw _ r hdecode
      (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

end
end ImbalancedChen.P1FifthRawKeyThirdOwnerPersistence
