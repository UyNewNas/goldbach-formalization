import ImbalancedChen.P5HistoricalRectangularGammaTransport
import ImbalancedChen.P5HistoricalHistoryResidualAndSchedule

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The full original positional archive, its actual decoder, and the genuine
currentExponent are used. No archive order or third-gap verdict is assumed.
The first-cube obstruction is paid exactly. The remaining third-history
transport has a uniform 9 chi / 2 error, including selected pair, W rescue,
inactive rough and unselected-owner cases.
-/
namespace ImbalancedChen.P5HistoricalActualThirdHistoryTransport
noncomputable section
open Set
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthAdoptedOwnerBank
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P5CanonicalOwnerFilterStrips P5HistoricalHistoryResidualAndSchedule
open P5HistoricalRectangularGammaTransport

theorem decoded_first_endpoints (i : ArchiveIndex) (q : ℕ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q)) :
    (archiveRow i).lower 0 ≤ (box (refinedMesh q) (thirdOwner r.cell)).lx ∧
      (box (refinedMesh q) (thirdOwner r.cell)).ux ≤ (archiveRow i).upper 0 := by
  obtain ⟨_hg, _hm, j, hj, heq⟩ :=
    (mem_decodeFifthRows_iff (archiveRow i) (refinedMesh q) r).mp hr
  cases heq
  simpa only [box, thirdOwner, historicalPrefixProject, qLogPrimeMeshLo,
    qLogPrimeMeshHi] using hj 0

theorem decoded_thirdBox_below_mu (i : ArchiveIndex) (q : ℕ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q)) :
    ((box (refinedMesh q) (thirdOwner r.cell)).ux : ℝ) ≤ 39 / 200 := by
  have hk : ((archiveRow i).lo 0 : ℝ) ≤ 77 := by
    exact_mod_cast (archiveRow_baseGeometry i).2.2.2
  have hu : ((box (refinedMesh q) (thirdOwner r.cell)).ux : ℝ) ≤
      ((archiveRow i).upper 0 : ℝ) := by
    exact_mod_cast (decoded_first_endpoints i q r hr).2
  simp only [FifthWireRow.upper, archiveRow_grid] at hu
  push_cast at hu
  linarith

/-- A genuine uniform positive margin for the CURRENT third first cube.
The grid400 raw interval is used, so this works even when chi is large,
the third owner is unselected, or rough activation is off. -/
theorem archive_current_first_cube_margin (i : ArchiveIndex) (q : ℕ)
    (chi omega : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    3 * t 0 + 9 / 800 ≤ currentExponent 0 chi (refinedMesh q) omega r.cell t := by
  let b := box (refinedMesh q) (thirdOwner r.cell)
  have hk : ((archiveRow i).lo 0 : ℝ) ≤ 77 := by
    exact_mod_cast (archiveRow_baseGeometry i).2.2.2
  have hraw := (decodeFifthRows_source_geometry
    (archiveRow i) (refinedMesh q) r hr t ht).2.2.2
  have hl : ((archiveRow i).lower 0 : ℝ) ≤ (b.lx : ℝ) := by
    exact_mod_cast (decoded_first_endpoints i q r hr).1
  have hu : (b.ux : ℝ) ≤ ((archiveRow i).upper 0 : ℝ) := by
    exact_mod_cast (decoded_first_endpoints i q r hr).2
  have hp := (hraw 0).2
  simp only [FifthWireRow.lower, FifthWireRow.upper, archiveRow_grid] at hl hu hp
  push_cast at hl hu hp
  have hbase : 3 * t 0 + 9 / 800 ≤ (qVLo b.lx b.ux : ℝ) := by
    rw [cast_qVLo]
    apply le_min <;> dsimp only [A, C] <;> linarith
  have hgamma : (qVLo b.lx b.ux : ℝ) ≤ gamma 0 b := by
    exact_mod_cast baseline_le_gamma 0 b
  have hlevel : 3 * t 0 + 9 / 800 ≤ levelExponent 0 b := by
    simpa only [levelExponent, mul_zero, sub_zero] using hbase.trans hgamma
  have hinitial : 3 * t 0 + 9 / 800 ≤ initial 0 := by
    dsimp only [initial, extendedDistributionCap]
    linarith
  by_cases ha : omega ≤ t 2
  · rw [currentExponent, if_pos ha]
    by_cases hs : thirdOwner r.cell ∈ cells 0 chi (refinedMesh q)
    · simpa only [thirdCellExponent, if_pos hs] using hlevel
    · simpa only [thirdCellExponent, if_neg hs] using hinitial
  · simpa only [currentExponent, if_neg ha] using hinitial

/-- One of I's three unpaid predicates disappears throughout the full
original archive, with no history, order, selected-owner or cap premise. -/
theorem mem_canonicalInvalidHistory_iff_order_or_third
    (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    t ∈ canonicalInvalidHistory (archiveRow i) q chi omega ↔
      ¬ StrictAnti t ∨ currentExponent 0 chi (refinedMesh q) omega r.cell t ≤
        t 0 + t 1 + 3 * t 2 := by
  have hmargin := archive_current_first_cube_margin i q chi omega r hr t ht
  have hfirst : ¬currentExponent 0 chi (refinedMesh q) omega r.cell t ≤ 3 * t 0 := by
    linarith
  rw [mem_canonicalInvalidHistory_iff_actual_failures i q chi omega r hr t ht]
  simp only [hfirst, false_or]

theorem six_le_cap_of_nonnegative_third (x y z : ℝ) (hz : 0 ≤ z) :
    six x y z ≤ cap := by
  have hW : B z ≤ cap := by dsimp only [B]; linarith
  exact max_le (v_le_cap _) (max_le (v_le_cap _)
    (max_le (v_le_cap _) (max_le hW (max_le (v_le_cap _) (v_le_cap _)))))

/-- The exact currentExponent dispatch is bounded below by the original
six-branch endpoint, up to the actual rectangular mesh error. Selected
cells supply their own weak ordering; no all-archive ordering is presumed.
Unselected and rough-inactive cells keep the larger original initial cap. -/
theorem archive_current_third_lower (i : ArchiveIndex) (q : ℕ)
    (chi omega : ℝ) (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256)
    (r : FifthRow (refinedMesh q))
    (hr : r ∈ decodeFifthRows (archiveRow i) (refinedMesh q))
    (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell) :
    six (t 0) (t 1) (t 2) - (9 / 2 : ℝ) * chi ≤
      currentExponent 0 chi (refinedMesh q) omega r.cell t := by
  let b := box (refinedMesh q) (thirdOwner r.cell)
  have hraw := (decodeFifthRows_source_geometry
    (archiveRow i) (refinedMesh q) r hr t ht).2.2.2
  have hk : (1 : ℝ) ≤ ((archiveRow i).lo 2 : ℝ) := by
    exact_mod_cast (archiveRow_baseGeometry i).2.2.1 2
  have hlo := (hraw 2).1
  simp only [FifthWireRow.lower, archiveRow_grid] at hlo
  push_cast at hlo
  have hz : 0 ≤ t 2 := by linarith
  have hcap := six_le_cap_of_nonnegative_third (t 0) (t 1) (t 2) hz
  have hinitial : six (t 0) (t 1) (t 2) - (9 / 2 : ℝ) * chi ≤ initial 0 := by
    dsimp only [initial, extendedDistributionCap, cap] at *
    linarith
  by_cases ha : omega ≤ t 2
  · rw [currentExponent, if_pos ha]
    by_cases hs : thirdOwner r.cell ∈ cells 0 chi (refinedMesh q)
    · rw [thirdCellExponent, if_pos hs]
      have hc := (mem_cells 0 chi (refinedMesh q) (thirdOwner r.cell)).mp hs
      have hbox : b.InBox (t 0) (t 1) (t 2) := by
        have hp := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht
        simpa only [b, thirdOwner, historicalPrefixProject] using inBox_of_cell hp
      have hzy : (b.uz : ℝ) ≤ b.ly := by exact_mod_cast hc.2.2.1
      have hyx : (b.uy : ℝ) ≤ b.lx := by exact_mod_cast hc.2.2.2.1
      have hmu : (b.ux : ℝ) ≤ mu := by
        have hb := decoded_thirdBox_below_mu i q r hr
        change (b.ux : ℝ) ≤ 39 / 200 at hb
        dsimp only [mu]
        linarith
      have ho : Ordered (t 0) (t 1) (t 2) :=
        ⟨hz, by linarith [hbox.2.2.2.2.2, hbox.2.2.1],
          by linarith [hbox.2.2.2.1, hbox.1], hbox.2.1.trans hmu⟩
      have herr := (zero_level_error chi b hchi hc.2.2.2.2.2
        hbox ho hmu hfine).2
      linarith
    · simpa only [thirdCellExponent, if_neg hs] using hinitial
  · simpa only [currentExponent, if_neg ha] using hinitial

end
end ImbalancedChen.P5HistoricalActualThirdHistoryTransport
