import ImbalancedChen.P1FifthRawKeyThirdOwnerPersistence
import ImbalancedChen.P1OriginalFifthUntruncatedIntegral
import ImbalancedChen.P1OriginalHistoricalFifthOwnCubeAffineGates
import ImbalancedChen.P1FifthUnitBoxGainDecomposition

-- Proposed target: ImbalancedChen/P1FifthMask6RawOwnerLicence.lean
-- SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT / HELD / NOT_ROOT_ACCEPTED.
-- Actual non-W thirdgap branch mask6. No archived all-row verdict.
-- Preserves true fullGamma dispatch AND the original e<=yzGap pair gate.

namespace ImbalancedChen.P1FifthMask6RawOwnerLicence
open P1OriginalPrefixRowDecodeSoundness

def ascendingThirdNumerator (raw : FifthWireRow) : ℤ :=
  3200 - 16 * (raw.lo 0 + 1) - 8 * (raw.lo 1 + 1) - 40 * (raw.lo 2 + 1)

def descendingThirdNumerator (raw : FifthWireRow) : ℤ :=
  5700 - 16 * (raw.lo 0 + 1) - 40 * (raw.lo 1 + 1) - 72 * (raw.lo 2 + 1)

def mask6HistoryCheck (raw : FifthWireRow) : Bool :=
  decide (raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
    (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
    0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw))

def ascendingPairNumerator (raw : FifthWireRow) : ℤ :=
  3200 - 32 * (raw.lo 0 + 1) - 8 * (raw.lo 1 + 1) - 8 * (raw.lo 2 + 1)

def descendingPairNumerator (raw : FifthWireRow) : ℤ :=
  5700 - 32 * (raw.lo 0 + 1) - 40 * (raw.lo 1 + 1) - 40 * (raw.lo 2 + 1)

-- Stronger whole-raw guard. Positive thirdgap alone does NOT assert this.
def mask6WholeRawCheck (raw : FifthWireRow) : Bool :=
  mask6HistoryCheck raw &&
    decide (0 < min (ascendingPairNumerator raw) (descendingPairNumerator raw))

def yzCellGapQ (m : ℕ) (j : Fin 5 → Fin (m + 1)) : ℚ :=
  let u := qLogPrimeMeshHi 0 (19 / 96) m j
  VariableEnvelope.qV (u 1 + u 2) - (2 * u 0 + u 1 + u 2)

def yzCellGateCheck (e : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) : Bool :=
  decide (e ≤ yzCellGapQ m j)

noncomputable section
open Set VariableEnvelope HistoricalThirdCoarse
open scoped Classical
open P1OriginalVariableFifthContinuation
open P1FifthRawKeyThirdOwnerPersistence

-- Exact rational ORIGINAL pair gate at a decoded third cell's upper
-- corner. It handles equality inclusively, as does actual fullGamma.
theorem yzCellGateCheck_iff (e : ℚ) (m : ℕ) (j : Label5 m) :
    yzCellGateCheck e m j = true ↔
      (e : ℝ) ≤ yzGap (HistoricalThirdCoarse.box m
        (historicalPrefixProject (by omega : 3 ≤ 5) j)) := by
  have heq : (yzCellGapQ m j : ℝ) =
      yzGap (HistoricalThirdCoarse.box m (historicalPrefixProject (by omega : 3 ≤ 5) j)) := by
    let u := qLogPrimeMeshHi 0 (19 / 96) m j
    change ((qV (u 1 + u 2) - (2 * u 0 + u 1 + u 2) : ℚ) : ℝ) =
      v ((u 1 : ℝ) + (u 2 : ℝ)) - (2 * (u 0 : ℝ) + (u 1 : ℝ) + (u 2 : ℝ))
    simp only [Rat.cast_sub, cast_qV, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  change decide (e ≤ yzCellGapQ m j) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h
    have hc : (e : ℝ) ≤ (yzCellGapQ m j : ℝ) := Rat.cast_le.mpr h
    simpa only [heq] using hc
  · intro h
    have hc : (e : ℝ) ≤ (yzCellGapQ m j : ℝ) := by simpa only [heq] using h
    exact Rat.cast_le.mp hc

-- This cell-local filter is available when the stronger raw pair guard
-- has no verdict. It does not claim the filtered cells cover the raw box.
def licensedDecodedRows (e : ℚ) (raw : FifthWireRow) (m : ℕ) : Finset (FifthRow m) :=
  (decodeFifthRows raw m).filter (fun r => yzCellGateCheck e m r.cell = true)

theorem mem_licensedDecodedRows (e : ℚ) (raw : FifthWireRow) (m : ℕ) (r : FifthRow m) :
    r ∈ licensedDecodedRows e raw m ↔ r ∈ decodeFifthRows raw m ∧
      (e : ℝ) ≤ yzGap (HistoricalThirdCoarse.box m
        (historicalPrefixProject (by omega : 3 ≤ 5) r.cell)) := by
  simp only [licensedDecodedRows, Finset.mem_filter, yzCellGateCheck_iff]

-- The exact coefficient-sign minima used by Jensen's mask6 thirdgap:
-- A(y+z)-H and C(y+z)-H attain their minima at the raw upper corner.
theorem mask6_plane_gaps_exact (raw : FifthWireRow) (hg : raw.grid = 400) :
    qA (raw.upper 1 + raw.upper 2) - (raw.upper 0 + raw.upper 1 + 3 * raw.upper 2) =
        (ascendingThirdNumerator raw : ℚ) / 6400 ∧
    qC (raw.upper 1 + raw.upper 2) - (raw.upper 0 + raw.upper 1 + 3 * raw.upper 2) =
        (descendingThirdNumerator raw : ℚ) / 6400 := by
  constructor
  · simp only [ascendingThirdNumerator, FifthWireRow.upper, hg]
    push_cast
    unfold qA
    ring
  · simp only [descendingThirdNumerator, FifthWireRow.upper, hg]
    push_cast
    unfold qC
    ring

theorem mask6_raw_gaps_lower (raw : FifthWireRow) (hg : raw.grid = 400)
    (hgap : 0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw)) :
    (1 / 6400 : ℚ) ≤ qA (raw.upper 1 + raw.upper 2) -
        (raw.upper 0 + raw.upper 1 + 3 * raw.upper 2) ∧
      (1 / 6400 : ℚ) ≤ qC (raw.upper 1 + raw.upper 2) -
        (raw.upper 0 + raw.upper 1 + 3 * raw.upper 2) := by
  have ha : 1 ≤ ascendingThirdNumerator raw := by have h := (lt_min_iff.mp hgap).1; omega
  have hc : 1 ≤ descendingThirdNumerator raw := by have h := (lt_min_iff.mp hgap).2; omega
  have haQ : (1 : ℚ) ≤ (ascendingThirdNumerator raw : ℚ) := by exact_mod_cast ha
  have hcQ : (1 : ℚ) ≤ (descendingThirdNumerator raw : ℚ) := by exact_mod_cast hc
  rw [(mask6_plane_gaps_exact raw hg).1, (mask6_plane_gaps_exact raw hg).2]
  constructor <;> linarith

-- YZ is a GATED entry of the real fullGamma; preserve its literal gate.
theorem pair_plane_gaps_exact (raw : FifthWireRow) (hg : raw.grid = 400) :
    qA (raw.upper 1 + raw.upper 2) - (2 * raw.upper 0 + raw.upper 1 + raw.upper 2) =
        (ascendingPairNumerator raw : ℚ) / 6400 ∧
    qC (raw.upper 1 + raw.upper 2) - (2 * raw.upper 0 + raw.upper 1 + raw.upper 2) =
        (descendingPairNumerator raw : ℚ) / 6400 := by
  constructor
  · simp only [ascendingPairNumerator, FifthWireRow.upper, hg]
    push_cast
    unfold qA
    ring
  · simp only [descendingPairNumerator, FifthWireRow.upper, hg]
    push_cast
    unfold qC
    ring

theorem raw_pair_gap_implies_gate (raw : FifthWireRow) (hg : raw.grid = 400)
    (hp : 0 < min (ascendingPairNumerator raw) (descendingPairNumerator raw))
    (e : ℚ) (hemax : e ≤ 3 / 51200) (b : RationalBox)
    (hx : b.ux ≤ raw.upper 0) (hy : b.uy ≤ raw.upper 1) (hz : b.uz ≤ raw.upper 2) :
    (e : ℝ) ≤ yzGap b := by
  have haZ : 1 ≤ ascendingPairNumerator raw := by have h := (lt_min_iff.mp hp).1; omega
  have hcZ : 1 ≤ descendingPairNumerator raw := by have h := (lt_min_iff.mp hp).2; omega
  have haQ : (1 : ℚ) ≤ (ascendingPairNumerator raw : ℚ) := by exact_mod_cast haZ
  have hcQ : (1 : ℚ) ≤ (descendingPairNumerator raw : ℚ) := by exact_mod_cast hcZ
  have haRawQ : (1 / 6400 : ℚ) ≤ qA (raw.upper 1 + raw.upper 2) -
      (2 * raw.upper 0 + raw.upper 1 + raw.upper 2) := by
    rw [(pair_plane_gaps_exact raw hg).1]
    linarith
  have hcRawQ : (1 / 6400 : ℚ) ≤ qC (raw.upper 1 + raw.upper 2) -
      (2 * raw.upper 0 + raw.upper 1 + raw.upper 2) := by
    rw [(pair_plane_gaps_exact raw hg).2]
    linarith
  have haRaw : (1 / 6400 : ℝ) ≤ (qA (raw.upper 1 + raw.upper 2) : ℝ) -
      (2 * (raw.upper 0 : ℝ) + (raw.upper 1 : ℝ) + (raw.upper 2 : ℝ)) := by exact_mod_cast haRawQ
  have hcRaw : (1 / 6400 : ℝ) ≤ (qC (raw.upper 1 + raw.upper 2) : ℝ) -
      (2 * (raw.upper 0 : ℝ) + (raw.upper 1 : ℝ) + (raw.upper 2 : ℝ)) := by exact_mod_cast hcRawQ
  rw [cast_qA] at haRaw
  rw [cast_qC] at hcRaw
  push_cast at haRaw hcRaw
  have hxR : (b.ux : ℝ) ≤ (raw.upper 0 : ℝ) := Rat.cast_le.mpr hx
  have hyR : (b.uy : ℝ) ≤ (raw.upper 1 : ℝ) := Rat.cast_le.mpr hy
  have hzR : (b.uz : ℝ) ≤ (raw.upper 2 : ℝ) := Rat.cast_le.mpr hz
  have ha : 2 * (b.ux : ℝ) + (b.uy : ℝ) + (b.uz : ℝ) + 1 / 6400 ≤
      A ((b.uy : ℝ) + (b.uz : ℝ)) := by dsimp [A] at haRaw ⊢; linarith
  have hc : 2 * (b.ux : ℝ) + (b.uy : ℝ) + (b.uz : ℝ) + 1 / 6400 ≤
      C ((b.uy : ℝ) + (b.uz : ℝ)) := by dsimp [C] at hcRaw ⊢; linarith
  have hgap : (1 / 6400 : ℝ) ≤ yzGap b := by
    rw [yzGap, v_eq_min]
    have hmin := le_min ha hc
    linarith
  have heR : (e : ℝ) ≤ 3 / 51200 := Rat.cast_le.mpr hemax
  linarith

theorem decoded_yz_gate_of_wholeCheck (raw : FifthWireRow) (hc : mask6WholeRawCheck raw = true)
    (e : ℚ) (hemax : e ≤ 3 / 51200) (m : ℕ) (r : FifthRow m)
    (hr : r ∈ decodeFifthRows raw m) : yzCellGateCheck e m r.cell = true := by
  have hcore := (Bool.and_eq_true.mp hc).1
  have hp : 0 < min (ascendingPairNumerator raw) (descendingPairNumerator raw) :=
    of_decide_eq_true (Bool.and_eq_true.mp hc).2
  have hs : raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
      (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
      0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw) := of_decide_eq_true hcore
  have hcontained : fifthCellContained raw m r.cell := by
    obtain ⟨_hg, _hm, j, hj, heq⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
    cases heq
    exact hj
  apply (yzCellGateCheck_iff e m r.cell).mpr
  exact raw_pair_gap_implies_gate raw hs.1 hp e hemax
    (HistoricalThirdCoarse.box m (historicalPrefixProject (by omega : 3 ≤ 5) r.cell))
    (hcontained 0).2 (hcontained 1).2 (hcontained 2).2

theorem yz_le_fullGamma (e : ℝ) (b : RationalBox) (hgate : e ≤ yzGap b) :
    qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ fullGamma e b := by
  dsimp only [fullGamma]
  rw [if_pos hgate]
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_of_le_right le_rfl))))

-- Literal sum endpoints lose at most3chi. Unlike mask1, YZ needs the
-- true fullGamma dispatch, paid by lo0<=77 and the positive schedule.
theorem actual_mask6_third_cube_reserve (raw : FifthWireRow) (hg : raw.grid = 400)
    (htop : raw.lo 0 ≤ 77)
    (hgap : 0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw))
    (e : ℚ) (hemax : e ≤ 3 / 51200) (chi : ℝ) (hchi : chi < (e : ℝ) / 10)
    (b : RationalBox) (hux : b.ux ≤ raw.upper 0)
    (hgate : (e : ℝ) ≤ yzGap b)
    (hwidthy : (b.uy : ℝ) - (b.ly : ℝ) ≤ chi)
    (hwidthz : (b.uz : ℝ) - (b.lz : ℝ) ≤ chi)
    (t : Fin 5 → ℝ) (hbox : b.InBox (t 0) (t 1) (t 2)) (ht : t ∈ raw.originalBox) :
    t 0 + t 1 + 3 * t 2 + 1 / 51200 ≤ levelExponent (e : ℝ) b := by
  have hraw := mask6_raw_gaps_lower raw hg hgap
  have haR : (1 / 6400 : ℝ) ≤ (qA (raw.upper 1 + raw.upper 2) : ℝ) -
      ((raw.upper 0 : ℝ) + (raw.upper 1 : ℝ) + 3 * (raw.upper 2 : ℝ)) := by exact_mod_cast hraw.1
  have hcR : (1 / 6400 : ℝ) ≤ (qC (raw.upper 1 + raw.upper 2) : ℝ) -
      ((raw.upper 0 : ℝ) + (raw.upper 1 : ℝ) + 3 * (raw.upper 2 : ℝ)) := by exact_mod_cast hraw.2
  rw [cast_qA] at haR
  rw [cast_qC] at hcR
  push_cast at haR hcR
  have h0 := (ht 0).2.le
  have h1 := (ht 1).2.le
  have h2 := (ht 2).2.le
  have hly := hbox.2.2.1
  have huyT := hbox.2.2.2.1
  have hlz := hbox.2.2.2.2.1
  have huzT := hbox.2.2.2.2.2
  have hchi0 : 0 ≤ chi := by linarith
  have ha : t 0 + t 1 + 3 * t 2 + 1 / 6400 - 3 * chi ≤ A ((b.ly : ℝ) + (b.lz : ℝ)) := by
    dsimp [A] at haR ⊢
    linarith
  have hc : t 0 + t 1 + 3 * t 2 + 1 / 6400 - 3 * chi ≤ C ((b.uy : ℝ) + (b.uz : ℝ)) := by
    dsimp [C] at hcR ⊢
    linarith
  have hv : t 0 + t 1 + 3 * t 2 + 1 / 6400 - 3 * chi ≤
      (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) := by
    simpa only [qVLo, Rat.cast_min, cast_qA, cast_qC, Rat.cast_add] using le_min ha hc
  have htopQ : raw.upper 0 ≤ (39 / 200 : ℚ) := by
    have hq : (raw.lo 0 : ℚ) ≤ 77 := by exact_mod_cast htop
    simp only [FifthWireRow.upper, hg]
    push_cast
    linarith
  have hfull : (b.ux : ℝ) ≤ mu - 4 * (e : ℝ) := by
    have htopR : (b.ux : ℝ) ≤ 39 / 200 := by exact_mod_cast hux.trans htopQ
    have heR : (e : ℝ) ≤ 3 / 51200 := by exact_mod_cast hemax
    norm_num [mu] at *
    linarith
  have hyz : (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤ (gamma (e : ℝ) b : ℝ) := by
    have hq : qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ gamma (e : ℝ) b := by
      rw [gamma, if_pos hfull]
      exact yz_le_fullGamma (e : ℝ) b hgate
    exact_mod_cast hq
  have heR : (e : ℝ) ≤ 3 / 51200 := by exact_mod_cast hemax
  dsimp only [levelExponent]
  linarith

theorem mask6HistoryCheck_thirdOwnerKeyCheck (raw : FifthWireRow)
    (hc : mask6HistoryCheck raw = true) : thirdOwnerKeyCheck raw = true := by
  have hs : raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
      (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
      0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw) := of_decide_eq_true hc
  change decide (raw.grid = 400 ∧ 0 ≤ raw.mask ∧ 1 ≤ raw.lo 2 ∧
    raw.lo 2 + 1 ≤ raw.lo 1 ∧ raw.lo 1 + 1 ≤ raw.lo 0 ∧ raw.lo 0 ≤ 78) = true
  apply (decide_eq_true_eq).mpr
  exact ⟨hs.1, hs.2.1, hs.2.2.1 2, hs.2.2.2.1 1, hs.2.2.2.1 0,
    by linarith [hs.2.2.2.2.1]⟩

theorem mask6HistoryCheck_rawBox_subset_ambient (raw : FifthWireRow)
    (hc : mask6HistoryCheck raw = true) :
    raw.originalBox ⊆ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
  have hs : raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
      (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
      0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw) := of_decide_eq_true hc
  have htop : ∀ i, raw.lo i ≤ 77 := by
    have h0 := hs.2.2.2.1 0
    have h1 := hs.2.2.2.1 1
    have h2 := hs.2.2.2.1 2
    have h3 := hs.2.2.2.1 3
    intro i
    fin_cases i <;> omega
  intro t ht
  apply mem_logPrimeBox.mpr
  intro i
  have hloR : (1 : ℝ) ≤ (raw.lo i : ℝ) := by exact_mod_cast hs.2.2.1 i
  have hhiR : (raw.lo i : ℝ) ≤ 77 := by exact_mod_cast htop i
  have hli := (ht i).1
  have hui := (ht i).2
  simp only [FifthWireRow.lower, FifthWireRow.upper, hs.1] at hli hui
  push_cast at hli hui
  constructor <;> linarith

theorem decoded_mask6_fullCell (raw : FifthWireRow) (hc : mask6HistoryCheck raw = true)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (m : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96) m ≤ chi) (hw : omega ≤ 1 / 400)
    (J5 : Finset (Label5 m)) (r : FifthRow m) (hr : r ∈ decodeFifthRows raw m)
    (hJ : r.cell ∈ J5) (t : Fin 5 → ℝ)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m r.cell)
    (hgatecheck : yzCellGateCheck e m r.cell = true) :
    r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5 ∧
      t ∈ P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega r.cell := by
  have hs : raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
      (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
      0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw) := of_decide_eq_true hc
  have hselected := decoded_third_owner_selected raw
    (mask6HistoryCheck_thirdOwnerKeyCheck raw hc) e hemax chi omega m hstep hw J5 r hr hJ
  have hcontained : fifthCellContained raw m r.cell := by
    obtain ⟨_hg, _hm, j, hj, heq⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
    cases heq
    exact hj
  have hraw := (decodeFifthRows_source_geometry raw m r hr t ht).2.2.2
  have hp : ∀ i, 0 < t i := by
    intro i
    have hz : (1 : ℚ) ≤ (raw.lo i : ℚ) := by exact_mod_cast hs.2.2.1 i
    have hlo : (1 / 400 : ℝ) ≤ (raw.lower i : ℝ) := by
      simp only [FifthWireRow.lower, hs.1]
      push_cast
      exact_mod_cast (div_le_div_of_nonneg_right hz (by norm_num : (0 : ℚ) ≤ 400))
    linarith [(hraw i).1]
  have horder : StrictAnti t := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    have hz : (raw.lo i.succ : ℚ) + 1 ≤ raw.lo i.castSucc := by exact_mod_cast hs.2.2.2.1 i
    have hgap : raw.upper i.succ ≤ raw.lower i.castSucc := by
      simp only [FifthWireRow.upper, FifthWireRow.lower, hs.1]
      push_cast
      linarith
    have hgapR : (raw.upper i.succ : ℝ) ≤ (raw.lower i.castSucc : ℝ) := by exact_mod_cast hgap
    exact (hraw i.succ).2.trans_le (hgapR.trans (hraw i.castSucc).1)
  let j3 := historicalPrefixProject (by omega : 3 ≤ 5) r.cell
  let b := HistoricalThirdCoarse.box m j3
  have hc3 := ((P1OriginalCoarseFifthContinuation.mem_selectedFifthCells
    e chi m omega J5 r.cell).mp hselected).2.1
  have hcell := (mem_cells (e : ℝ) chi m j3).mp hc3
  have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 5) ht
  have hbox : b.InBox (t 0) (t 1) (t 2) := inBox_of_cell ht3
  have heR : (0 : ℝ) < (e : ℝ) := Rat.cast_pos.mpr he
  have hesmall : (e : ℝ) < (3 / 256 : ℝ) / 100 := by
    have hmaxR : (e : ℝ) ≤ 3 / 51200 := Rat.cast_le.mpr hemax
    linarith
  have hfirst : 3 * t 0 < levelExponent (e : ℝ) b :=
    first_cube_margin (e : ℝ) chi b heR hesmall hchi hcell.2.2.2.2.2 hbox hcell.2.2.2.2.1
  have hroot : 3 * t 0 < initial (e : ℝ) :=
    hfirst.trans (levelExponent_lt_initial (e : ℝ) b heR.le hcell.1 hcell.2.1)
  have hwidthy : (b.uy : ℝ) - (b.ly : ℝ) ≤ chi := by
    have hside : (b.uy : ℝ) - (b.ly : ℝ) ≤ (b.width : ℝ) := by
      exact_mod_cast b.coordinate_widths_le.2.1
    exact hside.trans hcell.2.2.2.2.2
  have hwidthz : (b.uz : ℝ) - (b.lz : ℝ) ≤ chi := by
    have hside : (b.uz : ℝ) - (b.lz : ℝ) ≤ (b.width : ℝ) := by exact_mod_cast b.coordinate_widths_le.2.2
    exact hside.trans hcell.2.2.2.2.2
  have hthird : t 0 + t 1 + 3 * t 2 < levelExponent (e : ℝ) b := by
    have hreserve := actual_mask6_third_cube_reserve raw hs.1 hs.2.2.2.2.1 hs.2.2.2.2.2
      e hemax chi hchi b (hcontained 0).2 ((yzCellGateCheck_iff e m r.cell).mp hgatecheck)
        hwidthy hwidthz t hbox hraw
    linarith
  have hstop : t ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.firstLabelRegion (e : ℝ) m := by
    apply (P1OriginalHistoricalFifthOwnCubeAffineGates.firstLabelRegion_on_cell
      (e : ℝ) m r.cell t ht).mpr
    rw [← congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m r.cell) 0]
    exact hcell.2.2.2.2.1
  have hcurrent := P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
    e chi m omega J5 r.cell hselected t ht
  have hjoint : t ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.jointRegion
      (e : ℝ) chi m omega r.cell := by
    apply (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_jointRegion
      (e : ℝ) chi m omega r.cell t).mpr
    refine ⟨hstop, horder, hroot, ?_, ?_⟩
    · rw [hcurrent]; exact hfirst
    · rw [hcurrent]; exact hthird
  exact ⟨hselected, hp, mask6HistoryCheck_rawBox_subset_ambient raw hc hraw, ht, hjoint⟩

theorem whole_raw_mask6_owner_cover (raw : FifthWireRow) (hc : mask6WholeRawCheck raw = true)
    (e : ℚ) (he : 0 < e) (hemax : e ≤ 3 / 51200)
    (chi omega : ℝ) (hchi : chi < (e : ℝ) / 10)
    (q : ℕ) (hq : 0 < q)
    (hstep : logPrimeMeshStep 0 (19 / 96)
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) ≤ chi) (hw : omega ≤ 1 / 400) :
    raw.originalBox = ⋃ r ∈ decodeFifthRows raw
      (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q),
        P1FifthUnitBoxGainDecomposition.rawOwnerDomain raw e chi
          (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) omega r.cell := by
  have hcore := (Bool.and_eq_true.mp hc).1
  have hs : raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ i, 1 ≤ raw.lo i) ∧
      (∀ i : Fin 4, raw.lo i.succ + 1 ≤ raw.lo i.castSucc) ∧ raw.lo 0 ≤ 77 ∧
      0 < min (ascendingThirdNumerator raw) (descendingThirdNumerator raw) := of_decide_eq_true hcore
  let m := P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
  let J : Finset (Label5 m) := (decodeFifthRows raw m).image FifthRow.cell
  have hcover := P1OriginalFifthGrid400RefinedFullBoxCover.refined_originalBox_inter_ambient_eq_decode_union
    q hq raw hs.1 hs.2.1
  ext t
  constructor
  · intro ht
    have hmesh : t ∈ raw.originalBox ∩ logPrimeBox
        (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) :=
      ⟨ht, mask6HistoryCheck_rawBox_subset_ambient raw hcore ht⟩
    rw [hcover] at hmesh
    obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp hmesh
    have hJ : r.cell ∈ J := Finset.mem_image.mpr ⟨r, hr, rfl⟩
    have hfull := (decoded_mask6_fullCell raw hcore e he hemax chi omega hchi m hstep hw J r hr hJ t htr
      (decoded_yz_gate_of_wholeCheck raw hc e hemax m r hr)).2
    exact mem_iUnion₂.mpr ⟨r, hr, ht, hfull⟩
  · intro ht
    obtain ⟨r, _hr, hraw, _hfull⟩ := mem_iUnion₂.mp ht
    exact hraw

end
end ImbalancedChen.P1FifthMask6RawOwnerLicence
