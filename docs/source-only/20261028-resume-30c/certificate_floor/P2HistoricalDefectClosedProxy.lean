import ImbalancedChen.P2HistoricalOrdinaryProxySourceUpper

/-!
SOURCE ONLY, uncompiled.  Exact closed-cell minimum for the actual copied
200-entry h248 Q80 bank, compared with the historical outward I80 query.
The source-only import has the exact installation/hash mapping in REGISTRY.
No table endpoint licence is needed for the finite minimum comparison.
-/

namespace ImbalancedChen.P2HistoricalDefectClosedProxy

noncomputable section

open Set
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2HistoricalSavedFloorRowsBinder P2HistoricalSavedFloorFullBinder
open P2HistoricSavedOrdinaryDefectAssembly P2HistoricQ80OrdinaryEstimatorSoundness
open P2HistoricalOrdinaryProxyIntegral P2HistoricalOrdinaryProxySourceUpper
open P2SavedFloorSemantics

def cellLeft (k : ℤ) : ℚ := 1 + (k : ℚ) / 50
def cellRight (k : ℤ) : ℚ := 1 + ((k : ℚ) + 1) / 50
def exactStart (sl : ℚ) : ℤ := max 0 (⌈(sl - 1) * 50⌉ - 1)
def exactStop (sh : ℚ) : ℤ := min 199 ⌊(sh - 1) * 50⌋

/-- The `ceil - 1` is retained at an exact lower-endpoint knot. -/
theorem exact_indices_iff (sl sh : ℚ) (k : ℤ) :
    exactStart sl ≤ k ∧ k ≤ exactStop sh ↔
      0 ≤ k ∧ k ≤ 199 ∧ sl ≤ cellRight k ∧ cellLeft k ≤ sh := by
  have hc : ⌈(sl - 1) * 50⌉ - 1 ≤ k ↔ (sl - 1) * 50 ≤ (k : ℚ) + 1 := by
    rw [sub_le_iff_le_add, Int.ceil_le]
    norm_cast
  rw [exactStart, exactStop, max_le_iff, le_min_iff, hc, Int.le_floor]
  dsimp [cellLeft, cellRight]
  constructor
  · rintro ⟨⟨hk0, hl⟩, hk199, hh⟩
    exact ⟨hk0, hk199, by linarith, by linarith⟩
  · rintro ⟨hk0, hk199, hl, hh⟩
    exact ⟨⟨hk0, by linarith⟩, hk199, by linarith⟩

/-- Actual meeting of two closed intervals, not a one-sided ownership rule. -/
theorem exact_indices_iff_closed_meeting {sl sh : ℚ} (horder : sl ≤ sh) (k : ℤ) :
    exactStart sl ≤ k ∧ k ≤ exactStop sh ↔
      0 ≤ k ∧ k ≤ 199 ∧
        ∃ s : ℚ, s ∈ Icc sl sh ∧ s ∈ Icc (cellLeft k) (cellRight k) := by
  rw [exact_indices_iff]
  constructor
  · rintro ⟨hk0, hk199, hl, hh⟩
    refine ⟨hk0, hk199, max sl (cellLeft k), ?_, ?_⟩
    · exact ⟨le_max_left _ _, max_le horder hh⟩
    · exact ⟨le_max_right _ _, max_le hl (by dsimp [cellLeft, cellRight]; linarith)⟩
  · rintro ⟨hk0, hk199, s, hs, hc⟩
    exact ⟨hk0, hk199, hs.1.trans hc.2, hc.1.trans hs.2⟩

theorem exact_slice_nonempty {sl sh : ℚ}
    (hsl : 1 ≤ sl) (horder : sl ≤ sh) (hsh : sh ≤ 5) : exactStart sl ≤ exactStop sh := by
  have hscaled : (sl - 1) * 50 ≤ (sh - 1) * 50 := by linarith
  have hceil : ⌈(sl - 1) * 50⌉ ≤ (200 : ℤ) :=
    Int.ceil_le.mpr (by norm_num; linarith)
  have hfloor : (0 : ℤ) ≤ ⌊(sh - 1) * 50⌋ :=
    Int.le_floor.mpr (by norm_num; linarith)
  have hcf := Int.ceil_le_floor_add_one ((sl - 1) * 50)
  have hmono := Int.floor_mono hscaled
  unfold exactStart exactStop
  rw [max_le_iff, le_min_iff, le_min_iff]
  omega

theorem exact_knot_both_cells (k : ℤ) (hk : 1 ≤ k) (hk199 : k ≤ 199) :
    (exactStart (cellLeft k) ≤ k - 1 ∧ k - 1 ≤ exactStop (cellLeft k)) ∧
      (exactStart (cellLeft k) ≤ k ∧ k ≤ exactStop (cellLeft k)) := by
  constructor
  · apply (exact_indices_iff _ _ _).mpr
    refine ⟨by omega, by omega, ?_, ?_⟩
    all_goals dsimp [cellLeft, cellRight] <;> push_cast <;> linarith
  · apply (exact_indices_iff _ _ _).mpr
    refine ⟨by omega, hk199, ?_, le_rfl⟩
    dsimp [cellLeft, cellRight]
    linarith

private theorem scaledLo_decode (x : I80) : scaledLo 50 x = (x.decodeLo - 1) * 50 := by
  unfold scaledLo I80.decodeLo
  field_simp [Q_ne_zero] <;> ring

private theorem scaledHi_decode (x : I80) : scaledHi 50 x = (x.decodeHi - 1) * 50 := by
  unfold scaledHi I80.decodeHi
  field_simp [Q_ne_zero] <;> ring

/-- Every exact closed cell is also selected by any outward interval.
This includes each of the two endpoint cells at a knot. -/
theorem exact_slice_subset_outward {sl sh : ℚ} (x : I80)
    (hl : x.decodeLo ≤ sl) (hh : sh ≤ x.decodeHi) (k : ℤ)
    (hk : exactStart sl ≤ k ∧ k ≤ exactStop sh) :
    lookupStart 50 x ≤ k ∧ k ≤ lookupStop 50 x := by
  rcases (exact_indices_iff sl sh k).mp hk with ⟨hk0, hk199, hsl, hsh⟩
  apply (lookup_indices_iff 50 x k).mpr
  refine ⟨hk0, by norm_num; exact hk199, ?_, ?_⟩
  · rw [scaledLo_decode]
    dsimp [cellRight] at hsl
    linarith
  · rw [scaledHi_decode]
    dsimp [cellLeft] at hsh
    linarith

theorem outward_min_le_exact_min {sl sh : ℚ} (table : ℤ → ℤ) (x : I80)
    (hne : exactStart sl ≤ exactStop sh)
    (hl : x.decodeLo ≤ sl) (hh : sh ≤ x.decodeHi) :
    closedSliceMin table (lookupStart 50 x) (lookupStop 50 x) ≤
      closedSliceMin table (exactStart sl) (exactStop sh) := by
  apply le_closedSliceMin _ _ _ _ hne
  intro k hklo hkhi
  have hk := exact_slice_subset_outward x hl hh k ⟨hklo, hkhi⟩
  exact closedSliceMin_le table _ _ k hk.1 hk.2

theorem guarded_bank_lookup_le_exact_min {sl sh : ℚ} (x : I80)
    (hne : exactStart sl ≤ exactStop sh)
    (hl : x.decodeLo ≤ sl) (hh : sh ≤ x.decodeHi) :
    (bankDefectLookup x).lo ≤ closedSliceMin bankLowerTable (exactStart sl) (exactStop sh) := by
  by_cases hguard : lookupGuard x true
  · simpa only [bankDefectLookup, defectLookup, if_pos hguard, I80.raw] using
      bankSlice_nonneg (exactStart sl) (exactStop sh)
  · simpa only [bankDefectLookup, defectLookup, if_neg hguard, I80.raw] using
      outward_min_le_exact_min bankLowerTable x hne hl hh

def rowSL (r : Row) : ℚ := sourceRL r / Certificates.P2HistoricQ80DefectLookup.a
def rowSH (r : Row) : ℚ := sourceRH r / Certificates.P2HistoricQ80DefectLookup.a
def rowHNumerator (r : Row) : ℤ :=
  closedSliceMin bankLowerTable (exactStart (rowSL r)) (exactStop (rowSH r))
def rowHB (r : Row) : ℝ := decodeQ80 (rowHNumerator r)

theorem row_exact_domain (r : Row) : 1 < rowSL r ∧ rowSL r < rowSH r ∧ rowSH r < 4 := by
  obtain ⟨hi, _hjpos, hj⟩ := indices_bounds r
  have hs := P2HistoricChordDivisorGuard.parent_s_range hi hj
  have hspan := P2HistoricChordDivisorGuard.parent_plane1_gap_pos (indices r).1 (indices r).2
  have ha : (0 : ℚ) < Certificates.P2HistoricQ80DefectLookup.a := by
    norm_num [Certificates.P2HistoricQ80DefectLookup.a]
  exact ⟨hs.1, (div_lt_div_iff_of_pos_right ha).mpr hspan, hs.2⟩

theorem row_exact_nonempty (r : Row) : exactStart (rowSL r) ≤ exactStop (rowSH r) :=
  exact_slice_nonempty (row_exact_domain r).1.le (row_exact_domain r).2.1.le
    ((row_exact_domain r).2.2.le.trans (by norm_num))

theorem row_outward_query_eq (r : Row) :
    rowDefectArgument r = I80.ofEnclosure ⟨rowSL r, rowSH r⟩ := by
  simp only [rowDefectArgument, rowResidualRange, source_range_same_row r,
    rowSL, rowSH, sourceRL, sourceRH]

theorem row_outward_encloses_exact (r : Row) :
    (rowDefectArgument r).decodeLo ≤ rowSL r ∧ rowSH r ≤ (rowDefectArgument r).decodeHi := by
  rw [row_outward_query_eq]
  have hl := (I80.lower_rounding ⟨rowSL r, rowSH r⟩).1
  have hh := (I80.upper_rounding ⟨rowSL r, rowSH r⟩).1
  exact ⟨by linarith, by linarith⟩

theorem row_exact_cell_also_old (r : Row) (k : ℤ)
    (hk : exactStart (rowSL r) ≤ k ∧ k ≤ exactStop (rowSH r)) :
    lookupStart 50 (rowDefectArgument r) ≤ k ∧ k ≤ lookupStop 50 (rowDefectArgument r) :=
  exact_slice_subset_outward _ (row_outward_encloses_exact r).1
    (row_outward_encloses_exact r).2 k hk

theorem decoded_mono {m n : ℤ} (hmn : m ≤ n) : decodeQ80 m ≤ decodeQ80 n := by
  have hq : (m : ℚ) / Q ≤ (n : ℚ) / Q :=
    div_le_div_of_nonneg_right (by exact_mod_cast hmn) Q_pos.le
  exact_mod_cast hq

theorem rowHB_nonneg (r : Row) : 0 ≤ rowHB r := by
  have hn := decoded_mono (bankSlice_nonneg (exactStart (rowSL r)) (exactStop (rowSH r)))
  simpa only [rowHB, rowHNumerator, decodeQ80, Int.cast_zero, zero_div, Rat.cast_zero] using hn

theorem row_old_lookup_le_HB (r : Row) :
    ((bankDefectLookup (rowDefectArgument r)).decodeLo : ℝ) ≤ rowHB r := by
  exact decoded_mono (guarded_bank_lookup_le_exact_min (rowDefectArgument r)
    (row_exact_nonempty r) (row_outward_encloses_exact r).1 (row_outward_encloses_exact r).2)

/-- At s=2 the exact closed interval retains the preceding zero cell49. -/
theorem rowHB_zero_of_two_mem (r : Row) (hl : rowSL r ≤ 2) (hh : 2 ≤ rowSH r) : rowHB r = 0 := by
  have hk : exactStart (rowSL r) ≤ 49 ∧ 49 ≤ exactStop (rowSH r) := by
    apply (exact_indices_iff _ _ _).mpr
    norm_num [cellLeft, cellRight]
    exact ⟨hl, (by linarith)⟩
  have hzero : bankLowerTable 49 = 0 := by norm_num [bankLowerTable, bankLowerNumerators]
  have hle : rowHNumerator r ≤ 0 := by
    unfold rowHNumerator
    simpa only [hzero] using closedSliceMin_le bankLowerTable _ _ 49 hk.1 hk.2
  have hdec := decoded_mono hle
  have hupper : rowHB r ≤ 0 := by simpa only [rowHB, decodeQ80, Int.cast_zero, zero_div, Rat.cast_zero] using hdec
  exact le_antisymm hupper (rowHB_nonneg r)

theorem exactStop_right_covers {sh : ℚ} (hsh : sh ≤ 5) : sh ≤ cellRight (exactStop sh) := by
  have hs : (sh - 1) * 50 ≤ (exactStop sh : ℚ) + 1 := by
    unfold exactStop
    rcases le_total (199 : ℤ) ⌊(sh - 1) * 50⌋ with h | h
    · rw [min_eq_left h]
      norm_num
      linarith
    · rw [min_eq_right h]
      exact (Int.lt_floor_add_one _).le
  dsimp [cellRight]
  linarith

/-- The exact minimum itself retains the last meeting cell.  Its original
bank endpoint licence therefore controls H_B at the exact upper query. -/
theorem rowHB_le_actual_upper_endpoint {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hbank : BankEndpointLicences δ)
    (r : Row) (hpos : 2 * ordinaryA ≤ rowResidualLo r) :
    rowHB r ≤ P2TableActionSourceOnly.h δ (rowResidualHi r / ordinaryA) := by
  let k := exactStop (rowSH r)
  have hk := (exact_indices_iff (rowSL r) (rowSH r) k).mp ⟨row_exact_nonempty r, le_rfl⟩
  have hs2 : (2 : ℚ) ≤ rowSL r := by
    have h2 : (2 : ℝ) ≤ rowResidualLo r / ordinaryA := (le_div_iff₀ ordinaryA_pos).mpr hpos
    rw [← (source_query_casts r).1] at h2
    exact_mod_cast h2
  have hr2 : (2 : ℚ) ≤ cellRight k := hs2.trans hk.2.2.1
  have hr5 : cellRight k ≤ 5 := by
    have hki : (k : ℚ) ≤ 199 := by exact_mod_cast hk.2.1
    dsimp [cellRight]
    linarith
  have hcover : rowSH r ≤ cellRight k := exactStop_right_covers
    ((row_exact_domain r).2.2.le.trans (by norm_num))
  have hmin : rowHNumerator r ≤ bankLowerTable k :=
    closedSliceMin_le bankLowerTable _ _ k (row_exact_nonempty r) le_rfl
  have hlic := hbank k hk.1 hk.2.1 (by exact_mod_cast hr2)
  have hmono := Wu2008DoubleSieve.wuImprovementLimit_lower_antitone hδ hδhi
    (show (rowSH r : ℝ) ∈ Icc (2 : ℝ) 10 from by
      constructor
      · exact_mod_cast hs2.trans (row_exact_domain r).2.1.le
      · have h4 : (rowSH r : ℝ) < 4 := by exact_mod_cast (row_exact_domain r).2.2
        linarith)
    (show (cellRight k : ℝ) ∈ Icc (2 : ℝ) 10 from by
      constructor
      · exact_mod_cast hr2
      · have hr5R : (cellRight k : ℝ) ≤ 5 := by exact_mod_cast hr5
        linarith)
    (by exact_mod_cast hcover)
  have hlic' : decodeQ80 (bankLowerTable k) ≤ P2TableActionSourceOnly.h δ (cellRight k : ℝ) := hlic
  have hbound : rowHB r ≤ P2TableActionSourceOnly.h δ (rowSH r : ℝ) :=
    (decoded_mono hmin).trans (hlic'.trans hmono)
  simpa only [rowSH, (source_query_casts r).2] using hbound

end

end ImbalancedChen.P2HistoricalDefectClosedProxy
