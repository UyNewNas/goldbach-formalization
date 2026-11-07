import ImbalancedChen.P2HistoricalDefectClosedProxy

/-!
SOURCE ONLY, uncompiled.  Add the separate exact closed-cell H_B proxy to
the frozen ordinary proxy.  Actual directed historical arithmetic supplies
the saved-output upper comparison.  The original bank endpoint licences
are used only for the independent comparison with the actual Wu-h density.
No total integer equality or numerical proxy sum is asserted/evaluated.
-/

namespace ImbalancedChen.P2HistoricalFullFloorProxyChain

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2SavedFloorSemantics P2HistoricQ80OrdinaryEstimatorSoundness
open P2HistoricDefectIntegralMeasurability P2HistoricSavedOrdinaryDefectAssembly
open P2HistoricalSavedFloorRowsBinder P2HistoricalSavedFloorFullBinder
open P2HistoricalSavedFloorSelectedUnion P2HistoricalOrdinaryProxyIntegral
open P2HistoricalOrdinaryProxySourceUpper P2HistoricalDefectClosedProxy

/-- Exact historical arithmetic preceding the separate positive part. -/
def rowDefectRaw (r : Row) : I80 :=
  let z := bankDefectLookup (rowDefectArgument r)
  (((I80.point 4).mul z).mul
    (rectangleMass actualLog (rowTL r) (rowTR r) (rowUL r) (rowUR r))).div
      (I80.point (rowResidualRange r).2)

/-- On a positive cell this is exactly H_B M_B/R_B in quarter units.
The strict crossing branch records the source's zero lookup. -/
def rowDefectProxy (r : Row) : ℝ :=
  if 2 * ordinaryA ≤ rowResidualLo r then rowHB r * rowMass r / rowResidualHi r else 0
def rowFullProxy (r : Row) : ℝ := rowOrdinaryProxy r + rowDefectProxy r
def selectedFullProxy : ℝ := ∑ r : Row, rowFullProxy r

private theorem row_mass_nonneg (r : Row) : 0 ≤ rowMass r := by
  rcases row_geometry r with ⟨htl, hul, ht, hu, _hmu⟩
  have htR : (rowTL r : ℝ) ≤ rowTR r := by exact_mod_cast ht
  have huR : (rowUL r : ℝ) ≤ rowUR r := by exact_mod_cast hu
  have ht1 : 1 ≤ (rowTR r : ℝ) / rowTL r :=
    (le_div_iff₀ htl).mpr (by simpa using htR)
  have hu1 : 1 ≤ (rowUR r : ℝ) / rowUL r :=
    (le_div_iff₀ hul).mpr (by simpa using huR)
  exact mul_nonneg (Real.log_nonneg ht1) (Real.log_nonneg hu1)

theorem rowResidualHi_pos (r : Row) : 0 < rowResidualHi r := by
  have ha : (0 : ℚ) < Certificates.P2HistoricQ80DefectLookup.a := by
    norm_num [Certificates.P2HistoricQ80DefectLookup.a]
  have hlo : Certificates.P2HistoricQ80DefectLookup.a < sourceRL r :=
    (one_lt_div ha).mp (row_exact_domain r).1
  have hspan : sourceRL r < sourceRH r :=
    P2HistoricChordDivisorGuard.parent_plane1_gap_pos (indices r).1 (indices r).2
  have hpos : (0 : ℚ) < sourceRH r := ha.trans (hlo.trans hspan)
  have hreal : (0 : ℝ) < (sourceRH r : ℝ) := by exact_mod_cast hpos
  simpa only [(source_residual_casts r).2] using hreal

theorem rowDefect_denominator_positive (r : Row) :
    0 < (I80.point (rowResidualRange r).2).lo := by
  have ha : (0 : ℚ) < Certificates.P2HistoricQ80DefectLookup.a := by
    norm_num [Certificates.P2HistoricQ80DefectLookup.a]
  have hlo : Certificates.P2HistoricQ80DefectLookup.a < sourceRL r :=
    (one_lt_div ha).mp (row_exact_domain r).1
  have hspan : sourceRL r < sourceRH r :=
    P2HistoricChordDivisorGuard.parent_plane1_gap_pos (indices r).1 (indices r).2
  have hunit : (1 : ℚ) / Q ≤ Certificates.P2HistoricQ80DefectLookup.a := by
    norm_num [Certificates.P2HistoricQ80DefectLookup.a, Q]
  have hd := P2HistoricChordDivisorGuard.point_lo_pos_of_unit_gap (sourceRH r)
    (hunit.trans (hlo.trans hspan).le)
  simpa only [rowResidualRange, source_range_same_row r, sourceRH] using hd

theorem rowDefectRaw_contains_actual_mass (r : Row) :
    (rowDefectRaw r).Contains
      (4 * ((bankDefectLookup (rowDefectArgument r)).decodeLo : ℝ) *
        rowMass r / rowResidualHi r) := by
  rcases actualLog_row_contract r with ⟨hlogt, hlogu⟩
  have hm : (rectangleMass actualLog (rowTL r) (rowTR r) (rowUL r) (rowUR r)).Contains
      (rowMass r) := by
    simpa only [rectangleMassValue, rowMass, realMass, Rat.cast_div] using
      rectangleMass_contains actualLog (rowTL r) (rowTR r) (rowUL r) (rowUR r) hlogt hlogu
  have hrr : (((rowResidualRange r).2 : ℚ) : ℝ) = rowResidualHi r := by
    simpa only [rowResidualRange, source_range_same_row r, sourceRH] using
      (source_residual_casts r).2
  have hp := I80.point_contains (rowResidualRange r).2
  rw [hrr] at hp
  have hv := I80.div_contains
    (I80.mul_contains
      (I80.mul_contains (I80.point_contains 4)
        (bankDefectLookup_contains_decode (rowDefectArgument r))) hm)
    hp (rowDefect_denominator_positive r)
  simpa only [rowDefectRaw, Rat.cast_ofNat, mul_assoc] using hv

theorem rowDefectProxy_nonneg (r : Row) : 0 ≤ rowDefectProxy r := by
  unfold rowDefectProxy
  split_ifs
  · exact div_nonneg (mul_nonneg (rowHB_nonneg r) (row_mass_nonneg r))
      (rowResidualHi_pos r).le
  · exact le_rfl

private theorem decoded_max_le {m n : ℤ} {v : ℝ}
    (hm : decodeQ80 m ≤ v) (hn : decodeQ80 n ≤ v) : decodeQ80 (max m n) ≤ v := by
  rcases le_total m n with h | h
  · simpa only [max_eq_right h] using hn
  · simpa only [max_eq_left h] using hm

theorem actual_defect_credit_le_proxy (r : Row) :
    decodeQ80 (rowDefectCredit actualLog r) / 4 ≤ rowDefectProxy r := by
  have hvlo : decodeQ80 (rowDefectRaw r).lo ≤
      4 * ((bankDefectLookup (rowDefectArgument r)).decodeLo : ℝ) * rowMass r /
        rowResidualHi r := (rowDefectRaw_contains_actual_mass r).1
  have hzero : decodeQ80 0 ≤ 4 * rowDefectProxy r := by
    simpa only [decodeQ80, Int.cast_zero, zero_div, Rat.cast_zero] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (rowDefectProxy_nonneg r)
  have hraw : decodeQ80 (rowDefectRaw r).lo ≤ 4 * rowDefectProxy r := by
    by_cases hpos : 2 * ordinaryA ≤ rowResidualLo r
    · have hprod := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (row_old_lookup_le_HB r) (by norm_num : (0 : ℝ) ≤ 4))
        (row_mass_nonneg r)
      have hratio := div_le_div_of_nonneg_right hprod (rowResidualHi_pos r).le
      apply hvlo.trans
      convert hratio using 1 <;> simp only [rowDefectProxy, if_pos hpos] <;> ring
    · have hcR : rowResidualLo r / ordinaryA < 2 :=
        (div_lt_iff₀ ordinaryA_pos).mpr (lt_of_not_ge hpos)
      rw [← (source_query_casts r).1] at hcR
      have hc : rowSL r < 2 := by exact_mod_cast hcR
      have hz : bankDefectLookup (rowDefectArgument r) = I80.raw 0 :=
        P2HistoricChordDivisorGuard.parent_crossing_defect_zero
          (indices r).1 (indices r).2 50 bankLowerTable hc
      have hraw0 : decodeQ80 (rowDefectRaw r).lo ≤ 0 := by
        simpa only [hz, I80.raw, I80.decodeLo, Int.cast_zero, zero_div, Rat.cast_zero,
          mul_zero, zero_mul] using hvlo
      simpa only [rowDefectProxy, if_neg hpos, mul_zero] using hraw0
  have hmax : decodeQ80 (rowDefectCredit actualLog r) ≤ 4 * rowDefectProxy r :=
    decoded_max_le hzero hraw
  linarith

/-- The analytic direction needs the actual bank licences.  They are not
deduced from the finite minimum or from a successful producer comparison. -/
theorem rowDefectProxy_le_actual {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hbank : BankEndpointLicences δ) (r : Row) :
    rowDefectProxy r ≤ guardedDefectIntegral δ
      (rowTL r) (rowTR r) (rowUL r) (rowUR r) / 4 := by
  by_cases hpos : 2 * ordinaryA ≤ rowResidualLo r
  · rcases row_geometry r with ⟨htl, hul, ht, hu, _hmu⟩
    have htR : (rowTL r : ℝ) ≤ rowTR r := by exact_mod_cast ht
    have huR : (rowUL r : ℝ) ≤ rowUR r := by exact_mod_cast hu
    have hrl : 0 < rowResidualLo r := by have := ordinaryA_pos; linarith
    have hhi : rowResidualHi r / ordinaryA ≤ 5 :=
      (row_residual_query_le_four r).trans (by norm_num)
    have hlower := guarded_defect_logmass_lower hδ hδhi htl hul hrl htR huR
      (fun t ht' u hu' => row_residual_range r ht' hu') hhi (rowHB_nonneg r)
      (fun hc => False.elim ((not_lt_of_ge hpos) hc))
      (fun _hpos => rowHB_le_actual_upper_endpoint hδ hδhi hbank r hpos)
    change 4 * rowHB r * rowMass r / rowResidualHi r ≤
      guardedDefectIntegral δ (rowTL r) (rowTR r) (rowUL r) (rowUR r) at hlower
    have he : 4 * rowDefectProxy r = 4 * rowHB r * rowMass r / rowResidualHi r := by
      simp only [rowDefectProxy, if_pos hpos]
      ring
    rw [← he] at hlower
    linarith
  · rw [rowDefectProxy, if_neg hpos]
    exact div_nonneg (row_guardedDefectIntegral_nonneg hδ hδhi r) (by norm_num)

theorem decodeQ80_add (m n : ℤ) : decodeQ80 (m + n) = decodeQ80 m + decodeQ80 n := by
  simp only [decodeQ80, Int.cast_add, add_div, Rat.cast_add]

theorem actual_full_saved_le_proxy (r : Row) :
    decodeQ80 (rowSourceOutput actualSf actualLog r) / 4 ≤ rowFullProxy r := by
  rw [rowSourceOutput_eq_components, decodeQ80_add]
  have ho := actual_saved_ordinary_le_proxy r
  have hd := actual_defect_credit_le_proxy r
  unfold rowFullProxy
  linarith

theorem checked_frozen_full_saved_le_proxy (r : Row) (hc : fullSourceRowCheck r = true) :
    decodeQ80 (frozenSavedRow r).savedQ80 / 4 ≤ rowFullProxy r := by
  rw [(fullSourceRowCheck_sound r hc).2.2]
  exact actual_full_saved_le_proxy r

theorem rowFullProxy_le_actual {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hbank : BankEndpointLicences δ) (r : Row) :
    rowFullProxy r ≤ rowCompleteActualIntegral δ r / 4 := by
  have ho := rowOrdinaryProxy_le_actual r
  have hd := rowDefectProxy_le_actual hδ hδhi hbank r
  unfold rowFullProxy rowCompleteActualIntegral
  linarith

theorem selectedFullProxy_le_actual_union {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hbank : BankEndpointLicences δ) :
    selectedFullProxy ≤ selectedUnionIntegral δ / 4 := by
  rw [selectedUnionIntegral_eq_fullCompleteActualIntegral hδ hδhi]
  unfold selectedFullProxy fullCompleteActualIntegral
  calc
    (∑ r : Row, rowFullProxy r) ≤ ∑ r : Row, rowCompleteActualIntegral δ r / 4 :=
      Finset.sum_le_sum (fun r _hr => rowFullProxy_le_actual hδ hδhi hbank r)
    _ = (∑ r : Row, rowCompleteActualIntegral δ r) / 4 := by rw [Finset.sum_div]

/-- Complete saved numerator retained, with exactly one division by four.
The left comparison is finite-source arithmetic; only the right comparison
uses the explicit endpoint bank licences of the actual analytic h family. -/
theorem checked_full_proxy_sandwich {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hbank : BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4) ≤ selectedFullProxy ∧
      selectedFullProxy ≤ selectedUnionIntegral δ / 4 := by
  exact ⟨Finset.sum_le_sum (fun r _hr => checked_frozen_full_saved_le_proxy r (hc r)),
    selectedFullProxy_le_actual_union hδ hδhi hbank⟩

end

end ImbalancedChen.P2HistoricalFullFloorProxyChain
