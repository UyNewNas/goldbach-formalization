import ImbalancedChen.P2HistoricalOrdinaryProxyIntegral

/-!
SOURCE ONLY; uncompiled.  Bind the independent ordinary upper proxy to the
actual historical sf/log producers, their two-plane max, and the same Row.
The two source-only files in this directory and the frozen first-batch
selected-union file require the installation mappings in REGISTRY.json.
No stored-total identity, numerical proxy evaluation or Wu-bank licence is
used.  The defect credit is explicitly subtracted when reading frozen rows.
-/

namespace ImbalancedChen.P2HistoricalOrdinaryProxySourceUpper

noncomputable section

open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2SavedFloorSemantics P2HistoricQ80OrdinaryEstimatorSoundness
open P2HistoricalSavedFloorRowsBinder P2HistoricalSavedFloorFullBinder
open P2HistoricalSavedFloorSelectedUnion P2HistoricalOrdinaryProxyIntegral

def sourceRL (r : Row) : ℚ :=
  (affineRange ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).1
def sourceRH (r : Row) : ℚ :=
  (affineRange ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).2

theorem source_residual_casts (r : Row) :
    (sourceRL r : ℝ) = rowResidualLo r ∧ (sourceRH r : ℝ) = rowResidualHi r := by
  constructor <;> simp only [sourceRL, sourceRH,
    P2HistoricChordDivisorGuard.ordinaryPlane1_range]
  all_goals norm_num [rowResidualLo, rowResidualHi, ordinaryResidual]
  all_goals ring

theorem source_query_casts (r : Row) :
    ((sourceRL r / Certificates.P2HistoricQ80DefectLookup.a : ℚ) : ℝ) =
        rowResidualLo r / ordinaryA ∧
      ((sourceRH r / Certificates.P2HistoricQ80DefectLookup.a : ℚ) : ℝ) =
        rowResidualHi r / ordinaryA := by
  rcases source_residual_casts r with ⟨hl, hh⟩
  constructor <;> simp only [Rat.cast_div, cast_source_a, hl, hh]

theorem source_range_same_row (r : Row) :
    ordinaryRanges (rowTL r) (rowTR r) (rowUL r) (rowUR r) =
      affineRange ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r) :=
  P2HistoricChordDivisorGuard.parent_ordinaryRanges (indices r).1 (indices r).2

theorem source_plane0_ineligible (r : Row) :
    ¬ chordEligible ordinaryPlane₀ ordinaryPlane₁
      (rowTL r) (rowTR r) (rowUL r) (rowUR r) :=
  fun hc => P2HistoricChordDivisorGuard.parent_plane0_not_accepted
    (indices r).1 (indices r).2 hc.1

theorem actual_sf_endpoint_lows_le_exact (r : Row)
    (hpos : 2 * ordinaryA ≤ rowResidualLo r) :
    ((actualSf (sourceRL r / Certificates.P2HistoricQ80DefectLookup.a)).decodeLo : ℝ) ≤
        rowFL r ∧
      ((actualSf (sourceRH r / Certificates.P2HistoricQ80DefectLookup.a)).decodeLo : ℝ) ≤
        rowFH r := by
  rcases source_query_casts r with ⟨hql, hqh⟩
  rcases row_exact_endpoint_values r hpos with ⟨hfl, hfh⟩
  have hl := (actualSf_contract (sourceRL r / Certificates.P2HistoricQ80DefectLookup.a)).1
  have hh := (actualSf_contract (sourceRH r / Certificates.P2HistoricQ80DefectLookup.a)).1
  rw [hql, ← hfl] at hl
  rw [hqh, ← hfh] at hh
  exact ⟨hl, hh⟩

private theorem row_mass_nonneg (r : Row) : 0 ≤ rowMass r := by
  rcases row_geometry r with ⟨htl, hul, ht, hu, _hmu⟩
  have htR : (rowTL r : ℝ) ≤ rowTR r := by exact_mod_cast ht
  have huR : (rowUL r : ℝ) ≤ rowUR r := by exact_mod_cast hu
  have ht1 : 1 ≤ (rowTR r : ℝ) / rowTL r :=
    (le_div_iff₀ htl).mpr (by simpa using htR)
  have hu1 : 1 ≤ (rowUR r : ℝ) / rowUL r :=
    (le_div_iff₀ hul).mpr (by simpa using huR)
  exact mul_nonneg (Real.log_nonneg ht1) (Real.log_nonneg hu1)

private theorem positive_proxy_nonneg (r : Row)
    (hpos : 2 * ordinaryA ≤ rowResidualLo r) : 0 ≤ rowOrdinaryProxy r := by
  have hf : 0 ≤ rowFL r := by
    rw [(row_exact_endpoint_values r hpos).1]
    exact actualExtendedThirdLowerFactor_nonneg _
  have hb : 0 ≤ rowConstantProxy r :=
    div_nonneg (mul_nonneg hf (row_mass_nonneg r)) ordinaryA_pos.le
  exact hb.trans (by simp only [rowOrdinaryProxy, if_pos hpos]; exact le_max_left _ _)

private theorem decoded_max_le {x y : ℤ} {v : ℝ}
    (hx : decodeQ80 x ≤ v) (hy : decodeQ80 y ≤ v) : decodeQ80 (max x y) ≤ v := by
  rcases le_total x y with hxy | hyx
  · simpa only [max_eq_right hxy] using hy
  · simpa only [max_eq_left hyx] using hx

/-- The real exact base majorizes the literal Q80 lower output, using the
actual sf and log contracts already proved for the historical algorithms. -/
theorem source_base_decode_le_exact (r : Row) :
    decodeQ80 (ordinaryRectangleBase actualSf actualLog
      (rowTL r) (rowTR r) (rowUL r) (rowUR r) (sourceRL r)).lo ≤
      4 * actualExtendedThirdLowerFactor (rowResidualLo r / ordinaryA) *
        rowMass r / ordinaryA := by
  rcases actualLog_row_contract r with ⟨hlogt, hlogu⟩
  have hb := ordinaryRectangleBase_decodeLo_le actualSf actualLog
    (rowTL r) (rowTR r) (rowUL r) (rowUR r) (sourceRL r)
    (actualExtendedThirdLowerFactor
      ((sourceRL r / Certificates.P2HistoricQ80DefectLookup.a : ℚ) : ℝ))
    (actualSf_contract _) hlogt hlogu
  rw [(source_query_casts r).1] at hb
  have hm : rectangleMassValue (rowTL r) (rowTR r) (rowUL r) (rowUR r) = rowMass r := by
    simp only [rectangleMassValue, rowMass, realMass, Rat.cast_div]
  rw [hm, cast_source_a] at hb
  convert hb using 1 <;> dsimp [decodeQ80, I80.decodeLo] <;> ring

/-- The eligible literal descending chord is below the exact manuscript
chord, including its fixed-point roundings and the endpoint replacements. -/
theorem source_chord_decode_le_proxy (r : Row)
    (hpos : 2 * ordinaryA ≤ rowResidualLo r) :
    decodeQ80 (ordinaryRectangleChord actualSf actualLog
      (rowTL r) (rowTR r) (rowUL r) (rowUR r) ordinaryPlane₁).lo ≤
      4 * rowChordProxy r := by
  rcases actualLog_row_contract r with ⟨hlogt, hlogu⟩
  have hden := (P2HistoricChordDivisorGuard.parent_chord_divisors_positive
    (indices r).1 (indices r).2).2
  have hc := ordinaryRectangleChord_decodeLo_le actualSf actualLog
    (rowTL r) (rowTR r) (rowUL r) (rowUR r) ordinaryPlane₁ hlogt hlogu hden
  rcases actual_sf_endpoint_lows_le_exact r hpos with ⟨hfl, hfh⟩
  have hmono := row_chord_endpoint_lows_le_proxy r hfl hfh
  have he : ordinaryRectangleChordValue actualSf
      (rowTL r) (rowTR r) (rowUL r) (rowUR r) ordinaryPlane₁ =
      4 * ((((actualSf (sourceRL r / Certificates.P2HistoricQ80DefectLookup.a)).decodeLo : ℝ) *
        (rowResidualHi r * rowMass r - rowResidualMoment r) +
        ((actualSf (sourceRH r / Certificates.P2HistoricQ80DefectLookup.a)).decodeLo : ℝ) *
        (rowResidualMoment r - rowResidualLo r * rowMass r)) /
          (ordinaryA * (rowResidualHi r - rowResidualLo r))) := by
    have he' : ordinaryRectangleChordValue actualSf
        (rowTL r) (rowTR r) (rowUL r) (rowUR r) ordinaryPlane₁ =
        (4 / ordinaryA) *
          ((((actualSf (sourceRL r / Certificates.P2HistoricQ80DefectLookup.a)).decodeLo : ℝ) *
            ((sourceRH r : ℝ) * rowMass r -
              realMoment ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r)) +
            ((actualSf (sourceRH r / Certificates.P2HistoricQ80DefectLookup.a)).decodeLo : ℝ) *
            (realMoment ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r) -
              (sourceRL r : ℝ) * rowMass r)) /
            ((sourceRH r : ℝ) - (sourceRL r : ℝ))) := by
      simp only [ordinaryRectangleChordValue, sourceRL, sourceRH, rectangleMassValue,
        rectangleMomentTValue, rectangleMomentUValue, rowMass, realMass, realMoment,
        Rat.cast_div, Rat.cast_sub, cast_source_a]
      ring
    rw [he', row_realMoment_eq r, (source_residual_casts r).1,
      (source_residual_casts r).2]
    field_simp [ordinaryA_pos.ne', (sub_pos.mpr (row_residual_span r)).ne']
    <;> ring
  rw [he] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))

/-- The complete ordinary max and its strict crossing branch are bound to
the independent proxy.  This is an upper bound for a saved lower estimate;
it gives no upper bound for the true ordinary density. -/
theorem actual_saved_ordinary_le_proxy (r : Row) :
    decodeQ80 (rowOrdinaryOutput actualSf actualLog r) / 4 ≤ rowOrdinaryProxy r := by
  let b := (ordinaryRectangleBase actualSf actualLog
    (rowTL r) (rowTR r) (rowUL r) (rowUR r) (sourceRL r)).lo
  let c := (ordinaryRectangleChord actualSf actualLog
    (rowTL r) (rowTR r) (rowUL r) (rowUR r) ordinaryPlane₁).lo
  have hno0 := source_plane0_ineligible r
  have he : rowOrdinaryOutput actualSf actualLog r =
      max 0 (if chordEligible ordinaryPlane₁ ordinaryPlane₀
        (rowTL r) (rowTR r) (rowUL r) (rowUR r) then max b c else b) := by
    simp only [rowOrdinaryOutput, savedOrdinaryRectangle, source_range_same_row r,
      if_neg hno0, sourceRL, b, c]
  have hb := source_base_decode_le_exact r
  by_cases hpos : 2 * ordinaryA ≤ rowResidualLo r
  · have hfl := (row_exact_endpoint_values r hpos).1
    rw [← hfl] at hb
    have hbase : decodeQ80 b ≤ 4 * rowConstantProxy r := by
      convert hb using 1 <;> dsimp [b, rowConstantProxy] <;> ring
    have hchord : decodeQ80 c ≤ 4 * rowChordProxy r := source_chord_decode_le_proxy r hpos
    have hbase' : decodeQ80 b ≤ 4 * rowOrdinaryProxy r :=
      hbase.trans (mul_le_mul_of_nonneg_left
        (by simp only [rowOrdinaryProxy, if_pos hpos]; exact le_max_left _ _) (by norm_num))
    have hchord' : decodeQ80 c ≤ 4 * rowOrdinaryProxy r :=
      hchord.trans (mul_le_mul_of_nonneg_left
        (by simp only [rowOrdinaryProxy, if_pos hpos]; exact le_max_right _ _) (by norm_num))
    have hz : decodeQ80 0 ≤ 4 * rowOrdinaryProxy r := by
      simpa only [decodeQ80, Int.cast_zero, zero_div, Rat.cast_zero] using
        mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (positive_proxy_nonneg r hpos)
    have hbest : decodeQ80 (rowOrdinaryOutput actualSf actualLog r) ≤
        4 * rowOrdinaryProxy r := by
      rw [he]
      apply decoded_max_le hz
      split_ifs
      · exact decoded_max_le hbase' hchord'
      · exact hbase'
    linarith
  · have hquery : rowResidualLo r / ordinaryA ≤ 2 :=
      (div_le_iff₀ ordinaryA_pos).mpr (le_of_lt (lt_of_not_ge hpos))
    rw [actualExtendedThirdLowerFactor_of_le_two hquery] at hb
    have hb0 : decodeQ80 b ≤ 0 := by simpa only [mul_zero, zero_mul, zero_div] using hb
    have hno1 : ¬ chordEligible ordinaryPlane₁ ordinaryPlane₀
        (rowTL r) (rowTR r) (rowUL r) (rowUR r) := by
      intro hc
      have hl : 2 * (Certificates.P2HistoricQ80DefectLookup.a : ℝ) ≤ (sourceRL r : ℝ) := by
        exact_mod_cast hc.2.1
      rw [cast_source_a, (source_residual_casts r).1] at hl
      exact hpos hl
    have hbest : decodeQ80 (rowOrdinaryOutput actualSf actualLog r) ≤ 0 := by
      rw [he, if_neg hno1]
      exact decoded_max_le (by norm_num [decodeQ80]) hb0
    rw [rowOrdinaryProxy, if_neg hpos]
    linarith

theorem checked_frozen_ordinary_component_le_proxy (r : Row)
    (hc : fullSourceRowCheck r = true) :
    decodeQ80 ((frozenSavedRow r).savedQ80 - rowDefectCredit actualLog r) / 4 ≤
      rowOrdinaryProxy r := by
  have he : (frozenSavedRow r).savedQ80 - rowDefectCredit actualLog r =
      rowOrdinaryOutput actualSf actualLog r := by
    rw [(fullSourceRowCheck_sound r hc).2.2, rowSourceOutput_eq_components]
    omega
  rw [he]
  exact actual_saved_ordinary_le_proxy r

/-- Same-mask upper proxy and genuine complete integral, with neither a
total-integer certificate nor a bank endpoint premise hidden in the chain. -/
theorem checked_selected_ordinary_proxy_sandwich {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) :
    (∑ r : Row,
      decodeQ80 ((frozenSavedRow r).savedQ80 - rowDefectCredit actualLog r) / 4) ≤
        selectedOrdinaryProxy ∧
      selectedOrdinaryProxy ≤ selectedOrdinaryIntegral / 4 ∧
        selectedOrdinaryIntegral / 4 ≤ selectedUnionIntegral δ / 4 := by
  refine ⟨Finset.sum_le_sum (fun r _hr => checked_frozen_ordinary_component_le_proxy r (hc r)),
    selectedOrdinaryProxy_le_actual_integral, ?_⟩
  exact div_le_div_of_nonneg_right (selectedOrdinaryIntegral_le_complete_union hδ hδhi)
    (by norm_num)

end

end ImbalancedChen.P2HistoricalOrdinaryProxySourceUpper
