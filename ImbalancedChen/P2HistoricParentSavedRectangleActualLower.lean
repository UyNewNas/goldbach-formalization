import ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly

/-!
The literal source pair_cell output is the ordinary maximum plus the
positive part of the rounded defect term.  This module supplies the missing
parent-level composition.  Its only analytic table input is the licence for
the 200 actual h-bank endpoints.  SOURCE WRITTEN, UNCOMPILED.
-/

namespace ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly

noncomputable section

open Set MeasureTheory P2SavedFloorSemantics
open Certificates.P2DirectedLogRounding
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricBackendTypeAdapters
open Certificates.PairedV2
open P2SavedFloorSubdivisionEstimator
open P2HistoricQ80OrdinaryEstimatorSoundness
open P2HistoricDefectIntegralMeasurability
open P2HistoricOrdinaryParentClosed
open scoped Interval

private def parentRange (i j : Fin 512) : ℚ × ℚ :=
  ordinaryRanges (tLower i.val) (tUpper i.val) (uLower j.val) (uUpper j.val)

private def parentQuery (i j : Fin 512) : I80 :=
  I80.ofEnclosure ⟨(parentRange i j).1 / a, (parentRange i j).2 / a⟩

private def parentDefectValue (i j : Fin 512) : I80 :=
  let rr := parentRange i j
  let z := bankDefectLookup (parentQuery i j)
  (((I80.point 4).mul z).mul
    (rectangleMass sourceLogI (tLower i.val) (tUpper i.val)
      (uLower j.val) (uUpper j.val))).div (I80.point rr.2)

private theorem parentRange_strict (i j : Fin 512) :
    (parentRange i j).1 < (parentRange i j).2 := by
  simpa only [parentRange, P2HistoricChordDivisorGuard.parent_ordinaryRanges] using
    P2HistoricChordDivisorGuard.parent_plane1_gap_pos i.val j.val

private theorem parentRange_pointwise (i j : Fin 512) :
    ∀ t ∈ Icc (parentTL i) (parentTR i),
      ∀ u ∈ Icc (parentUL j) (parentUR j),
        ordinaryResidual t u ∈
          Icc ((parentRange i j).1 : ℝ) ((parentRange i j).2 : ℝ) := by
  intro t ht u hu
  have h := affineRange_real_enclosure ordinaryPlane₁
    (tLower i.val) (tUpper i.val) (uLower j.val) (uUpper j.val) ht hu
  rw [ordinaryPlane₁_real] at h
  simpa only [parentRange, P2HistoricChordDivisorGuard.parent_ordinaryRanges] using h

private theorem parentQuery_rounding (i j : Fin 512) :
    (parentQuery i j).lo ≤ (parentQuery i j).hi ∧
      (((parentRange i j).2 / a : ℚ) : ℝ) ≤
        ((parentQuery i j).decodeHi : ℝ) := by
  let rr := parentRange i j
  let E : Enclosure := ⟨rr.1 / a, rr.2 / a⟩
  have hl := (I80.lower_rounding E).1
  have hu := (I80.upper_rounding E).1
  have ha : (0 : ℚ) < a := by norm_num [a]
  have hr : rr.1 / a ≤ rr.2 / a :=
    div_le_div_of_nonneg_right (parentRange_strict i j).le ha.le
  have hq : (parentQuery i j).decodeLo ≤ (parentQuery i j).decodeHi := by
    change rr.1 / a - (parentQuery i j).decodeLo ≥ 0 at hl
    change (parentQuery i j).decodeHi - rr.2 / a ≥ 0 at hu
    linarith
  have hq' : ((parentQuery i j).lo : ℚ) ≤ (parentQuery i j).hi := by
    change ((parentQuery i j).lo : ℚ) / Q ≤ (parentQuery i j).hi / Q at hq
    have hm := (div_le_div_iff₀ Q_pos Q_pos).mp hq
    exact (mul_le_mul_right Q_pos).mp (by simpa [mul_comm] using hm)
  constructor
  · exact_mod_cast hq'
  · have h : rr.2 / a ≤ (parentQuery i j).decodeHi := by
      change (parentQuery i j).decodeHi - rr.2 / a ≥ 0 at hu
      linarith
    exact_mod_cast h

private theorem parentDefect_denominator_positive (i j : Fin 512) :
    0 < (I80.point (parentRange i j).2).lo := by
  have ha : (0 : ℚ) < a := by norm_num [a]
  have hs : 1 < (parentRange i j).1 / a := by
    simpa only [parentRange, P2HistoricChordDivisorGuard.parent_ordinaryRanges] using
      (P2HistoricChordDivisorGuard.parent_s_range i.isLt j.isLt).1
  have hunit : (1 : ℚ) / Q ≤ a := by norm_num [a, Q]
  have h : (1 : ℚ) / Q ≤ (parentRange i j).2 := by
    have hlow : a < (parentRange i j).1 := (one_lt_div ha).mp hs
    linarith [parentRange_strict i j]
  exact P2HistoricChordDivisorGuard.point_lo_pos_of_unit_gap _ h

private theorem parent_defect_credit_actual_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : BankEndpointLicences δ) (i j : Fin 512) :
    decodeQ80 (max 0 (parentDefectValue i j).lo) ≤
      guardedDefectIntegral δ (parentTL i) (parentTR i) (parentUL j) (parentUR j) := by
  let rr := parentRange i j
  let x := parentQuery i j
  let z := bankDefectLookup x
  let hlow : ℝ := (z.decodeLo : ℝ)
  let rh : ℝ := (rr.2 : ℝ)
  let rl : ℝ := (rr.1 : ℝ)
  have hg := parent_geometry i j
  have hrange := parentRange_pointwise i j
  have hs := P2HistoricChordDivisorGuard.parent_s_range i.isLt j.isLt
  have haQ : (0 : ℚ) < a := by norm_num [a]
  have haR : (a : ℝ) = ordinaryA := cast_source_a
  have hrl : 0 < rl := by
    have hs1 : (1 : ℚ) < rr.1 / a := by
      simpa only [rr, parentRange, P2HistoricChordDivisorGuard.parent_ordinaryRanges] using hs.1
    have h : (0 : ℚ) < rr.1 := by
      have := (one_lt_div haQ).mp hs1
      linarith
    exact_mod_cast h
  have hrh : 0 < rh := hrl.trans_le (by exact_mod_cast (parentRange_strict i j).le)
  have hhi : rh / ordinaryA ≤ 5 := by
    have hs4 : rr.2 / a < (4 : ℚ) := by
      simpa only [rr, parentRange, P2HistoricChordDivisorGuard.parent_ordinaryRanges] using hs.2
    have h4 : rh / ordinaryA < 4 := by
      rw [← haR]
      exact_mod_cast hs4
    linarith
  have hh0 : 0 ≤ hlow := by
    have hz := bankDefectLookup_nonneg x
    have hzQ : (0 : ℚ) ≤ z.decodeLo := div_nonneg (by exact_mod_cast hz) Q_pos.le
    exact_mod_cast hzQ
  have hcross : rl < 2 * ordinaryA → hlow = 0 := by
    intro hc
    have hcQ : rr.1 < 2 * a := by
      rw [← haR] at hc
      exact_mod_cast hc
    have hz := literalLookup_real_crossing bankLowerTable hcQ
    have hx : z = I80.raw 0 := by
      simpa only [z, x, parentQuery, rr, parentRange, bankDefectLookup] using hz
    simp [hlow, hx, I80.raw, I80.decodeLo]
  have hh : 2 * ordinaryA ≤ rl →
      hlow ≤ P2TableActionSourceOnly.h δ (rh / ordinaryA) := by
    intro hs2a
    have hs2 : (2 : ℝ) ≤ rh / ordinaryA := by
      have hle : rl ≤ rh := by exact_mod_cast (parentRange_strict i j).le
      exact (le_div_iff₀ ordinaryA_pos).mpr (by linarith)
    have hs5 : rh / ordinaryA ≤ 5 := hhi
    have hquery : rh / ordinaryA ≤ (x.decodeHi : ℝ) := by
      rw [← haR]
      simpa only [rh, rr, x] using (parentQuery_rounding i j).2
    exact bankDefectLookup_endpoint_sound hδ hδhi hbank x
      (parentQuery_rounding i j).1 hs2 hs5 hquery
  have hintegral := guarded_defect_logmass_lower hδ hδhi hg.1 hg.2.1
    hrl hg.2.2.1 hg.2.2.2.1 hrange hhi hh0 hcross hh
  have hzero := guarded_defect_integral_nonneg hδ hδhi hg.1 hg.2.1
    hrl hg.2.2.1 hg.2.2.2.1 hrange hhi
  have htQ : (0 : ℚ) < tLower i.val := by exact_mod_cast hg.1
  have huQ : (0 : ℚ) < uLower j.val := by exact_mod_cast hg.2.1
  have htordQ : tLower i.val ≤ tUpper i.val := by exact_mod_cast hg.2.2.1
  have huordQ : uLower j.val ≤ uUpper j.val := by exact_mod_cast hg.2.2.2.1
  have hmass := source_rectangleMass_contains
    (tLower i.val) (tUpper i.val) (uLower j.val) (uUpper j.val)
      htQ huQ htordQ huordQ
  have hv : (parentDefectValue i j).Contains
      (4 * hlow * realMass (parentTL i) (parentTR i) (parentUL j) (parentUR j) / rh) := by
    have hmass' : (rectangleMass sourceLogI (tLower i.val) (tUpper i.val)
      (uLower j.val) (uUpper j.val)).Contains
        (realMass (parentTL i) (parentTR i) (parentUL j) (parentUR j)) := by
      convert hmass using 1
      simp [rectangleMassValue, realMass, parentTL, parentTR, parentUL, parentUR]
    have hp : (I80.point rr.2).Contains rh := I80.point_contains rr.2
    have hfour : (I80.point 4).Contains (4 : ℝ) := I80.point_contains 4
    simpa only [parentDefectValue, rr, x, z, hlow, rh, mul_assoc] using
      (I80.div_contains
        (I80.mul_contains (I80.mul_contains hfour (bankDefectLookup_contains_decode x))
          hmass') hp (parentDefect_denominator_positive i j))
  have hvlo : decodeQ80 (parentDefectValue i j).lo ≤
      4 * hlow * realMass (parentTL i) (parentTR i) (parentUL j) (parentUR j) / rh :=
    hv.1
  by_cases hn : 0 ≤ (parentDefectValue i j).lo
  · simpa only [max_eq_right hn] using hvlo.trans hintegral
  · have hn' : (parentDefectValue i j).lo ≤ 0 := le_of_lt (lt_of_not_ge hn)
    simpa [max_eq_left hn', decodeQ80] using hzero

/-- Literal 512-grid parent, with both positive parts of pair_cell present. -/
theorem parent_sourceSavedRectangle_actual_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : BankEndpointLicences δ) (i j : Fin 512) :
    decodeQ80
        (sourceSavedRectangle sourceSf sourceLogI
          (tLower i.val) (tUpper i.val) (uLower j.val) (uUpper j.val)) ≤
      ordinaryParentIntegral i.val j.val +
        guardedDefectIntegral δ (parentTL i) (parentTR i) (parentUL j) (parentUR j) := by
  have ho := parent_ordinary_lower i j
  have hd := parent_defect_credit_actual_lower hδ hδhi hbank i j
  have heq : sourceSavedRectangle sourceSf sourceLogI
      (tLower i.val) (tUpper i.val) (uLower j.val) (uUpper j.val) =
      rawOrdinaryParent i.val j.val + max 0 (parentDefectValue i j).lo := by
    rfl
  rw [heq]
  have hadd : decodeQ80 (rawOrdinaryParent i.val j.val +
      max 0 (parentDefectValue i j).lo) =
      decodeQ80 (rawOrdinaryParent i.val j.val) +
        decodeQ80 (max 0 (parentDefectValue i j).lo) := by
    unfold decodeQ80
    push_cast
    ring
  rw [hadd]
  exact add_le_add ho hd

end

end ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly
