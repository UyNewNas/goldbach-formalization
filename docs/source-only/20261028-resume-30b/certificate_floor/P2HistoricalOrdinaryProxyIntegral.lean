import ImbalancedChen.P2HistoricalSavedFloorSelectedUnion

/-!
# The independent ordinary floor proxy on the same selected pair mask

SOURCE ONLY, uncompiled.  The imported selected-union module is the frozen
first-batch candidate, not an installed/verified dependency.  See REGISTRY.

The manuscript's exact endpoint constant and chord are upper proxies for
historical lower estimators.  Their comparison with the true ordinary
integral goes in the other direction: each is a genuine lower integral
alternative.  This file proves that direction on every original Row,
including a zero proxy for a rectangle crossing below two.  It proves the
two coefficient moments nonnegative and hence permits replacing historical
endpoint lows by exact endpoint values.  It does not assume a proxy bound,
run a historical checker, or infer an upper bound for the true Y6 count.
-/

namespace ImbalancedChen.P2HistoricalOrdinaryProxyIntegral

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2SavedFloorSemantics P2SavedFloorSubdivisionEstimator
open P2HistoricQ80OrdinaryEstimatorSoundness P2HistoricDefectIntegralMeasurability
open P2HistoricalSavedFloorRowsBinder P2HistoricalSavedFloorFullBinder
open P2HistoricalSavedFloorSelectedUnion
open OriginalU2CoupledRecurrenceSourceOnly

def rowResidualLo (r : Row) : ℝ := ordinaryResidual (rowTR r) (rowUR r)
def rowResidualHi (r : Row) : ℝ := ordinaryResidual (rowTL r) (rowUL r)
def rowMass (r : Row) : ℝ := realMass (rowTL r) (rowTR r) (rowUL r) (rowUR r)

/-- Exactly M_{R,B} in the independent proxy formula. -/
def rowResidualMoment (r : Row) : ℝ :=
  (57 / 64) * rowMass r - (5 / 2) * ((rowTR r : ℝ) - rowTL r) *
    Real.log ((rowUR r : ℝ) / rowUL r) -
    ((rowUR r : ℝ) - rowUL r) * Real.log ((rowTR r : ℝ) / rowTL r)

def logFactor (s : ℝ) : ℝ := Real.log (s - 1) / s
def rowFL (r : Row) : ℝ := logFactor (rowResidualLo r / ordinaryA)
def rowFH (r : Row) : ℝ := logFactor (rowResidualHi r / ordinaryA)

/-- Both proxies are already in Chen-quarter units. -/
def rowConstantProxy (r : Row) : ℝ := rowFL r * rowMass r / ordinaryA
def rowChordProxy (r : Row) : ℝ :=
  (rowFL r * (rowResidualHi r * rowMass r - rowResidualMoment r) +
    rowFH r * (rowResidualMoment r - rowResidualLo r * rowMass r)) /
      (ordinaryA * (rowResidualHi r - rowResidualLo r))

/-- The manuscript gives zero saved ordinary alternatives when the exact
lower query is below two.  This definition records that proxy convention;
it is not a claim that the real density vanishes in a crossing cell. -/
def rowOrdinaryProxy (r : Row) : ℝ :=
  if 2 * ordinaryA ≤ rowResidualLo r then
    max (rowConstantProxy r) (rowChordProxy r) else 0

def selectedOrdinaryProxy : ℝ := ∑ r : Row, rowOrdinaryProxy r
def selectedOrdinaryIntegral : ℝ :=
  ∫ p in selectedPairRegion, ordinaryPairKernel p.1 p.2

private theorem row_geometry_real (r : Row) :
    (0 : ℝ) < (rowTL r : ℝ) ∧ (0 : ℝ) < (rowUL r : ℝ) ∧
      (rowTL r : ℝ) < (rowTR r : ℝ) ∧ (rowUL r : ℝ) < (rowUR r : ℝ) := by
  rcases row_geometry r with ⟨htl, hul, _ht, _hu, _hmu⟩
  obtain ⟨_haZ, _hzul, huu, _hurh, _hhtl, htu, _htrd, _hcut⟩ := row_endpoint_bounds r
  exact ⟨htl, hul, by exact_mod_cast htu, by exact_mod_cast huu⟩

theorem row_residual_span (r : Row) : rowResidualLo r < rowResidualHi r := by
  rcases row_geometry_real r with ⟨_htl, _hul, ht, hu⟩
  dsimp [rowResidualLo, rowResidualHi, ordinaryResidual]
  linarith

theorem row_residual_range (r : Row) {t u : ℝ}
    (ht : t ∈ Icc (rowTL r : ℝ) (rowTR r : ℝ))
    (hu : u ∈ Icc (rowUL r : ℝ) (rowUR r : ℝ)) :
    ordinaryResidual t u ∈ Icc (rowResidualLo r) (rowResidualHi r) :=
  ⟨ordinaryResidual_antitone ht.2 hu.2, ordinaryResidual_antitone ht.1 hu.1⟩

/-- The whole parent grid already lies in the genuine initial log strip.
This bound is weaker than the selected positive-cell 9/4 bound, but suffices
to identify the exact endpoint formula, whose valid domain reaches four. -/
theorem row_residual_query_le_four (r : Row) : rowResidualHi r / ordinaryA ≤ 4 := by
  obtain ⟨hi, _hjpos, hj⟩ := indices_bounds r
  let i : Fin 512 := ⟨(indices r).1, hi⟩
  let j : Fin 512 := ⟨(indices r).2, hj⟩
  rcases parent_geometry i j with ⟨_htl, _hul, ht, hu, _hmu⟩
  have hr := (actual_savedParent_residual_bounds i j
    (parentTL i) ⟨le_rfl, ht⟩ (parentUL j) ⟨le_rfl, hu⟩).2
  have hupper : parentResidualUpper / ordinaryA ≤ 4 := by
    norm_num [parentResidualUpper, ordinaryResidual, ordinaryA]
  apply (div_le_div_of_nonneg_right ?_ ordinaryA_pos.le).trans hupper
  simpa only [rowResidualHi, parentTL, parentUL, rowTL, rowUL, i, j] using hr

theorem actual_factor_eq_logFactor {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 4) :
    actualExtendedThirdLowerFactor s = logFactor s := by
  exact (lower_eq_actual hs).symm.trans
    (by simpa only [logFactor] using lower_eq_log hs hs4)

theorem row_exact_endpoint_values (r : Row)
    (hpos : 2 * ordinaryA ≤ rowResidualLo r) :
    rowFL r = actualExtendedThirdLowerFactor (rowResidualLo r / ordinaryA) ∧
      rowFH r = actualExtendedThirdLowerFactor (rowResidualHi r / ordinaryA) := by
  have hl2 := (le_div_iff₀ ordinaryA_pos).mpr hpos
  have hle := div_le_div_of_nonneg_right (row_residual_span r).le ordinaryA_pos.le
  exact ⟨(actual_factor_eq_logFactor hl2 (hle.trans (row_residual_query_le_four r))).symm,
    (actual_factor_eq_logFactor (hl2.trans hle) (row_residual_query_le_four r)).symm⟩

theorem row_realMoment_eq (r : Row) :
    realMoment ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r) =
      rowResidualMoment r := by
  norm_num [realMoment, ordinaryPlane₁, rowResidualMoment, rowMass] <;> ring

/-- The exact moments are actual weighted integrals, not decimal tokens. -/
theorem row_residual_moment_integral (r : Row) :
    weightedIntegral ordinaryResidual (rowTL r) (rowTR r) (rowUL r) (rowUR r) =
      rowResidualMoment r := by
  rcases row_geometry_real r with ⟨htl, hul, ht, hu⟩
  have he : ordinaryResidual = fun t u : ℝ => (57 / 64) + (-5 / 2) * t + (-1) * u := by
    funext t u
    unfold ordinaryResidual
    ring
  rw [he, weightedIntegral_affine _ _ _ htl hul ht.le hu.le]
  unfold rowResidualMoment rowMass
  ring

/-- Both coefficient integrals in the manuscript chord are nonnegative.
This is proved by integrating R_B-R and R-r_B against the real 1/(tu)
weight, using the actual closed-cell residual enclosure. -/
theorem row_chord_coefficients_nonneg (r : Row) :
    0 ≤ rowResidualHi r * rowMass r - rowResidualMoment r ∧
      0 ≤ rowResidualMoment r - rowResidualLo r * rowMass r := by
  rcases row_geometry_real r with ⟨htl, hul, ht, hu⟩
  have hnonneg (f : ℝ → ℝ → ℝ)
      (hf : ∀ t ∈ Icc (rowTL r : ℝ) (rowTR r : ℝ),
        ∀ u ∈ Icc (rowUL r : ℝ) (rowUR r : ℝ), 0 ≤ f t u) :
      0 ≤ weightedIntegral f (rowTL r) (rowTR r) (rowUL r) (rowUR r) := by
    apply intervalIntegral.integral_nonneg ht.le
    intro t ht'
    apply intervalIntegral.integral_nonneg hu.le
    intro u hu'
    exact div_nonneg (hf t ht' u hu')
      (mul_pos (htl.trans_le ht'.1) (hul.trans_le hu'.1)).le
  constructor
  · have hn := hnonneg (fun t u => rowResidualHi r - ordinaryResidual t u)
      (fun t ht' u hu' => sub_nonneg.mpr (row_residual_range r ht' hu').2)
    have he : (fun t u : ℝ => rowResidualHi r - ordinaryResidual t u) =
        fun t u => (rowResidualHi r - 57 / 64) + (5 / 2) * t + (1 : ℝ) * u := by
      funext t u
      unfold ordinaryResidual
      ring
    rw [he, weightedIntegral_affine _ _ _ htl hul ht.le hu.le] at hn
    convert hn using 1 <;> dsimp [rowResidualMoment, rowMass] <;> ring
  · have hn := hnonneg (fun t u => ordinaryResidual t u - rowResidualLo r)
      (fun t ht' u hu' => sub_nonneg.mpr (row_residual_range r ht' hu').1)
    have he : (fun t u : ℝ => ordinaryResidual t u - rowResidualLo r) =
        fun t u => (57 / 64 - rowResidualLo r) + (-5 / 2) * t + (-1) * u := by
      funext t u
      unfold ordinaryResidual
      ring
    rw [he, weightedIntegral_affine _ _ _ htl hul ht.le hu.le] at hn
    convert hn using 1 <;> dsimp [rowResidualMoment, rowMass] <;> ring

/-- This is the precise endpoint-upward comparison needed by the historical
chord: increasing its two endpoint lows increases the exact coefficient
expression, because the two genuine coefficient integrals are nonnegative. -/
theorem row_chord_endpoint_lows_le_proxy (r : Row) {fl fh : ℝ}
    (hfl : fl ≤ rowFL r) (hfh : fh ≤ rowFH r) :
    (fl * (rowResidualHi r * rowMass r - rowResidualMoment r) +
      fh * (rowResidualMoment r - rowResidualLo r * rowMass r)) /
        (ordinaryA * (rowResidualHi r - rowResidualLo r)) ≤ rowChordProxy r := by
  rcases row_chord_coefficients_nonneg r with ⟨hleft, hright⟩
  exact div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_right hfl hleft)
      (mul_le_mul_of_nonneg_right hfh hright))
    (mul_pos ordinaryA_pos (sub_pos.mpr (row_residual_span r))).le

theorem rowConstantProxy_le_actual (r : Row)
    (hpos : 2 * ordinaryA ≤ rowResidualLo r) :
    rowConstantProxy r ≤ rowActualOrdinaryIntegral r / 4 := by
  rcases row_geometry_real r with ⟨htl, hul, ht, hu⟩
  have hv := (row_exact_endpoint_values r hpos).1
  have hb := ordinary_base_real_sound htl hul ht.le hu.le
    (le_rfl : rowResidualLo r ≤ ordinaryResidual (rowTR r) (rowUR r)) hv.le
  change 4 * rowFL r * rowMass r / ordinaryA ≤ rowActualOrdinaryIntegral r at hb
  have he : 4 * rowConstantProxy r = 4 * rowFL r * rowMass r / ordinaryA := by
    unfold rowConstantProxy
    ring
  rw [← he] at hb
  linarith

theorem rowChordProxy_le_actual (r : Row)
    (hpos : 2 * ordinaryA ≤ rowResidualLo r) :
    rowChordProxy r ≤ rowActualOrdinaryIntegral r / 4 := by
  rcases row_geometry_real r with ⟨htl, hul, ht, hu⟩
  rcases row_exact_endpoint_values r hpos with ⟨hfl, hfh⟩
  have hc := ordinary_chord_real_sound ordinaryPlane₁ htl hul ht.le hu.le
    hpos (row_residual_span r)
    (fun t ht' u hu' => by
      simpa only [ordinaryPlane₁_real] using row_residual_range r ht' hu')
    (fun t _ht u _hu => (ordinaryPlane₁_real t u).le) hfl.le hfh.le
  rw [row_realMoment_eq r] at hc
  change (4 / ordinaryA) *
      ((rowFL r * (rowResidualHi r * rowMass r - rowResidualMoment r) +
        rowFH r * (rowResidualMoment r - rowResidualLo r * rowMass r)) /
          (rowResidualHi r - rowResidualLo r)) ≤ rowActualOrdinaryIntegral r at hc
  have he : 4 * rowChordProxy r = (4 / ordinaryA) *
      ((rowFL r * (rowResidualHi r * rowMass r - rowResidualMoment r) +
        rowFH r * (rowResidualMoment r - rowResidualLo r * rowMass r)) /
          (rowResidualHi r - rowResidualLo r)) := by
    unfold rowChordProxy
    field_simp [ordinaryA_pos.ne', (sub_pos.mpr (row_residual_span r)).ne']
    <;> ring
  rw [← he] at hc
  linarith

/-- The zero crossing proxy is compared using actual density nonnegativity,
not by declaring the whole crossing-cell ordinary integral zero. -/
theorem rowOrdinaryProxy_le_actual (r : Row) :
    rowOrdinaryProxy r ≤ rowActualOrdinaryIntegral r / 4 := by
  unfold rowOrdinaryProxy
  split_ifs with hpos
  · exact max_le (rowConstantProxy_le_actual r hpos) (rowChordProxy_le_actual r hpos)
  · rcases row_geometry_real r with ⟨htl, hul, ht, hu⟩
    exact div_nonneg (ordinary_integral_nonneg htl hul ht.le hu.le) (by norm_num)

theorem selectedOrdinaryIntegral_eq_row_sum :
    selectedOrdinaryIntegral = ∑ r : Row, rowActualOrdinaryIntegral r := by
  unfold selectedOrdinaryIntegral selectedPairRegion
  rw [integral_iUnion_fintype pairCell_measurable pairCells_pairwise_disjoint
    ordinary_integrableOn_pairCell]
  apply Finset.sum_congr rfl
  intro r _hr
  exact pairCell_setIntegral_eq_nested r _ (ordinary_integrableOn_pairCell r)

theorem selectedOrdinaryProxy_le_actual_integral :
    selectedOrdinaryProxy ≤ selectedOrdinaryIntegral / 4 := by
  rw [selectedOrdinaryIntegral_eq_row_sum]
  unfold selectedOrdinaryProxy
  calc
    (∑ r : Row, rowOrdinaryProxy r) ≤ ∑ r : Row, rowActualOrdinaryIntegral r / 4 :=
      Finset.sum_le_sum (fun r _hr => rowOrdinaryProxy_le_actual r)
    _ = (∑ r : Row, rowActualOrdinaryIntegral r) / 4 := by rw [Finset.sum_div]

theorem row_guardedDefectIntegral_nonneg {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (r : Row) :
    0 ≤ guardedDefectIntegral δ (rowTL r) (rowTR r) (rowUL r) (rowUR r) := by
  obtain ⟨hi, _hjpos, hj⟩ := indices_bounds r
  let i : Fin 512 := ⟨(indices r).1, hi⟩
  let j : Fin 512 := ⟨(indices r).2, hj⟩
  rcases parent_geometry i j with ⟨htl, hul, ht, hu, _hmu⟩
  have hn := guarded_defect_integral_nonneg hδ hδhi htl hul parentResidualLower_pos ht hu
    (actual_savedParent_residual_bounds i j) parentResidualUpper_guard
  simpa only [parentTL, parentTR, parentUL, parentUR, rowTL, rowTR, rowUL, rowUR, i, j]
    using hn

/-- Same selected region, actual ordinary density plus actual guarded h.
No bank endpoint licence is needed to prove nonnegativity of the actual h. -/
theorem selectedOrdinaryIntegral_le_complete_union {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    selectedOrdinaryIntegral ≤ selectedUnionIntegral δ := by
  rw [selectedOrdinaryIntegral_eq_row_sum,
    selectedUnionIntegral_eq_fullCompleteActualIntegral hδ hδhi]
  unfold fullCompleteActualIntegral rowCompleteActualIntegral
  exact Finset.sum_le_sum (fun r _hr =>
    le_add_of_nonneg_right (row_guardedDefectIntegral_nonneg hδ hδhi r))

theorem selectedOrdinaryProxy_le_complete_union {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    selectedOrdinaryProxy ≤ selectedUnionIntegral δ / 4 :=
  selectedOrdinaryProxy_le_actual_integral.trans
    (div_le_div_of_nonneg_right (selectedOrdinaryIntegral_le_complete_union hδ hδhi)
      (by norm_num))

end

end ImbalancedChen.P2HistoricalOrdinaryProxyIntegral
