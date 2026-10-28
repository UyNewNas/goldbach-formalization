import ImbalancedChen.P2HistoricalSavedFloorFullBinder
import ImbalancedChen.Certificates.PairedV2GlobalGeometry
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The literal saved mask as a genuine two-dimensional integral

SOURCE ONLY; not compiled or evaluated.  The intended installation is
`ImbalancedChen/P2HistoricalSavedFloorSelectedUnion.lean`.

The full row binder already proves ordinary-plus-guarded-actual-Wu-h
semantics for each frozen Q80 numerator.  This file supplies the next
geometric/analytic step: the sum of those 17572 iterated rectangle
integrals is the Lebesgue integral of the same complete density over
their actual, disjoint, half-open pair mask.  No integrability premise or
integral inequality is supplied by the caller.  Neither the stored-total
check nor the source-output checks are executed here.

The endpoint bank licences and the eventual identification of this
guarded Wu-h density with an arithmetic enhanced family remain separate.
In particular the complete saved numerator is not asserted to be a lower
bound for the ordinary-only density.
-/

namespace ImbalancedChen.P2HistoricalSavedFloorSelectedUnion

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2SavedFloorSemantics P2HistoricalSavedFloorRowsBinder
open P2HistoricDefectIntegralMeasurability P2HistoricalSavedFloorFullBinder
open P2SavedFloorSubdivisionEstimator

/-- Same two grid indices as the frozen row, with unique half-open ownership. -/
def pairCell (r : Row) : Set (ℝ × ℝ) :=
  Ioc (rowTL r : ℝ) (rowTR r : ℝ) ×ˢ Ioc (rowUL r : ℝ) (rowUR r : ℝ)

def selectedPairRegion : Set (ℝ × ℝ) := ⋃ r : Row, pairCell r

/-- Complete density used by the historical lower estimator, before /4. -/
def completeKernel (δ : ℝ) (p : ℝ × ℝ) : ℝ :=
  ordinaryPairKernel p.1 p.2 + guardedDefectKernel δ p.1 p.2

def selectedUnionIntegral (δ : ℝ) : ℝ :=
  ∫ p in selectedPairRegion, completeKernel δ p

theorem pairCell_measurable (r : Row) : MeasurableSet (pairCell r) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem selectedPairRegion_measurable : MeasurableSet selectedPairRegion :=
  MeasurableSet.iUnion pairCell_measurable

/-- Ownership is proved for the actual 512-grid keys, not a row ordinal. -/
theorem pairCell_unique_owner {r q : Row} {p : ℝ × ℝ}
    (hr : p ∈ pairCell r) (hq : p ∈ pairCell q) : r = q := by
  have hti : (indices r).1 = (indices q).1 := by
    rcases lt_trichotomy (indices r).1 (indices q).1 with hlt | heq | hgt
    · have hsep : (rowTR r : ℝ) ≤ (rowTL q : ℝ) := by
        exact_mod_cast tUpper_le_tLower hlt
      exact False.elim (not_lt_of_ge (hr.1.2.trans hsep) hq.1.1)
    · exact heq
    · have hsep : (rowTR q : ℝ) ≤ (rowTL r : ℝ) := by
        exact_mod_cast tUpper_le_tLower hgt
      exact False.elim (not_lt_of_ge (hq.1.2.trans hsep) hr.1.1)
  have hui : (indices r).2 = (indices q).2 := by
    rcases lt_trichotomy (indices r).2 (indices q).2 with hlt | heq | hgt
    · have hsep : (rowUR r : ℝ) ≤ (rowUL q : ℝ) := by
        exact_mod_cast uUpper_le_uLower hlt
      exact False.elim (not_lt_of_ge (hr.2.2.trans hsep) hq.2.1)
    · exact heq
    · have hsep : (rowUR q : ℝ) ≤ (rowUL r : ℝ) := by
        exact_mod_cast uUpper_le_uLower hgt
      exact False.elim (not_lt_of_ge (hq.2.2.trans hsep) hr.2.1)
  exact indices_injective (Prod.ext hti hui)

theorem pairCells_pairwise_disjoint :
    Pairwise (fun r q => Disjoint (pairCell r) (pairCell q)) := by
  intro r q hrq
  apply Set.disjoint_left.mpr
  intro p hr hq
  exact hrq (pairCell_unique_owner hr hq)

private theorem row_real_geometry (r : Row) :
    (0 : ℝ) < (rowTL r : ℝ) ∧ (0 : ℝ) < (rowUL r : ℝ) ∧
      (rowTL r : ℝ) ≤ (rowTR r : ℝ) ∧ (rowUL r : ℝ) ≤ (rowUR r : ℝ) := by
  rcases row_geometry r with ⟨htl, hul, ht, hu, _hmu⟩
  exact ⟨htl, hul, by exact_mod_cast ht, by exact_mod_cast hu⟩

/-- The ordinary density is jointly integrable, including its s=2 branch. -/
theorem ordinary_integrableOn_pairCell (r : Row) :
    IntegrableOn (fun p : ℝ × ℝ => ordinaryPairKernel p.1 p.2) (pairCell r) := by
  rcases row_real_geometry r with ⟨htl, hul, _ht, _hu⟩
  let B : Set (ℝ × ℝ) :=
    Icc (rowTL r : ℝ) (rowTR r : ℝ) ×ˢ Icc (rowUL r : ℝ) (rowUR r : ℝ)
  have hr : Continuous (fun p : ℝ × ℝ =>
      ordinaryResidual p.1 p.2 / ordinaryA) := by
    unfold ordinaryResidual
    fun_prop
  have hn : Continuous (fun p : ℝ × ℝ =>
      4 * actualExtendedThirdLowerFactor (ordinaryResidual p.1 p.2 / ordinaryA)) :=
    continuous_const.mul (continuous_actualExtendedThirdLowerFactor.comp hr)
  have hc : ContinuousOn (fun p : ℝ × ℝ => ordinaryPairKernel p.1 p.2) B := by
    apply hn.continuousOn.div (by fun_prop)
    intro p hp
    exact (mul_pos (mul_pos ordinaryA_pos (htl.trans_le hp.1.1))
      (hul.trans_le hp.2.1)).ne'
  apply (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩

/-- The actual parent bounds discharge every residual and denominator
licence; the crossing branch is the guarded source kernel itself. -/
theorem defect_integrableOn_pairCell {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (r : Row) :
    IntegrableOn (fun p : ℝ × ℝ => guardedDefectKernel δ p.1 p.2) (pairCell r) := by
  obtain ⟨hi, _hjpos, hj⟩ := indices_bounds r
  let i : Fin 512 := ⟨(indices r).1, hi⟩
  let j : Fin 512 := ⟨(indices r).2, hj⟩
  rcases parent_geometry i j with ⟨htl, hul, _ht, _hu, _hmu⟩
  have hint := guardedDefect_joint_integrable hδ hδhi htl hul
    parentResidualLower_pos (actual_savedParent_residual_bounds i j)
    parentResidualUpper_guard
  rw [Measure.prod_restrict] at hint
  simpa only [IntegrableOn, pairCell, Measure.volume_eq_prod,
    parentTL, parentTR, parentUL, parentUR, rowTL, rowTR, rowUL, rowUR, i, j] using hint

theorem complete_integrableOn_pairCell {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (r : Row) :
    IntegrableOn (completeKernel δ) (pairCell r) :=
  (ordinary_integrableOn_pairCell r).add (defect_integrableOn_pairCell hδ hδhi r)

/-- Fubini uses actual joint integrability on this same half-open cell.
The ordered interval-integral convention introduces no sign or factor. -/
theorem pairCell_setIntegral_eq_nested (r : Row) (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (pairCell r)) :
    (∫ p in pairCell r, F p) =
      ∫ t in (rowTL r : ℝ)..(rowTR r : ℝ),
        ∫ u in (rowUL r : ℝ)..(rowUR r : ℝ), F (t, u) := by
  rcases row_real_geometry r with ⟨_htl, _hul, ht, hu⟩
  have hfubini : (∫ p in pairCell r, F p) =
      ∫ t in Ioc (rowTL r : ℝ) (rowTR r : ℝ),
        ∫ u in Ioc (rowUL r : ℝ) (rowUR r : ℝ), F (t, u) := by
    rw [pairCell, Measure.volume_eq_prod]
    exact setIntegral_prod _ (by
      simpa only [pairCell, Measure.volume_eq_prod] using hF)
  simpa only [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hu]
    using hfubini

/-- The existing ordinary/defect decomposition equals one product-space
integral; a total-integer identity has no role in this theorem. -/
theorem rowCompleteActualIntegral_eq_pairCellIntegral {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (r : Row) :
    rowCompleteActualIntegral δ r = ∫ p in pairCell r, completeKernel δ p := by
  rw [completeKernel, integral_add (ordinary_integrableOn_pairCell r)
    (defect_integrableOn_pairCell hδ hδhi r)]
  rw [pairCell_setIntegral_eq_nested r _ (ordinary_integrableOn_pairCell r),
    pairCell_setIntegral_eq_nested r _ (defect_integrableOn_pairCell hδ hδhi r)]
  rfl

/-- No row is counted twice, including adjacent 512-grid boundary rows. -/
theorem selectedUnionIntegral_eq_fullCompleteActualIntegral {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    selectedUnionIntegral δ = fullCompleteActualIntegral δ := by
  unfold selectedUnionIntegral selectedPairRegion fullCompleteActualIntegral
  rw [integral_iUnion_fintype pairCell_measurable pairCells_pairwise_disjoint
    (complete_integrableOn_pairCell hδ hδhi)]
  apply Finset.sum_congr rfl
  intro r _hr
  exact (rowCompleteActualIntegral_eq_pairCellIntegral hδ hδhi r).symm

/-- Literal complete saved floors bound the genuine selected-mask integral
once both exact finite checks and the actual bank licences are supplied. -/
theorem checked_saved_total_le_selectedUnionIntegral {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) (hsum : storedTotalCheck = true) :
    decodeQ80 sourceSavedFloorTotal ≤ selectedUnionIntegral δ := by
  rw [selectedUnionIntegral_eq_fullCompleteActualIntegral hδ hδhi]
  exact checked_full_saved_total_actual_lower hδ hδhi hbank hc hsum

theorem checked_saved_total_quarter_le_selectedUnionIntegral {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) (hsum : storedTotalCheck = true) :
    decodeQ80 sourceSavedFloorTotal / 4 ≤ selectedUnionIntegral δ / 4 := by
  exact div_le_div_of_nonneg_right
    (checked_saved_total_le_selectedUnionIntegral hδ hδhi hbank hc hsum) (by norm_num)

end

end ImbalancedChen.P2HistoricalSavedFloorSelectedUnion
