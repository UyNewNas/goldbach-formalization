import ImbalancedChen.P2HistoricalSavedFloorRowsBinder
import ImbalancedChen.P2HistoricSieveStateInduction
import ImbalancedChen.P2HistoricLogCallerGuards
import ImbalancedChen.P2HistoricSavedOrdinaryDefectAssembly
import ImbalancedChen.P2HistoricParentSavedRectangleActualLower

/-!
# All frozen saved rows: complete ordinary-plus-actual-Wu-h semantics

SOURCE ONLY, uncompiled.  All four bare imports name the owned sibling
source candidates and their declared future dependencies; no installed
module or compiled supplier is claimed by this file.

The original saved fields and source-ordinal/grid-index dictionary are
reused verbatim from P2HistoricalSavedFloorRowsBinder.  The actual engine
is the literal historical SieveTable(16384,8); the actual log backend is
the recovered Q80 log_point/log(I80) algorithm.  Their semantic theorems,
and the actual parent-grid chord guards, are applied below, rather than
passed as arbitrary caller licences.

The output bound is the COMPLETE original pair_cell(False,False) output:
ordinary max-of-proofs PLUS its positive defect credit.  Its real target
is the actual ordinary integral PLUS the guarded actual Wu-h defect
integral at R/a with denominator R*t*u.  No zero-defect check is needed.
The actual 200-bank endpoint licences and delta domain remain explicit;
none is a saved-output bound, aggregate loss bound or final gain premise.

Neither the output equality checks nor the total integer check are run in
this source-only task.  Parent ownership and identification of the actual
Wu source family with the manuscript enhanced family remain separate.
-/

namespace ImbalancedChen.P2HistoricalSavedFloorFullBinder

noncomputable section

open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2HistoricalSavedFloorRowsBinder
open P2HistoricDefectIntegralMeasurability

/-- Exactly `author.Ordinary(16384).f`, whose maximum is eight. -/
def actualSf : ℚ → I80 := P2HistoricSieveTableSemantics.sf 16384 8

/-- Exactly the historical Q80 `log(I(q))` wrapper. -/
def actualLog : ℚ → I80 := Certificates.P2HistoricLogPointInterpreter.logI

/-- Full-output equality with the original stored numerator and grid keys. -/
def fullSourceRowCheck (r : Row) : Bool := sourceOutputCheck actualSf actualLog r

theorem actualSf_contract (q : ℚ) :
    (actualSf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)) :=
  P2HistoricSieveStateInduction.sf_contains_actual q

theorem actualLog_row_contract (r : Row) :
    (actualLog (rowLogQueries r).1).Contains
        (Real.log (((rowLogQueries r).1 : ℚ) : ℝ)) ∧
      (actualLog (rowLogQueries r).2).Contains
        (Real.log (((rowLogQueries r).2 : ℚ) : ℝ)) := by
  exact Certificates.P2HistoricLogCallerGuards.grid_log_contract
    (indices r).1 (indices r).2

/-- Both primitive eligible-chord divisors are closed by actual 512-grid
widths, without evaluating a stored-output equality. -/
theorem actual_chordDivisorCheck (r : Row) : chordDivisorCheck r = true := by
  have hg := P2HistoricChordDivisorGuard.parent_chord_divisors_positive
    (indices r).1 (indices r).2
  apply decide_eq_true
  exact ⟨fun _hc => hg.1, fun _hc => hg.2⟩

theorem actual_ordinary_component_lower (r : Row) :
    decodeQ80 (rowOrdinaryOutput actualSf actualLog r) ≤ rowActualOrdinaryIntegral r := by
  exact Certificates.P2HistoricLogCallerGuards.adopted_savedOrdinaryRectangle_actual_lower_logClosed
    actualSf r actualSf_contract

/-- The complete mathematical lower-estimator target for one stored row. -/
def rowCompleteActualIntegral (δ : ℝ) (r : Row) : ℝ :=
  rowActualOrdinaryIntegral r +
    guardedDefectIntegral δ (rowTL r) (rowTR r) (rowUL r) (rowUR r)

def fullCompleteActualIntegral (δ : ℝ) : ℝ :=
  ∑ r : Row, rowCompleteActualIntegral δ r

/-- The original source metadata and the complete integer output are
bound to the same adopted row by one decidable check. -/
theorem fullSourceRowCheck_sound (r : Row) (hc : fullSourceRowCheck r = true) :
    (frozenSavedRow r).tIndex = (indices r).1 ∧
      (frozenSavedRow r).uIndex = (indices r).2 ∧
      (frozenSavedRow r).savedQ80 = rowSourceOutput actualSf actualLog r := by
  exact sourceOutputCheck_sound actualSf actualLog r hc

theorem fullCompleteActualIntegral_eq_components (δ : ℝ) :
    fullCompleteActualIntegral δ = (∑ r : Row, rowActualOrdinaryIntegral r) +
      ∑ r : Row, guardedDefectIntegral δ (rowTL r) (rowTR r) (rowUL r) (rowUR r) := by
  simp only [fullCompleteActualIntegral, rowCompleteActualIntegral, Finset.sum_add_distrib]

/-- The entire original stored integer stream uses both positive parts;
this identity does not use a zero-defect hypothesis. -/
theorem checked_full_source_integer_components (hc : ∀ r : Row, fullSourceRowCheck r = true) :
    (∑ r : Row, (frozenSavedRow r).savedQ80) =
      (∑ r : Row, rowOrdinaryOutput actualSf actualLog r) +
        ∑ r : Row, rowDefectCredit actualLog r := by
  exact fullMask_checked_source_sum_identity actualSf actualLog hc

/-- The complete engine output has genuine ordinary-plus-actual-Wu-h
integral meaning.  Every sf/log/divisor/geometric prerequisite is supplied
by the imported actual-parent theorem; only actual bank endpoint licences
and the source delta domain remain as analytic inputs. -/
theorem rowSourceOutput_complete_actual_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ) (r : Row) :
    decodeQ80 (rowSourceOutput actualSf actualLog r) ≤ rowCompleteActualIntegral δ r := by
  obtain ⟨hi, _hjpos, hj⟩ := indices_bounds r
  exact P2HistoricSavedOrdinaryDefectAssembly.parent_sourceSavedRectangle_actual_lower
    hδ hδhi hbank ⟨(indices r).1, hi⟩ ⟨(indices r).2, hj⟩

/-- Exact same-row historical binder for the COMPLETE stored numerator.
No defect credit is removed, and no analytic saved-floor bound is assumed.
The check asserts equality of finite integers and source grid keys only. -/
theorem checked_full_saved_row_actual_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (r : Row) (hc : fullSourceRowCheck r = true) :
    decodeQ80 (frozenSavedRow r).savedQ80 ≤ rowCompleteActualIntegral δ r := by
  rw [(fullSourceRowCheck_sound r hc).2.2]
  exact rowSourceOutput_complete_actual_lower hδ hδhi hbank r

/-- All 17572 adopted rows use their original full stored fields and the
same concrete historical Q80 engine.  The sole finite-output premise is
the exact decidable check stream, not the desired real lower inequality. -/
theorem fullMask_checked_full_saved_rows_actual_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80) ≤ fullCompleteActualIntegral δ := by
  exact Finset.sum_le_sum (fun r _hr => checked_full_saved_row_actual_lower
    hδ hδhi hbank r (hc r))

/-- The frozen aggregate token acquires its actual integral semantics only
after the separate integer sum check and complete source-output checks. -/
theorem checked_full_saved_total_actual_lower {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) (hsum : storedTotalCheck = true) :
    decodeQ80 sourceSavedFloorTotal ≤ fullCompleteActualIntegral δ := by
  rw [← checked_stored_total_decode hsum]
  exact fullMask_checked_full_saved_rows_actual_lower hδ hδhi hbank hc

/-- The same literal complete saved-total lower estimate in Chen-quarter
units, with exactly one division by four and the original Q80 scale. -/
theorem checked_full_saved_total_quarter_units {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) (hsum : storedTotalCheck = true) :
    decodeQ80 sourceSavedFloorTotal / 4 ≤ fullCompleteActualIntegral δ / 4 := by
  exact div_le_div_of_nonneg_right
    (checked_full_saved_total_actual_lower hδ hδhi hbank hc hsum) (by norm_num)

theorem checked_full_saved_estimator_pos {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hbank : P2HistoricSavedOrdinaryDefectAssembly.BankEndpointLicences δ)
    (hc : ∀ r : Row, fullSourceRowCheck r = true) (hsum : storedTotalCheck = true) :
    0 < fullCompleteActualIntegral δ := by
  have hp : 0 < decodeQ80 sourceSavedFloorTotal := by
    norm_num [decodeQ80, sourceSavedFloorTotal, Q]
  exact hp.trans_le (checked_full_saved_total_actual_lower hδ hδhi hbank hc hsum)

end

end ImbalancedChen.P2HistoricalSavedFloorFullBinder
