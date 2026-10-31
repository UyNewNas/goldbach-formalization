import ImbalancedChen.P2HistoricalSavedFloorStoredTotalCheckCore
import ImbalancedChen.P2HistoricQ80OrdinaryEstimatorSoundness
import ImbalancedChen.Certificates.PairedV2FullMaskGeometry

namespace ImbalancedChen.P2HistoricalSavedFloorRowsBinder

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2SavedFloorSemantics P2HistoricQ80OrdinaryEstimatorSoundness

/-! SOURCE ONLY, uncompiled. Literal source-row integer fields only.
The original ordinal and both source indices are retained alongside the saved Q80 token.
The E0/E1 labels and parent ownership are supplied elsewhere by P1.
Source SHA256 f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7.
Rows were sorted by their existing t/u fields for FullMask.Row access; no estimator was run.
The original pair_cell(False,False) output INCLUDES a nonnegative defect term.
Consequently equality with its ordinary-only component is a separate exact check, never inferred.
The peer imports name source-only future modules P2HistoricQ80OrdinaryEstimatorSoundness
and its declared P2HistoricQ80DefectLookup/P2SavedFloorSemantics/P2TableActionSoundness dependencies.
Their primitive sf/log licences and positive-divisor checks remain explicit.
No floor-equals-output check, aggregate floor sum, backend licence or final gain is claimed passed. -/

/-- Separate ordinary-only exact check.  This is not substituted for the
original algorithm, whose defect can be strictly positive on E1 rows. -/
def ordinaryOnlyCheck (sf logI : ℚ → I80) (r : Row) : Bool :=
  decide ((frozenSavedRow r).tIndex = (indices r).1 ∧
    (frozenSavedRow r).uIndex = (indices r).2 ∧
    (frozenSavedRow r).savedQ80 = rowOrdinaryOutput sf logI r)

def zeroDefectCheck (logI : ℚ → I80) (r : Row) : Bool :=
  decide (rowDefectCredit logI r = 0)

def chordDivisorCheck (r : Row) : Bool :=
  decide ((rowChordEligible r ordinaryPlane₀ ordinaryPlane₁ →
    0 < (I80.point ((affineRange ordinaryPlane₀ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).2 -
      (affineRange ordinaryPlane₀ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).1)).lo) ∧
    (rowChordEligible r ordinaryPlane₁ ordinaryPlane₀ →
    0 < (I80.point ((affineRange ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).2 -
      (affineRange ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).1)).lo))

theorem sourceOutputCheck_sound (sf logI : ℚ → I80) (r : Row)
    (hc : sourceOutputCheck sf logI r = true) :
    (frozenSavedRow r).tIndex = (indices r).1 ∧
      (frozenSavedRow r).uIndex = (indices r).2 ∧
      (frozenSavedRow r).savedQ80 = rowSourceOutput sf logI r := by
  exact of_decide_eq_true hc

theorem source_and_zeroDefect_imply_ordinaryOnly (sf logI : ℚ → I80) (r : Row)
    (hc : sourceOutputCheck sf logI r = true) (hz : zeroDefectCheck logI r = true) :
    ordinaryOnlyCheck sf logI r = true := by
  obtain ⟨hti, hui, hsaved⟩ := sourceOutputCheck_sound sf logI r hc
  have hzero : rowDefectCredit logI r = 0 := of_decide_eq_true hz
  apply decide_eq_true
  refine ⟨hti, hui, ?_⟩
  simpa only [rowSourceOutput_eq_components, hzero, add_zero] using hsaved

/-- The source geometry is supplied by the actual existing FullMask rows,
not by the stored saved numerator or a backend output. -/
theorem row_geometry (r : Row) :
    (0 : ℝ) < rowTL r ∧ (0 : ℝ) < rowUL r ∧
      rowTL r ≤ rowTR r ∧ rowUL r ≤ rowUR r ∧ (25 / 128 : ℚ) ≤ rowTL r := by
  obtain ⟨haZ, hzul, huu, _hurh, hhtl, htu, _htrd, _hcut⟩ := row_endpoint_bounds r
  have ha : (0 : ℚ) < Certificates.PairedV2.a := by norm_num [Certificates.PairedV2.a]
  have hh : (0 : ℚ) < Certificates.PairedV2.h := by norm_num [Certificates.PairedV2.h]
  have ht0 : (0 : ℚ) < tLower (indices r).1 := hh.trans hhtl
  have hu0 : (0 : ℚ) < uLower (indices r).2 := ha.trans (haZ.trans_le hzul)
  refine ⟨by exact_mod_cast ht0, by exact_mod_cast hu0, htu.le, huu.le, ?_⟩
  have hi : (0 : ℚ) ≤ (indices r).1 := by exact_mod_cast (Nat.zero_le (indices r).1)
  dsimp [rowTL, tLower, mu, d]
  nlinarith

def decodeQ80 (n : ℤ) : ℝ := (((n : ℚ) / Q : ℚ) : ℝ)

def rowActualOrdinaryIntegral (r : Row) : ℝ :=
  ordinaryCellIntegral (rowTL r) (rowTR r) (rowUL r) (rowUR r)

/-- Calls the peer's actual historical estimator theorem.  The hypotheses
are primitive sf/log enclosures and a checked positive divisor; none is a
saved-floor lower bound.  The peer currently exposes a global sf licence;
the explicit rowSfQueries above records its actual finite query footprint. -/
theorem rowOrdinaryOutput_actual_lower (sf logI : ℚ → I80) (r : Row)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hlogT : (logI (rowLogQueries r).1).Contains (Real.log (((rowLogQueries r).1 : ℚ) : ℝ)))
    (hlogU : (logI (rowLogQueries r).2).Contains (Real.log (((rowLogQueries r).2 : ℚ) : ℝ)))
    (hdiv : chordDivisorCheck r = true) :
    decodeQ80 (rowOrdinaryOutput sf logI r) ≤ rowActualOrdinaryIntegral r := by
  obtain ⟨htl, hul, ht, hu, hhigh⟩ := row_geometry r
  have hguards :
      (rowChordEligible r ordinaryPlane₀ ordinaryPlane₁ →
        0 < (I80.point ((affineRange ordinaryPlane₀ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).2 -
          (affineRange ordinaryPlane₀ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).1)).lo) ∧
      (rowChordEligible r ordinaryPlane₁ ordinaryPlane₀ →
        0 < (I80.point ((affineRange ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).2 -
          (affineRange ordinaryPlane₁ (rowTL r) (rowTR r) (rowUL r) (rowUR r)).1)).lo) :=
    of_decide_eq_true hdiv
  exact savedOrdinaryRectangle_actual_lower sf logI (rowTL r) (rowTR r) (rowUL r) (rowUR r)
    htl hul ht hu hhigh hsf hlogT hlogU hguards.1 hguards.2

/-- An exact equality check, not a stored-floor analytic hypothesis,
binds the frozen ordinary-only numerator to that same row's real integral. -/
theorem checked_ordinary_floor_actual_lower (sf logI : ℚ → I80) (r : Row)
    (hc : ordinaryOnlyCheck sf logI r = true)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hlogT : (logI (rowLogQueries r).1).Contains (Real.log (((rowLogQueries r).1 : ℚ) : ℝ)))
    (hlogU : (logI (rowLogQueries r).2).Contains (Real.log (((rowLogQueries r).2 : ℚ) : ℝ)))
    (hdiv : chordDivisorCheck r = true) :
    decodeQ80 (frozenSavedRow r).savedQ80 ≤ rowActualOrdinaryIntegral r := by
  have hcheck : (frozenSavedRow r).tIndex = (indices r).1 ∧
      (frozenSavedRow r).uIndex = (indices r).2 ∧
      (frozenSavedRow r).savedQ80 = rowOrdinaryOutput sf logI r := of_decide_eq_true hc
  rw [hcheck.2.2]
  exact rowOrdinaryOutput_actual_lower sf logI r hsf hlogT hlogU hdiv

/-- The original output can always be decomposed honestly: remove its
explicit defect credit before invoking the ordinary-only integral theorem. -/
theorem checked_source_ordinary_component_actual_lower (sf logI : ℚ → I80) (r : Row)
    (hc : sourceOutputCheck sf logI r = true)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hlogT : (logI (rowLogQueries r).1).Contains (Real.log (((rowLogQueries r).1 : ℚ) : ℝ)))
    (hlogU : (logI (rowLogQueries r).2).Contains (Real.log (((rowLogQueries r).2 : ℚ) : ℝ)))
    (hdiv : chordDivisorCheck r = true) :
    decodeQ80 ((frozenSavedRow r).savedQ80 - rowDefectCredit logI r) ≤ rowActualOrdinaryIntegral r := by
  rw [(sourceOutputCheck_sound sf logI r hc).2.2, rowSourceOutput_eq_components,
    add_sub_cancel_right]
  exact rowOrdinaryOutput_actual_lower sf logI r hsf hlogT hlogU hdiv

/-- Source-output plus zero-defect integer checks suffice for a genuine
ordinary bound on the complete stored numerator. -/
theorem checked_source_zeroDefect_actual_lower (sf logI : ℚ → I80) (r : Row)
    (hc : sourceOutputCheck sf logI r = true) (hz : zeroDefectCheck logI r = true)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hlogT : (logI (rowLogQueries r).1).Contains (Real.log (((rowLogQueries r).1 : ℚ) : ℝ)))
    (hlogU : (logI (rowLogQueries r).2).Contains (Real.log (((rowLogQueries r).2 : ℚ) : ℝ)))
    (hdiv : chordDivisorCheck r = true) :
    decodeQ80 (frozenSavedRow r).savedQ80 ≤ rowActualOrdinaryIntegral r := by
  exact checked_ordinary_floor_actual_lower sf logI r
    (source_and_zeroDefect_imply_ordinaryOnly sf logI r hc hz) hsf hlogT hlogU hdiv

/-- Full adopted-row assembly.  Positive defect rows keep their distinct
credit instead of being forced under an unrelated ordinary theorem. -/
theorem fullMask_checked_ordinary_components_actual_lower (sf logI : ℚ → I80)
    (hchecks : ∀ r : Row, sourceOutputCheck sf logI r = true)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hlogT : ∀ r : Row, (logI (rowLogQueries r).1).Contains
      (Real.log (((rowLogQueries r).1 : ℚ) : ℝ)))
    (hlogU : ∀ r : Row, (logI (rowLogQueries r).2).Contains
      (Real.log (((rowLogQueries r).2 : ℚ) : ℝ)))
    (hdiv : ∀ r : Row, chordDivisorCheck r = true) :
    (∑ r : Row, decodeQ80 ((frozenSavedRow r).savedQ80 - rowDefectCredit logI r)) ≤
      ∑ r : Row, rowActualOrdinaryIntegral r := by
  exact Finset.sum_le_sum (fun r _hr => checked_source_ordinary_component_actual_lower
    sf logI r (hchecks r) hsf (hlogT r) (hlogU r) (hdiv r))

/-- If ordinary-only checks pass, every stored row has its same-row actual
ordinary integral meaning.  No assertion that these checks passed is made. -/
theorem fullMask_checked_ordinary_floors_actual_lower (sf logI : ℚ → I80)
    (hchecks : ∀ r : Row, ordinaryOnlyCheck sf logI r = true)
    (hsf : ∀ q : ℚ, (sf q).Contains (actualExtendedThirdLowerFactor (q : ℝ)))
    (hlogT : ∀ r : Row, (logI (rowLogQueries r).1).Contains
      (Real.log (((rowLogQueries r).1 : ℚ) : ℝ)))
    (hlogU : ∀ r : Row, (logI (rowLogQueries r).2).Contains
      (Real.log (((rowLogQueries r).2 : ℚ) : ℝ)))
    (hdiv : ∀ r : Row, chordDivisorCheck r = true) :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80) ≤
      ∑ r : Row, rowActualOrdinaryIntegral r := by
  exact Finset.sum_le_sum (fun r _hr => checked_ordinary_floor_actual_lower
    sf logI r (hchecks r) hsf (hlogT r) (hlogU r) (hdiv r))

/-- Exact decomposition of ORIGINAL saved rows into ordinary and defect
integers, before taking any real limit or asserting any table licence. -/
theorem fullMask_checked_source_sum_identity (sf logI : ℚ → I80)
    (hchecks : ∀ r : Row, sourceOutputCheck sf logI r = true) :
    (∑ r : Row, (frozenSavedRow r).savedQ80) =
      (∑ r : Row, rowOrdinaryOutput sf logI r) + ∑ r : Row, rowDefectCredit logI r := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  exact (sourceOutputCheck_sound sf logI r (hchecks r)).2.2.trans
    (rowSourceOutput_eq_components sf logI r)

theorem checked_stored_total_decode (hc : storedTotalCheck = true) :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80) = decodeQ80 sourceSavedFloorTotal := by
  have he : (∑ r : Row, (frozenSavedRow r).savedQ80) = sourceSavedFloorTotal :=
    of_decide_eq_true hc
  simp only [decodeQ80, ← Rat.cast_sum, ← Finset.sum_div, ← Int.cast_sum]
  rw [he]

end

end ImbalancedChen.P2HistoricalSavedFloorRowsBinder
