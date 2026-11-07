import ImbalancedChen.P2HistoricalSavedFloorFullBinder
import ImbalancedChen.P2HistoricalSavedFloorStripSumBridge

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.

This is a structural reduction of the actual all-row historical output
equality to 186 independently decidable strip predicates. No predicate is
evaluated here. In particular this file does not claim that the frozen
savedQ80 fields match the historical Q80 engine outputs.

The source's ordinal is kept separate from the t/u grid indices. An
additional strip predicate states the expected consecutive source ordinal;
it is not used as an array index or silently inferred from a saved value.
The main output predicate is the original `fullSourceRowCheck`, which
includes the ordinary maximum and positive defect credit.
-/

namespace ImbalancedChen.CertificateSol6SavedRowStripCheckReduction

open scoped BigOperators
open Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorRowsBinder
open P2HistoricalSavedFloorFullBinder
open P2HistoricalSavedFloorStripSumBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One actual strip's complete historical source-output check. Its
truth value is deliberately not asserted. -/
def fullSourceStripCheck (i : Fin 186) : Bool :=
  decide (∀ j : Fin (512 - firstU i), fullSourceRowCheck ⟨i, j⟩ = true)

/-- Exact, proof-only reduction of the 17,572-row proposition to 186
strip propositions. This theorem does not evaluate any strip. -/
theorem all_full_source_rows_iff_strips :
    (∀ r : Row, fullSourceRowCheck r = true) ↔
      (∀ i : Fin 186, fullSourceStripCheck i = true) := by
  constructor
  · intro h i
    apply decide_eq_true
    intro j
    exact h ⟨i, j⟩
  · intro h
    rintro ⟨i, j⟩
    exact (of_decide_eq_true (h i)) j

/-- A checked strip binds the frozen t/u indices and the COMPLETE original
output, including the separate positive h-defect credit, at every row. -/
theorem checked_strip_row_complete_components (i : Fin 186)
    (h : fullSourceStripCheck i = true) (j : Fin (512 - firstU i)) :
    (frozenSavedRow ⟨i, j⟩).tIndex = (indices ⟨i, j⟩).1 ∧
      (frozenSavedRow ⟨i, j⟩).uIndex = (indices ⟨i, j⟩).2 ∧
      (frozenSavedRow ⟨i, j⟩).savedQ80 =
        rowOrdinaryOutput actualSf actualLog ⟨i, j⟩ +
          rowDefectCredit actualLog ⟨i, j⟩ := by
  have hc : fullSourceRowCheck ⟨i, j⟩ = true :=
    (of_decide_eq_true h) j
  obtain ⟨hti, hui, hout⟩ := fullSourceRowCheck_sound ⟨i, j⟩ hc
  exact ⟨hti, hui, hout.trans (rowSourceOutput_eq_components actualSf actualLog ⟨i, j⟩)⟩

/-- The inherited dependent-row dictionary guarantees that a checked
strip never reaches `frozenSavedRow`'s default. -/
theorem strip_row_literal_index_in_bounds (i : Fin 186)
    (j : Fin (512 - firstU i)) :
    j.val < (frozenSavedStrips i).length :=
  frozen_saved_row_index_in_bounds ⟨i, j⟩

/-- The source ordinal begins immediately after the 6091 E0 rows.
Only earlier E1 strip lengths are counted; the ordinal never serves as a
grid index. This is the explicit proposed ordinal dictionary, not a
claim that the frozen rows have passed its check. -/
def expectedSourceOrdinal (r : Row) : ℕ :=
  6091 +
    (∑ k ∈ (Finset.univ.filter (fun k : Fin 186 => k < r.1)),
      512 - firstU k) + r.2.val

def sourceOrdinalStripCheck (i : Fin 186) : Bool :=
  decide (∀ j : Fin (512 - firstU i),
    (frozenSavedRow ⟨i, j⟩).sourceOrdinal = expectedSourceOrdinal ⟨i, j⟩)

/-- The ordinal check is a separate 186-strip finite obligation. -/
theorem all_source_ordinals_iff_strips :
    (∀ r : Row,
      (frozenSavedRow r).sourceOrdinal = expectedSourceOrdinal r) ↔
      (∀ i : Fin 186, sourceOrdinalStripCheck i = true) := by
  constructor
  · intro h i
    apply decide_eq_true
    intro j
    exact h ⟨i, j⟩
  · intro h
    rintro ⟨i, j⟩
    exact (of_decide_eq_true (h i)) j

end ImbalancedChen.CertificateSol6SavedRowStripCheckReduction
