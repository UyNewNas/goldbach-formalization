import ImbalancedChen.P2IndependentFullProxyFiniteCertificate
import Mathlib.Tactic.FinCases

/-!
SOURCE ONLY; uncompiled and UNEVALUATED.

This file finally supplies closed finite source-check proof proposals for
the ORIGINAL frozen 17572 saved rows.  It compares independently imported
literal payloads with the actual historical SieveTable(16384,8), Q80
point/log_point interpreter, two-plane ordinary max and separate defect
lookup/output.  Neither side is replaced by a new proposed evaluator.

The finite proof is split by the existing 186 t-strips.  No strip proof,
source engine, independent Mercator evaluator or aggregate decision was
executed in this author task.  Compiler-owned chunking/sharing may still
be needed.  The display total 112908... is not an input or an output here.
-/

namespace ImbalancedChen.P2HistoricalFullSourceRowWitness

noncomputable section

open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2HistoricalSavedFloorRowsBinder P2HistoricalSavedFloorFullBinder
open P2HistoricalFullFloorProxyChain
open P2IndependentFullProxyFiniteCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The actual ordinary producer, including its original maximum eight.
No P112 weighted-node table or true log formula replaces these integers. -/
theorem actualSf_exact_source (q : ℚ) :
    actualSf q = P2HistoricSieveTableSemantics.point 16384 8 q.num (q.den : ℤ) := rfl

/-- First round the rational query to Q80, then retain the lower log_point
output at lo and the upper output at hi.  This is the historical wrapper. -/
theorem actualLog_exact_source (q : ℚ) :
    actualLog q =
      let x := I80.point q
      ⟨(Certificates.P2HistoricLogPointInterpreter.logPoint x.lo).lo,
        (Certificates.P2HistoricLogPointInterpreter.logPoint x.hi).hi⟩ := rfl

/-- Auditable expansion of the existing source output.  All operations are
the actual I80 primitives, including each directed rounding and both max0s.
The independently stored frozenSavedRow is deliberately absent from this
formula; its equality with this program is the separate finite obligation. -/
theorem actual_source_directed_formula (r : Row) :
    rowSourceOutput actualSf actualLog r =
      let tl := rowTL r
      let tr := rowTR r
      let ul := rowUL r
      let ur := rowUR r
      let rr := ordinaryRanges tl tr ul ur
      let base := (ordinaryRectangleBase actualSf actualLog tl tr ul ur rr.1).lo
      let best₀ := if chordEligible ordinaryPlane₀ ordinaryPlane₁ tl tr ul ur then
        max base (ordinaryRectangleChord actualSf actualLog tl tr ul ur ordinaryPlane₀).lo else base
      let best₁ := if chordEligible ordinaryPlane₁ ordinaryPlane₀ tl tr ul ur then
        max best₀ (ordinaryRectangleChord actualSf actualLog tl tr ul ur ordinaryPlane₁).lo else best₀
      let x := I80.ofEnclosure ⟨rr.1 / Certificates.P2HistoricQ80DefectLookup.a,
        rr.2 / Certificates.P2HistoricQ80DefectLookup.a⟩
      let hlow := bankDefectLookup x
      let defect := ((((I80.point 4).mul hlow).mul
        (rectangleMass actualLog tl tr ul ur)).div (I80.point rr.2)).lo
      max 0 best₁ + max 0 defect := rfl

/-- The imported list is totalized with getD.  This finite structural
obligation confirms every actual strip has exactly its original width. -/
theorem original_frozen_strip_lengths :
    ∀ i : Fin 186, (frozenSavedStrips i).length = 512 - firstU i := by
  decide +kernel

/-- One actual original t-strip.  The check includes BOTH frozen grid keys
and the full stored ordinary-plus-defect numerator, not an ordinary-only
field or an equality to a separately chosen bound. -/
def stripSourceCheck (i : Fin 186) : Bool :=
  decide (∀ j : Fin (512 - firstU i), fullSourceRowCheck ⟨i, j⟩ = true)

/-- 186 closed finite proof bodies after fin_cases; all remain unexecuted.
Only the original strip coordinate is split, so every existing dependent
u-row is retained.  No source-output equality is assumed by a caller. -/
theorem original_strip_source_checks : ∀ i : Fin 186, stripSourceCheck i = true := by
  intro i
  fin_cases i <;> decide +kernel

theorem original_fullSourceRowCheck_true (r : Row) : fullSourceRowCheck r = true := by
  have hs : ∀ j : Fin (512 - firstU r.1), fullSourceRowCheck ⟨r.1, j⟩ = true :=
    of_decide_eq_true (original_strip_source_checks r.1)
  exact hs r.2

/-- Payload fields are independent literals.  Their original t/u keys and
the complete actual source output are bound to the very same selected Row. -/
theorem original_frozen_source_fields (r : Row) :
    (frozenSavedRow r).tIndex = (indices r).1 ∧
      (frozenSavedRow r).uIndex = (indices r).2 ∧
      (frozenSavedRow r).savedQ80 = rowSourceOutput actualSf actualLog r :=
  fullSourceRowCheck_sound r (original_fullSourceRowCheck_true r)

theorem original_frozen_full_components (r : Row) :
    (frozenSavedRow r).savedQ80 = rowOrdinaryOutput actualSf actualLog r + rowDefectCredit actualLog r := by
  rw [(original_frozen_source_fields r).2.2, rowSourceOutput_eq_components]

/-- Symbolic aggregate identity only.  No saved display total is pasted,
checked or substituted for the actual source outputs. -/
theorem original_stored_sum_eq_source_sum :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4) =
      ∑ r : Row, decodeQ80 (rowSourceOutput actualSf actualLog r) / 4 := by
  apply Finset.sum_congr rfl
  intro r _hr
  rw [(original_frozen_source_fields r).2.2]

theorem original_stored_sum_le_full_proxy :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4) ≤ selectedFullProxy := by
  exact Finset.sum_le_sum (fun r _hr =>
    checked_frozen_full_saved_le_proxy r (original_fullSourceRowCheck_true r))

/-- This consumes the frozen D evaluator and its proof, with no alternate
logarithm backend, numerical aggregate, analytic licence or copied total. -/
theorem original_stored_sum_le_independent320_upper :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4) ≤ (selectedProxyUpper : ℝ) :=
  original_stored_sum_le_full_proxy.trans selectedFullProxy_le_directed_upper

/-- Both the D aggregate decision and this file's strip decisions are
closed source proposals, unexecuted until compiler intake. -/
theorem original_stored_sum_lt_lambda :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4) < (lambda : ℝ) :=
  checked_full_saved_sum_lt_lambda original_fullSourceRowCheck_true

theorem decoded_stored_integer_sum_eq :
    decodeQ80 (∑ r : Row, (frozenSavedRow r).savedQ80) / 4 =
      ∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80 / 4 := by
  simp [decodeQ80, Finset.sum_div]

/-- Same original selected stored-output sum and the manuscript lambda,
with the original Q80 scaling and one Chen-quarter division. -/
theorem original_stored_integer_sum_lt_lambda :
    decodeQ80 (∑ r : Row, (frozenSavedRow r).savedQ80) / 4 < (lambda : ℝ) := by
  rw [decoded_stored_integer_sum_eq]
  exact original_stored_sum_lt_lambda

end

end ImbalancedChen.P2HistoricalFullSourceRowWitness
