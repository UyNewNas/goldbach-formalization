import Lean
import ImbalancedChen.P2OriginalSaving16OriginalInput
import ImbalancedChen.P2OriginalSaving16Decoder
import ImbalancedChen.P2OriginalSaving16Q96FloorCore
import ImbalancedChen.P2OriginalSaving19SourceJson
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import ImbalancedChen.P2OriginalSaving16FiniteCore

/-!
SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.

Mechanical relocation of the original saving16 archive's 37 source commands:
35 named declarations, the original text-reader elaborator, and its original
simplex-validity Decidable instance. Their namespace, declaration text, pure
parser, rational operations, separate Q96 floors, and closed proof bodies
are unchanged. The original owner retains the actual atlas and closure
bridge declarations and imports this module.

The reader still reads all fourteen ORIGINAL texts from
../goldbach-research at user compilation, and emits only String literals.
No JSON parsing, determinant evaluation, numerical generation, or theorem
construction has been performed during this extraction. The existing
39,741-simplex checks and aggregate guards remain UNEVALUATED. Their truth,
elaboration, kernel reduction, memory use, and runtime are not certified.

This finite layer imports no project atlas or custom native dependency.
It does not establish the real-integral or source-ownership endpoint.
-/
namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16JensenFloor (q96Floor)
open scoped BigOperators


noncomputable section







/-- Closed original-file parse-success guard, UNEVALUATED. No parse
success premise or external PASS record is introduced. -/
theorem original_parse_success_tag : ∀ i : Fin 14, parsedCellSuccess i = true := by
  decide +kernel

/-- Recover the exact decoded record by constructor elimination, without
an equality test on any record or JSON payload. -/
theorem original_parse_success : ∀ i : Fin 14, parsedCell i = .ok (archive i) := by
  intro i
  cases h : parsedCell i with
  | error message =>
      have hs := original_parse_success_tag i
      simp [parsedCellSuccess, h] at hs
  | ok record =>
      simp [archive, h]
      rfl





theorem original_simplex_operations : ∀ (i : Fin 14) (s : Fin (archive i).simplices.size),
    simplexValid (archive i) s := by decide +kernel



/-- Pure, closed ORIGINAL-operation comparison. It sums39,741 separate
floors; it neither floors their sum nor reads a reported gain as proof.
This is UNEVALUATED, with truth and resources unverified. -/
theorem original_q96_aggregate : aggregateNumerator = historicalNumerator := by decide +kernel

theorem original_counts :
    (∑ i : Fin 14, (archive i).simplices.size) = 39741 ∧
    (∑ i : Fin 14, (archive i).active8.size) = 39381 := by decide +kernel

end
end ImbalancedChen.P2OriginalSaving16OriginalArchive
