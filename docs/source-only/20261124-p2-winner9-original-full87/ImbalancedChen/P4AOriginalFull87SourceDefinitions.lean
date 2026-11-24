import ImbalancedChen.P4AOriginalRemainingEighthSourceDefinitions
import ImbalancedChen.OriginalDescendingFifteenRowDefinitions
import ImbalancedChen.OriginalAscendingThirteenRowDefinitions
import ImbalancedChen.P2OriginalDescendingEighthCapDefinitions
import ImbalancedChen.P2OriginalThirdMinorantCapDefinitions
import ImbalancedChen.P4AOriginalH3SourceDefinitions

/-! SOURCE ONLY / NOT COMPILED. Mechanical extraction of existing declarations.
See ../docs/source-only/20261124-p2-winner9-original-full87/DEFINITION_RECEIPT.json.
Names, types and bodies are retained. Original modules must import this core
and remove these declarations using the accompanying refactor patch. -/

namespace ImbalancedChen.P4AOriginalFull87SourceDictionary
noncomputable section
open scoped Classical BigOperators

abbrev Point := Fin 8 → ℝ

inductive Cell where
  | remaining (c : P4AOriginalRemainingEighthSources.Cell)
  | descending (i : Fin 15)
  | ascendingPair (i : Fin 13)
  | h3 (i : Fin 12)
  deriving DecidableEq, Fintype

def Source : Cell → Point → Prop
  | .remaining c, t => P4AOriginalRemainingEighthSources.Source c t
  | .descending i, t => OriginalDescendingFifteenLiteralAffineRows.StrictExportedRows i t
  | .ascendingPair i, t => OriginalAscendingThirteenLiteralAffineRows.StrictExportedRows i t
  | .h3 i, t => P4AOriginalFirstFailureH3Literal.sourceAffineGuard i t

def newCap : Cell → Point → ℝ
  | .remaining c, t => P4AOriginalRemainingEighthSources.newCap c t
  | .descending _, t => P2OriginalDescendingEighthLogSemantics.newCap t
  | .ascendingPair _, t => P2OriginalThirdMinorantLogDictionarySourceOnly.newCap t
  | .h3 _, t => P4AOriginalFirstFailureH3Literal.M8 t

def comparison : Cell → Point → ℝ
  | .remaining c, t => P4AOriginalRemainingEighthSources.comparison c t
  | .descending _, t => P2OriginalDescendingEighthLogSemantics.oldRaw t
  | .ascendingPair _, t => P2OriginalThirdMinorantLogDictionarySourceOnly.comparisonCap t
  | .h3 _, t => P4AOriginalFirstFailureH3Literal.R6 t

end
end ImbalancedChen.P4AOriginalFull87SourceDictionary

namespace ImbalancedChen.P4AOriginalFull87StrictActionTrim
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary

def rowCount : Cell → ℕ
  | .remaining c => P4AOriginalRemainingEighthSources.rowCount c
  | .descending _ => 96
  | .ascendingPair _ => 97
  | .h3 _ => 99

def rowValue : (c : Cell) → Fin (rowCount c) → Point → ℝ
  | .remaining c, r =>
      P4AOriginalRemainingEighthSources.evalRow
        (P4AOriginalRemainingEighthSources.row c r)
  | .descending i, r =>
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        (OriginalDescendingFifteenLiteralAffineRows.exportedCoefficients i r)
  | .ascendingPair i, r =>
      OriginalDescendingFifteenLiteralAffineRows.evaluateCoefficients
        (OriginalAscendingThirteenLiteralAffineRows.exportedCoefficients i r)
  | .h3 i, r =>
      P4AOriginalFirstFailureH3Literal.evalAffine
        (P4AOriginalFirstFailureH3Literal.sourceAffineRows i r).2

def sourceSet (c : Cell) : Set Point := {t | Source c t}

end
end ImbalancedChen.P4AOriginalFull87StrictActionTrim
