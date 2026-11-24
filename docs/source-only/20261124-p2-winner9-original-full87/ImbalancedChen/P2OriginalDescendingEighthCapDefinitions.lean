import ImbalancedChen.VariableEnvelope
import Mathlib.Data.Fin.VecNotation

/-! SOURCE ONLY / NOT COMPILED. Mechanical extraction of existing declarations.
See ../docs/source-only/20261124-p2-winner9-original-full87/DEFINITION_RECEIPT.json.
Names, types and bodies are retained. Original modules must import this core
and remove these declarations using the accompanying refactor patch. -/

namespace ImbalancedChen.P2OriginalDescendingEighthLogSemantics
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

abbrev Point := Fin 8 → ℝ

def eta : ℝ := 1 / 1000000

def d (t : Point) : ℝ := t 1 + t 2

def selectedSum (t : Point) : ℝ := t 0 + t 7

def oldRaw (t : Point) : ℝ := C (d t)

def newCap (t : Point) : ℝ := C (selectedSum t) - eta

end
end ImbalancedChen.P2OriginalDescendingEighthLogSemantics
