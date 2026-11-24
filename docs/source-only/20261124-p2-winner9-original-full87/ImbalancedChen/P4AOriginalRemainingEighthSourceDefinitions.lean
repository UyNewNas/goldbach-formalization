import ImbalancedChen.VariableEnvelope
import ImbalancedChen.P4AOriginalAscendingFourteenSourceDefinitions
import ImbalancedChen.P4AOriginalSeed7Unequal15SourceDefinitions
import ImbalancedChen.P4AOriginalH5H7SourceDefinitions

/-! SOURCE ONLY / NOT COMPILED. Mechanical extraction of existing declarations.
See ../docs/source-only/20261124-p2-winner9-original-full87/DEFINITION_RECEIPT.json.
Names, types and bodies are retained. Original modules must import this core
and remove these declarations using the accompanying refactor patch. -/

namespace ImbalancedChen.P4AOriginalRemainingEighthSources
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

abbrev Point := Fin 8 → ℝ

inductive Cell where
  | ascending (i : Fin 14)
  | seed
  | nine (i : Fin 13)
  | fiftyA
  | fiftyD
  | h5 (i : Fin 7)
  | h7 (i : Fin 10)
  deriving DecidableEq, Fintype

def rowCount : Cell → ℕ
  | .ascending _ | .seed | .fiftyD => 96
  | .nine _ => 97
  | .fiftyA => 95
  | .h5 _ => 100
  | .h7 _ => 101

def row : (c : Cell) → Fin (rowCount c) → Fin 9 → ℚ
  | .ascending i, k => P4AOriginalAscendingFourteenAffineSource.rows i k
  | .seed, k => (P4AOriginalSeed7Unequal15Literal.seed7Rows k).2
  | .nine i, k => (P4AOriginalSeed7Unequal15Literal.nineRows i k).2
  | .fiftyA, k => (P4AOriginalSeed7Unequal15Literal.fiftyAscRows k).2
  | .fiftyD, k => (P4AOriginalSeed7Unequal15Literal.fiftyDescRows k).2
  | .h5 i, k => (P4AOriginalFirstFailureH5H7Literal.h5AffineRows i k).2
  | .h7 i, k => (P4AOriginalFirstFailureH5H7Literal.h7AffineRows i k).2

def evalRow (a : Fin 9 → ℚ) (t : Point) : ℝ :=
  (a 0 : ℝ) + ∑ j : Fin 8, (a j.succ : ℝ) * t j

def Source (c : Cell) (t : Point) : Prop := ∀ k, 0 < evalRow (row c k) t

def selected : Cell → Finset (Fin 8)
  | .ascending _ | .seed => {0,7}
  | .fiftyA => {3,4,5,7}
  | .fiftyD => {1,2,7}
  | _ => {1,3,7}

def selectedSum (c : Cell) (t : Point) : ℝ := ∑ j ∈ selected c, t j

def eta : ℝ := 1 / 1000000

def comparison : Cell → Point → ℝ
  | .ascending _, t | .seed, t => C (t 1 + t 2)
  | .fiftyA, t => A (t 1 + t 4 + t 5)
  | .fiftyD, t => C (t 1 + t 4 + t 5)
  | _, t => A (t 0 + t 3)

def descendingNew : Cell → Bool
  | .fiftyD => true
  | _ => false

def newCap (c : Cell) (t : Point) : ℝ :=
  (if descendingNew c then C (selectedSum c t) else A (selectedSum c t)) - eta

end
end ImbalancedChen.P4AOriginalRemainingEighthSources
