import ImbalancedChen.P4AOriginalFull87SourceDefinitions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT COMPILED OR KERNEL ACCEPTED.
Mechanical movement of three original source-index declarations.
Names, types and declaration bodies are copied without Lean-token changes.
The existing eleven source/integral cores are not modified.
Use the paired original-owner patch before loading the former owners.
-/

namespace ImbalancedChen.P4AOriginalAscendingFourteenAffineSource
noncomputable section
open scoped Classical BigOperators

def originalId : Fin 14 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14]

end
end ImbalancedChen.P4AOriginalAscendingFourteenAffineSource

namespace ImbalancedChen.P4AOriginalFull87SourceDictionary
noncomputable section
open scoped Classical BigOperators

def globalIndex : Cell → Fin 87
  | .remaining (.ascending i) =>
      ⟨P4AOriginalAscendingFourteenAffineSource.originalId i, by
        fin_cases i <;> decide⟩
  | .remaining .seed => 7
  | .remaining (.nine i) => ⟨30+i.val, by omega⟩
  | .remaining .fiftyA => 43
  | .remaining .fiftyD => 44
  | .remaining (.h5 i) => ⟨70+i.val, by omega⟩
  | .remaining (.h7 i) => ⟨77+i.val, by omega⟩
  | .descending i => ⟨15+i.val, by omega⟩
  | .ascendingPair i => ⟨45+i.val, by omega⟩
  | .h3 i => ⟨58+i.val, by omega⟩

theorem globalIndex_bijective : Function.Bijective globalIndex := by decide

end
end ImbalancedChen.P4AOriginalFull87SourceDictionary
