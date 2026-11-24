import ImbalancedChen.P2Winner9CompleteSeedTypes
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Prod

/-! Exact addition of the three selected Q96 numerator fields. -/

namespace ImbalancedChen.P2Winner9LedgerCore

open scoped BigOperators
open P2Winner9CompleteSeedTypes

abbrev SelectedNumerators := Nat × Nat × Nat

def selectedNumerators (r : RawRow) : SelectedNumerators :=
  (r.logSelected, r.curvatureSelected, r.mixedSelected)

def selectedTotals (rows : Array RawRow) : SelectedNumerators :=
  (rows.toList.map selectedNumerators).sum

theorem sum_selectedNumerators_eq {n : Nat} {rows : Array RawRow} (hs : rows.size = n) :
    (∑ i : Fin n, selectedNumerators rows[i.val]!) = selectedTotals rows := by
  rw [← List.sum_ofFn, selectedTotals]
  congr 1
  refine List.ext_getElem (by simpa using hs.symm) ?_
  intro i h₁ h₂
  have hi : i < rows.size := by simpa using h₂
  rw [List.getElem_ofFn, List.getElem_map, Array.getElem_toList, getElem!_pos rows i hi]

theorem selectedTotals_flatten (blocks : Array (Array RawRow)) :
    selectedTotals blocks.flatten = (blocks.toList.map selectedTotals).sum := by
  simp only [selectedTotals, Array.toList_flatten, List.map_flatten, List.map_map,
    List.sum_flatten, Function.comp_def]
  rfl

theorem sum_selectedNumerators_components {ι : Type*} [Fintype ι] (row : ι → RawRow) :
    (∑ i, selectedNumerators (row i)) =
      (∑ i, (row i).logSelected, ∑ i, (row i).curvatureSelected,
        ∑ i, (row i).mixedSelected) := by
  ext <;> simp [selectedNumerators, Prod.fst_sum, Prod.snd_sum]

end ImbalancedChen.P2Winner9LedgerCore
