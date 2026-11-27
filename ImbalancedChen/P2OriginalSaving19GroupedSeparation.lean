import ImbalancedChen.P2OriginalSaving19RationalAffineSeparator
import Mathlib.Data.List.Pairwise

/-! Sibling-cone separators compose through arbitrary finite groupings.
This is a generic geometric lemma; no original family is accepted here. -/
namespace ImbalancedChen.P2OriginalSaving19GroupedSeparation
noncomputable section
open Set MeasureTheory
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19RationalSimplexBridge
open P2OriginalSaving19RationalAffineSeparator

variable {α : Type*}

def Separated (v : α → Fin 9 → QPoint) (left right : List α) : Prop :=
  ∃ a : Form, (∃ j : Fin 8, a j.succ ≠ 0) ∧
    (∀ r ∈ left, ∀ i : Fin 9, 0 ≤ evalQ a (v r i)) ∧
    (∀ r ∈ right, ∀ i : Fin 9, evalQ a (v r i) ≤ 0)

theorem separated_families_aedisjoint
    (linear : α → Point ≃L[ℝ] Point) (base : α → Point)
    (v : α → Fin 9 → QPoint)
    (hv : ∀ r, vertices (linear r) (base r) = fun i => realPoint (v r i))
    {left right : List α} (h : Separated v left right) :
    ∀ r ∈ left, ∀ s ∈ right,
      AEDisjoint volume (support (linear r) (base r)) (support (linear s) (base s)) := by
  obtain ⟨a, hp, hl, hr⟩ := h
  intro r hrg s hsg
  apply separated_intersection_null a (linear r) (linear s) (base r) (base s) hp
  · intro i
    rw [hv r, eval_cast]
    exact_mod_cast hl r hrg i
  · intro i
    rw [hv s, eval_cast]
    exact_mod_cast hr s hsg i

theorem grouped_aedisjoint
    (linear : α → Point ≃L[ℝ] Point) (base : α → Point)
    (v : α → Fin 9 → QPoint)
    (hv : ∀ r, vertices (linear r) (base r) = fun i => realPoint (v r i))
    (groups : List (List α))
    (inside : ∀ group ∈ groups, group.Pairwise (fun r s =>
      AEDisjoint volume (support (linear r) (base r)) (support (linear s) (base s))))
    (between : groups.Pairwise (Separated v)) :
    groups.flatten.Pairwise (fun r s =>
      AEDisjoint volume (support (linear r) (base r)) (support (linear s) (base s))) := by
  apply List.pairwise_flatten.mpr
  refine ⟨inside, between.imp ?_⟩
  intro left right h
  exact separated_families_aedisjoint linear base v hv h

theorem pairwise_from_cover
    (linear : α → Point ≃L[ℝ] Point) (base : α → Point)
    (leaves : List α) (cover : ∀ r, r ∈ leaves)
    (h : leaves.Pairwise (fun r s =>
      AEDisjoint volume (support (linear r) (base r)) (support (linear s) (base s)))) :
    Pairwise (fun r s =>
      AEDisjoint volume (support (linear r) (base r)) (support (linear s) (base s))) := by
  let : Std.Symm (fun r s =>
      AEDisjoint volume (support (linear r) (base r)) (support (linear s) (base s))) :=
    ⟨fun _ _ hr => hr.symm⟩
  intro r s hrs
  exact h.forall (cover r) (cover s) hrs

#print axioms grouped_aedisjoint
#print axioms pairwise_from_cover
end
end ImbalancedChen.P2OriginalSaving19GroupedSeparation
