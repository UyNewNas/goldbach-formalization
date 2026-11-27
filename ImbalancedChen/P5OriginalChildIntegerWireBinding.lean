import ImbalancedChen.P5NamedFifthQ80FloorSoundness
import ImbalancedChen.P5OriginalChildIntegerWireDefinitions
import ImbalancedChen.P5OriginalNamedWireGeometryFields
import ImbalancedChen.P5OriginalWireExpandedFloorAlgebra

/-!
Original producer geometry and exact-floor binding for two named parents.
Independent transcription of the ORIGINAL producer integer geometry and
exact_floor(log_terms=4), followed by actual two-parent/128-child bindings.
Neither producer d nor its A/B is defined using the proposed rational
candidate. Parent midpoint argmin, strict ratio updates, integer planes,
vertex sum and expanded exact-floor numerator are separate definitions.

The archived subdivision NPZ stores indices/old_floor/new_floor PER PARENT;
it does NOT store per-child d/A/B. The latter are reconstructed source
expressions, not falsely attributed stored NPZ fields. Formal acceptance is recorded separately by the isolated normal/kernel audit.
-/
set_option Elab.async false

namespace ImbalancedChen.P5OriginalChildIntegerWireBinding

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5NamedFifthPayloadSemantics P5NamedFifthAllChildren
open P5NamedFifthChildSpecificRatio P5NamedFifthQ80FloorSoundness
open P5OldFifthExact64ChildTiling P5OldFifthChildGapIntegral
open P5OldFifthFrozenUpperSurrogate

/-- Same original integer floor, instantiated on all 128 actual named children.
The source d/AB identities and active gates are independently established. -/
theorem original_all128_expanded_floors_exact :
    ∀ b : Bool, ∀ c : ChildIndex,
      originalExactFloor (originalFields (namedParent b) c) = childFloorZ b c := by
  intro b c
  obtain ⟨hd_eq, hB, hAB⟩ := original_all128_geometry_fields b c
  have hactive : 0 < (originalFields (namedParent b) c).d →
      (∀ i : Fin 5, 0 < (originalFields (namedParent b) c).hi i) ∧
      0 < (originalFields (namedParent b) c).B ∧
      2 * (originalFields (namedParent b) c).B < (originalFields (namedParent b) c).A ∧
      2 * (1024 * (originalFields (namedParent b) c).hi 4) *
          (originalFields (namedParent b) c).B ≤
        (1024 * (originalFields (namedParent b) c).hi 4) *
          (originalFields (namedParent b) c).A -
            (originalFields (namedParent b) c).d * (originalFields (namedParent b) c).B := by
    intro hd
    obtain ⟨h2, _, hg⟩ := original_all128_active_field_gates b c hd
    refine ⟨?_, hB, h2, hg⟩
    intro i
    rw [P5OriginalGenericWireFloorReceiver.original_hi_eq_actual]
    have hp : 0 < (namedParent b).lo i := lt_of_lt_of_le (by norm_num) (named_positive_indices b i)
    have hw : (0 : ℤ) < (width i : ℤ) := by fin_cases i <;> decide
    dsimp only [childRightNumer, childLeftNumer]
    positivity
  have h := P5OriginalWireExpandedFloorAlgebra.originalExactFloor_eq_directed_floor
    (originalFields (namedParent b) c) hactive
  have hn : (originalFields (namedParent b) c).n = 1600 := rfl
  have hw : ∀ i : Fin 5, (wireWidth i : ℚ) = (width i : ℚ) := by
    intro i
    fin_cases i <;> norm_num [wireWidth, width]
  simpa only [childFloorZ, childMinorantQ, prefactorQ, childEQ, hn, hd_eq, hAB,
    P5OriginalGenericWireFloorReceiver.original_hi_eq_actual, hw, Int.cast_ofNat] using h

/-- Actual stored PER-PARENT fields, statically extracted from block0000
indices0/1. There is no invented stored per-child array. -/
def storedParentOld (b : Bool) : ℤ :=
  if b then 14082959319322957 else 15820276063068009

def storedParentNew (b : Bool) : ℤ :=
  if b then 22702709338745202 else 24665590035783072

def reconstructedParentReplacement (b : Bool) : ℤ :=
  max (storedParentOld b)
    (∑ c : ChildIndex, originalExactFloor (originalFields (namedParent b) c))

/-- Pure index grouping; each of the eight blocks has its original eight
children. This regrouping does not reorder or change any child algorithm. -/
private def childBlock (c : ChildIndex) : Fin 8 :=
  ⟨4 * (c 0).val + 2 * (c 1).val + (c 2).val, by
    have h0 := (c 0).isLt
    have h1 := (c 1).isLt
    have h2 := (c 2).isLt
    norm_num [divisions] at h0 h1 h2
    omega⟩

private def childBlockSum (b : Bool) (k : Fin 8) : ℤ :=
  ∑ c : ChildIndex with childBlock c = k,
    originalExactFloor (originalFields (namedParent b) c)

private theorem complete_sum_eq_blocks (b : Bool) :
    (∑ c : ChildIndex, originalExactFloor (originalFields (namedParent b) c)) =
      ∑ k : Fin 8, childBlockSum b k := by
  symm
  exact Finset.sum_fiberwise (Finset.univ : Finset ChildIndex) childBlock
    (fun c => originalExactFloor (originalFields (namedParent b) c))

/-- Derived block sums checked directly against the ORIGINAL integer source.
These are not claimed to be per-child fields in the original NPZ. -/
private theorem block_false_0 : childBlockSum false 0 = 3223438497238445 := by
  decide +kernel

private theorem block_false_1 : childBlockSum false 1 = 3061195911896112 := by
  decide +kernel

private theorem block_false_2 : childBlockSum false 2 = 3224776822578914 := by
  decide +kernel

private theorem block_false_3 : childBlockSum false 3 = 2978752618458360 := by
  decide +kernel

private theorem block_false_4 : childBlockSum false 4 = 3181924426158608 := by
  decide +kernel

private theorem block_false_5 : childBlockSum false 5 = 2975247252430657 := by
  decide +kernel

private theorem block_false_6 : childBlockSum false 6 = 3140789045882326 := by
  decide +kernel

private theorem block_false_7 : childBlockSum false 7 = 2879465461139650 := by
  decide +kernel

private theorem blocks_false_exact (k : Fin 8) :
    childBlockSum false k = (![3223438497238445, 3061195911896112, 3224776822578914, 2978752618458360, 3181924426158608, 2975247252430657, 3140789045882326, 2879465461139650] : Fin 8 → ℤ) k := by
  fin_cases k
  · exact block_false_0
  · exact block_false_1
  · exact block_false_2
  · exact block_false_3
  · exact block_false_4
  · exact block_false_5
  · exact block_false_6
  · exact block_false_7

private theorem parent_false_replacement_exact :
    reconstructedParentReplacement false = storedParentNew false := by
  have hs : (∑ c : ChildIndex,
      originalExactFloor (originalFields (namedParent false) c)) = 24665590035783072 := by
    rw [complete_sum_eq_blocks]
    simp_rw [blocks_false_exact]
    decide
  dsimp only [reconstructedParentReplacement]
  rw [hs]
  decide

private theorem block_true_0 : childBlockSum true 0 = 2797640793815422 := by
  decide +kernel

private theorem block_true_1 : childBlockSum true 1 = 2803697721332322 := by
  decide +kernel

private theorem block_true_2 : childBlockSum true 2 = 3017552356177212 := by
  decide +kernel

private theorem block_true_3 : childBlockSum true 3 = 2829718232063452 := by
  decide +kernel

private theorem block_true_4 : childBlockSum true 4 = 2809793170765632 := by
  decide +kernel

private theorem block_true_5 : childBlockSum true 5 = 2748695464061187 := by
  decide +kernel

private theorem block_true_6 : childBlockSum true 6 = 2964728700008105 := by
  decide +kernel

private theorem block_true_7 : childBlockSum true 7 = 2730882900521870 := by
  decide +kernel

private theorem blocks_true_exact (k : Fin 8) :
    childBlockSum true k = (![2797640793815422, 2803697721332322, 3017552356177212, 2829718232063452, 2809793170765632, 2748695464061187, 2964728700008105, 2730882900521870] : Fin 8 → ℤ) k := by
  fin_cases k
  · exact block_true_0
  · exact block_true_1
  · exact block_true_2
  · exact block_true_3
  · exact block_true_4
  · exact block_true_5
  · exact block_true_6
  · exact block_true_7

private theorem parent_true_replacement_exact :
    reconstructedParentReplacement true = storedParentNew true := by
  have hs : (∑ c : ChildIndex,
      originalExactFloor (originalFields (namedParent true) c)) = 22702709338745202 := by
    rw [complete_sum_eq_blocks]
    simp_rw [blocks_true_exact]
    decide
  dsimp only [reconstructedParentReplacement]
  rw [hs]
  decide

/-- Binding of independently read stored fields to the original source
replacement expression. Only the two displayed original parents are
checked; this is not a whole-bank/pair total. -/
theorem stored_first_two_parent_replacements_exact :
    ∀ b : Bool, reconstructedParentReplacement b = storedParentNew b := by
  intro b
  cases b
  · exact parent_false_replacement_exact
  · exact parent_true_replacement_exact

theorem stored_first_two_new_strictly_exceed_old (b : Bool) :
    storedParentOld b < storedParentNew b := by
  cases b <;> decide

/-- These TWO stored replacements choose their complete child sum. No
old parent floor is added to its children, and no pair total is evaluated. -/
theorem stored_first_two_new_eq_complete_child_sum (b : Bool) :
    storedParentNew b =
      ∑ c : ChildIndex, originalExactFloor (originalFields (namedParent b) c) := by
  have h := stored_first_two_parent_replacements_exact b
  unfold reconstructedParentReplacement at h
  have hlt := stored_first_two_new_strictly_exceed_old b
  have hle : storedParentOld b ≤
      ∑ c : ChildIndex, originalExactFloor (originalFields (namedParent b) c) := by
    by_contra hn
    have hsmall : (∑ c : ChildIndex,
        originalExactFloor (originalFields (namedParent b) c)) ≤ storedParentOld b :=
      (lt_of_not_ge hn).le
    rw [max_eq_left hsmall] at h
    linarith
  rw [max_eq_right hle] at h
  exact h.symm

noncomputable section
open scoped Classical

/-- Real geometry fields remain attached to the SAME child index. -/
theorem original_lo_is_actual (b : Bool) (c : ChildIndex) (i : Fin 5) :
    (originalFields (namedParent b) c).lo i = childLeftNumer (namedParent b) c i := by
  have hw : wireWidth i = (width i : ℤ) := by fin_cases i <;> decide
  simp [originalFields, wireLo, childLeftNumer, hw]

theorem original_hi_is_actual (b : Bool) (c : ChildIndex) (i : Fin 5) :
    (originalFields (namedParent b) c).hi i = childRightNumer (namedParent b) c i := by
  have hw : wireWidth i = (width i : ℤ) := by fin_cases i <;> decide
  simp [originalFields, wireHi, wireLo, childRightNumer, childLeftNumer, hw]

/-- The original reconstructed field expression inherits the existing
sharp directed-log soundness without redoing a Mercator/Jensen proof. -/
theorem reconstructed_original_floor_sound (b : Bool) (c : ChildIndex) :
    ((originalExactFloor (originalFields (namedParent b) c) : ℤ) : ℝ) /
        (2 : ℝ) ^ 80 ≤
      P5ChildSelectedOwnerJensenReserve.certifiedChildJensen
        (sourcePicks (namedParent b)) (namedParent b) c
        (childBQ b c) (sourceChildD (namedParent b) c) := by
  rw [original_all128_expanded_floors_exact]
  simpa [childFloorQ, ImbalancedChen.Certificates.P2DirectedLogRounding.dyadicScale]
    using childFloorQ_le_actual_certified_Jensen b c

end
end ImbalancedChen.P5OriginalChildIntegerWireBinding
