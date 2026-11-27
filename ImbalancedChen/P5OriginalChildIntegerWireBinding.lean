import ImbalancedChen.P5NamedFifthQ80FloorSoundness
import ImbalancedChen.P5OriginalChildIntegerWireDefinitions

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
Independent transcription of the ORIGINAL producer integer geometry and
exact_floor(log_terms=4), followed by actual two-parent/128-child bindings.
Neither producer d nor its A/B is defined using the proposed rational
candidate. Parent midpoint argmin, strict ratio updates, integer planes,
vertex sum and expanded exact-floor numerator are separate definitions.

The archived subdivision NPZ stores indices/old_floor/new_floor PER PARENT;
it does NOT store per-child d/A/B. The latter are reconstructed source
expressions, not falsely attributed stored NPZ fields. The final small
parent-field bindings are closed theorem source, not executed receipts.
-/
namespace ImbalancedChen.P5OriginalChildIntegerWireBinding

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5NamedFifthPayloadSemantics P5NamedFifthAllChildren
open P5NamedFifthChildSpecificRatio P5NamedFifthQ80FloorSoundness
open P5OldFifthExact64ChildTiling P5OldFifthChildGapIntegral
open P5OldFifthFrozenUpperSurrogate

/-- All these are closed finite arithmetic theorem bodies awaiting the
user's compiler. No checker or reduction was executed to create a receipt. -/
theorem original_parent_picks_exact :
    ∀ b : Bool, ∀ I : OldMask, originalPick (namedParent b) I = sourcePick (namedParent b) I := by
  decide

theorem original_all128_geometry_fields :
    ∀ b : Bool, ∀ c : ChildIndex,
      (originalFields (namedParent b) c).d = sourceChildD (namedParent b) c ∧
      0 < (originalFields (namedParent b) c).B ∧
      ((originalFields (namedParent b) c).A : ℚ) /
        ((originalFields (namedParent b) c).B : ℚ) = childBQ b c := by
  decide

theorem original_all128_expanded_floors_exact :
    ∀ b : Bool, ∀ c : ChildIndex,
      originalExactFloor (originalFields (namedParent b) c) = childFloorZ b c := by
  decide

/-- These source numerator/denominator signs are the actual integer
assertions needed by original exact_floor on a positive-d child. -/
theorem original_all128_active_field_gates :
    ∀ b : Bool, ∀ c : ChildIndex,
      let row := originalFields (namedParent b) c
      0 < row.d →
        2 * row.B < row.A ∧ row.A ≤ 4 * row.B ∧
        2 * (1024 * row.hi 4) * row.B ≤
          (1024 * row.hi 4) * row.A - row.d * row.B := by
  decide

/-- Actual stored PER-PARENT fields, statically extracted from block0000
indices0/1. There is no invented stored per-child array. -/
def storedParentOld (b : Bool) : ℤ :=
  if b then 14082959319322957 else 15820276063068009

def storedParentNew (b : Bool) : ℤ :=
  if b then 22702709338745202 else 24665590035783072

def reconstructedParentReplacement (b : Bool) : ℤ :=
  max (storedParentOld b)
    (∑ c : ChildIndex, originalExactFloor (originalFields (namedParent b) c))

/-- Binding of independently read stored fields to the original source
replacement expression. This source proof is UNEXECUTED; it is not an
archive replay or a computed whole-bank/pair total. -/
theorem stored_first_two_parent_replacements_exact :
    ∀ b : Bool, reconstructedParentReplacement b = storedParentNew b := by
  decide

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
