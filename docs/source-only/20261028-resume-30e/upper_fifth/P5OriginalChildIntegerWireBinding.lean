import ImbalancedChen.P5NamedFifthQ80FloorSoundness

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

/-- Source widths for divisions=(2,2,2,2,4), independent of the geometry API. -/
def wireWidth (i : Fin 5) : ℤ := ![2, 2, 2, 2, 1] i

def wireLo (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℤ :=
  4 * raw.lo i + wireWidth i * ((c i).val : ℤ)

def wireHi (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) : ℤ :=
  wireLo raw c i + wireWidth i

/-- Exact source product((0,1),repeat=5) order: last coordinate is fastest. -/
def producerBits : List Word :=
  [false, true].flatMap fun e0 =>
  [false, true].flatMap fun e1 =>
  [false, true].flatMap fun e2 =>
  [false, true].flatMap fun e3 =>
  [false, true].map fun e4 => (e0, e1, e2, e3, e4)

def vertexNumer (raw : FifthWireRow) (c : ChildIndex) (w : Word) (i : Fin 5) : ℤ :=
  wireLo raw c i + if wordChoice w i then wireWidth i else 0

/-- Original parent_picks INTEGER score columns; numpy.argmin tie order
is A then C then cap. These are not the rational sourcePick definition. -/
def originalPick (raw : FifthWireRow) (I : OldMask) : Fin 3 :=
  let ss : ℤ := ∑ i ∈ I, (2 * raw.lo i.castSucc + 1)
  let a := 32 * raw.grid + 16 * ss
  let c := 57 * raw.grid - 48 * ss
  let k := 153 * raw.grid / 4
  if a ≤ c ∧ a ≤ k then 0 else if c ≤ k then 1 else 2

/-- Source geometry uses n=1600 and the common affine scale32*n. -/
def oldPlaneNumer (pick : Fin 3) (ss : ℤ) : ℤ :=
  if pick.val = 0 then 25600 + 16 * ss
  else if pick.val = 1 then 45600 - 48 * ss else 30600

def oldNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  let seed := 30600 - 12 * v 2
  let values := (Finset.range 15).image fun k =>
    let I := maskSlots 4 (k + 1)
    oldPlaneNumer (originalPick raw I) (∑ i ∈ I, v i.castSucc)
  (insert seed values).max' ⟨seed, Finset.mem_insert_self _ _⟩

def selectedNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  ∑ i ∈ maskSlots 5 raw.mask.toNat, v i

def capNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  min (25600 + 16 * selectedNumer raw v) (45600 - 48 * selectedNumer raw v)

def gapNumer (raw : FifthWireRow) (v : Fin 5 → ℤ) : ℤ :=
  capNumer raw v - max (oldNumer raw v) (32 * ((∑ i : Fin 5, v i) + 2 * v 4))

def originalD (raw : FifthWireRow) (c : ChildIndex) : ℤ :=
  (producerBits.map (fun w => gapNumer raw (vertexNumer raw c w))).sum

structure RatioPair where
  num : ℤ
  den : ℤ
  deriving DecidableEq

def planeRatioPair (raw : FifthWireRow) (c : ChildIndex) (side : Bool) (w : Word) : RatioPair :=
  let v := vertexNumer raw c w
  let ss := selectedNumer raw v
  let plane := if side then 45600 - 48 * ss else 25600 + 16 * ss
  ⟨plane - 32 * ∑ i : Fin 5, v i, 32 * v 4⟩

/-- Strict original update retains the earlier unreduced pair at a tie. -/
def updatePair (old next : RatioPair) : RatioPair :=
  if old.num * next.den < next.num * old.den then next else old

def originalPlaneMax (raw : FifthWireRow) (c : ChildIndex) (side : Bool) : RatioPair :=
  let first := planeRatioPair raw c side (false, false, false, false, false)
  producerBits.tail.foldl (fun old w => updatePair old (planeRatioPair raw c side w)) first

/-- Source geometry finally takes the smaller of the TWO vertex maxima;
its strict comparison retains the A pair at a tie. -/
def originalAB (raw : FifthWireRow) (c : ChildIndex) : RatioPair :=
  let a := originalPlaneMax raw c false
  let cc := originalPlaneMax raw c true
  if cc.num * a.den < a.num * cc.den then cc else a

structure OriginalChildFields where
  n : ℤ
  lo : Fin 5 → ℤ
  hi : Fin 5 → ℤ
  mask : ℤ
  d : ℤ
  A : ℤ
  B : ℤ

def originalFields (raw : FifthWireRow) (c : ChildIndex) : OriginalChildFields :=
  let ab := originalAB raw c
  ⟨1600, wireLo raw c, wireHi raw c, raw.mask, originalD raw c, ab.num, ab.den⟩

/-- The original expanded exact_floor expression with log_terms=4.
Python // with the proved positive denominator is represented by Int /.
The d<=0 source fallback is exactly preserved. -/
def originalExactFloor (row : OriginalChildFields) : ℤ :=
  if row.d ≤ 0 then 0 else
  let H := 1024 * row.hi 4
  let C := H * row.A - row.d * row.B
  let z := row.d * row.B
  let den := 2 * H * (row.A - row.B) - z
  let rn := 2 * z * (15 * den ^ 4 + 5 * z ^ 2 * den ^ 2 + 3 * z ^ 4)
  let rd := 15 * den ^ 5
  let y := C - 2 * H * row.B
  let cc := C ^ 2
  let yy := y ^ 2
  let ln := 2 * y * (315 * cc ^ 4 - 210 * yy * cc ^ 3 -
    42 * yy ^ 2 * cc ^ 2 - 18 * yy ^ 3 * cc - 10 * yy ^ 4)
  let ld := 315 * C ^ 7 * (cc - yy)
  let dn := row.B * (C * rn * ld - row.d * row.B * ln * rd)
  let dd := C * row.A * rd * ld
  let numerator := 4 * row.n * (∏ i : Fin 5, wireWidth i) * dn
  let denominator := (∏ i : Fin 5, row.hi i) * row.hi 4 * dd
  numerator * (2 : ℤ) ^ 80 / denominator

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
