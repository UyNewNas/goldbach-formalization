import Std

/-!
SOURCEONLY / UNCOMPILED. Data carrier only; no analytic imports or checks.
Proposed module: ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore
The untrusted emitter places 4096 consecutive rows in each depth12 tree.
Lookup follows one branch at each depth; it never traverses a global list.
The prefix is represented by its constant original initializer. The emitter
must reject input prefix bytes differing from that initializer; this is an
external byte correspondence check, not a formal SHA/decoder theorem.
-/

namespace ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly

structure RawNode where
  Llo : Int
  Lhi : Int
  Hlo : Int
  Hhi : Int
  deriving DecidableEq

inductive NodeTree : Nat → Type where
  | leaf : RawNode → NodeTree 0
  | fork {depth : Nat} : NodeTree depth → NodeTree depth → NodeTree (depth+1)

/-- High-bit-first, contiguous halves. Legal block offsets are0..4095.
The outer reader guards that domain; an unrestricted read outside a leaf's
domain has no array-correspondence meaning and certifies no such index. -/
noncomputable def NodeTree.read : {depth : Nat} → NodeTree depth → Nat → RawNode :=
  fun {_depth} tree =>
    NodeTree.rec (motive := fun _ _ => Nat → RawNode)
      (fun value _ => value)
      (fun {depth} _left _right readLeft readRight i =>
        if i < 2^depth then readLeft i else readRight (i-2^depth))
      tree

abbrev Block := NodeTree 12

def rawInitial : RawNode := ⟨0,0,(2 : Int)^112,(2 : Int)^112⟩

/-- A single immutable block function supplies all40 update blocks.
Only0..196608 has the specified stored-array meaning. -/
noncomputable def assembledRawRead (blocks : Nat → Block) (i : Nat) : RawNode :=
  if i ≤ 32768 then rawInitial else
  if i ≤ 196608 then
    (blocks ((i-32769)/4096)).read ((i-32769)%4096)
  else rawInitial

end ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
