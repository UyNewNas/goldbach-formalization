import ImbalancedChen.P2OriginalSaving19SourceJson

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact relocation of FaceRecord (including its original derived instances)
and decodeFace from P2OriginalSaving16PullingOwnership, under the same
namespace. Only the retained SourceJson face-ledger fields are decoded.
No new file reader, parser, source data, or correctness premise is added.
This fresh owner needs a complete audit, including generated declarations,
and independent kernel replay before it can be reused as accepted code.
-/
namespace ImbalancedChen.P2OriginalSaving16PullingOwnership

open P2OriginalSaving19Archive (SourceJson)

structure FaceRecord where
  vertices : Array Nat
  dimension : Nat
  pivot : Nat
  facetSets : Array (Array Nat)
  simplices : Nat
  deriving Inhabited, DecidableEq

def decodeFace (j : SourceJson) : Except String FaceRecord := do
  return {
    vertices := ← j.getObjValAs? (Array Nat) "vertices"
    dimension := ← j.getObjValAs? Nat "dimension"
    pivot := ← j.getObjValAs? Nat "pivot"
    facetSets := ← j.getObjValAs? (Array (Array Nat)) "facet_sets"
    simplices := ← j.getObjValAs? Nat "simplices" }

end ImbalancedChen.P2OriginalSaving16PullingOwnership
