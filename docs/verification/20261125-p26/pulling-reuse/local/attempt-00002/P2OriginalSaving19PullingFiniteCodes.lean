import Init.Data.Nat.Bitwise.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort

/-!
Finite representation helpers for the original Saving19 pulling candidate.
No geometry, real measure, original numerical table or parser is imported.
-/
namespace ImbalancedChen.P2OriginalSaving19PullingFiniteCodes

/-- The exact set of natural-number vertex IDs, with no length truncation. -/
def vertexMask : List Nat → Nat
  | [] => 0
  | v :: vs => (2 ^ v) ||| vertexMask vs

theorem vertexMask_testBit (vs : List Nat) (v : Nat) :
    (vertexMask vs).testBit v = true ↔ v ∈ vs := by
  induction vs with
  | nil => simp [vertexMask]
  | cons a rest ih =>
      simp only [vertexMask, Nat.testBit_or, Bool.or_eq_true,
        Nat.testBit_two_pow, decide_eq_true_eq, List.mem_cons]
      rw [ih]
      exact or_congr eq_comm Iff.rfl

theorem vertexMask_eq_of_mem_iff {xs ys : List Nat}
    (h : ∀ v, v ∈ xs ↔ v ∈ ys) : vertexMask xs = vertexMask ys := by
  apply Nat.eq_of_testBit_eq
  intro v
  apply Bool.eq_iff_iff.mpr
  exact (vertexMask_testBit xs v).trans ((h v).trans (vertexMask_testBit ys v).symm)

def sortedCodes {n : Nat} (code : Fin n → Nat) : List Nat :=
  (List.ofFn code).mergeSort (fun a b => decide (a ≤ b))

/-- An adjacent strict-order check on the complete sorted list proves all-row
injectivity. The permutation theorem retains every original row. -/
theorem code_injective_of_sorted_chain {n : Nat} (code : Fin n → Nat)
    (h : (sortedCodes code).IsChain (· < ·)) : Function.Injective code := by
  apply List.nodup_ofFn.mp
  apply (List.mergeSort_perm (List.ofFn code) (fun a b => decide (a ≤ b))).nodup
  exact (List.isChain_iff_pairwise.mp h).imp (fun hab => ne_of_lt hab)

/-- A projection of the original ledger fields used by a pulling path.
Dimensions and simplex counts remain in the original Archive record. -/
structure LedgerFace where
  vertices : List Nat
  pivot : Nat
  facetSets : List (List Nat)
  deriving DecidableEq

/-- Trace one actual ordered row through recorded faces. Each successful step
uses a recorded pivot and child and a global facet with exactly that intersection.
The result is bounded facet indices; no original constraint ID is coerced.
Failure remains none, including exhausted fuel and malformed terminal faces. -/
def traceFlags (ledger : List LedgerFace) (facets : Array (Array Nat)) :
    Nat → List Nat → List Nat → Option (List (Fin facets.size))
  | 0, _, _ => none
  | fuel + 1, face, ids =>
      match ids with
      | [] => none
      | [apex] => if face = [apex] then some [] else none
      | apex :: next :: tail => do
          let record ← ledger.find? (fun f => f.vertices == face)
          if record.pivot != apex then none else
            record.facetSets.findSome? fun child => do
              if child.contains apex then none else
                if !(next :: tail).all (fun v => child.contains v) then none else do
                  let g ← (List.finRange facets.size).find? (fun f =>
                    (vertexMask face &&& vertexMask (facets[f]).toList) == vertexMask child)
                  let rest ← traceFlags ledger facets fuel child (next :: tail)
                  return g :: rest

end ImbalancedChen.P2OriginalSaving19PullingFiniteCodes
