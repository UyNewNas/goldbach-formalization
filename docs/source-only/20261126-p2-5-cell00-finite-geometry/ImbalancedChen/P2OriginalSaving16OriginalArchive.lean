import Lean
import ImbalancedChen.P2OriginalSaving16JensenFloor
import ImbalancedChen.P2OriginalSaving19SourceJson
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ImbalancedChen.P2OriginalSaving16FiniteArchive
import ImbalancedChen.P2OriginalSaving16FiniteGeometryCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All fourteen ORIGINAL witness texts are read only at USER compilation.
The elaborator emits only ordinary String literals. It parses no JSON,
computes no determinant or floor, and manufactures no theorem. The shared
fuel-recursive SourceJson parser and all decoders/checks below are pure.
Lean.Json.parse (which uses partial recursion) is deliberately not used.

Every finite theorem body below is UNEVALUATED. Truth, elaboration and
kernel resource feasibility are unverified. In particular Matrix.det on
39,741 rational8x8 matrices can be expensive; no feasibility claim is made.
These are proposed closed proofterms, not accepted historical PASS flags.

Compile from the repository root after installing the registered source
modules. Original files remain at ../goldbach-research. No archive text was
exported or expanded while authoring this source.
-/
namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16JensenFloor (q96Floor)
open scoped BigOperators


noncomputable section


open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16CellOwnership

def atlasCell (i : Fin 14) : Cell :=
  if h : i.val < 3 then .inl ⟨i.val, h⟩ else .inr ⟨i.val - 3, by omega⟩

theorem atlasCell_sourceId (i : Fin 14) : (sourceId (atlasCell i)).val = originalId i := by
  fin_cases i <;> decide

def castPoint (x : QPoint) : Point := fun j => (x j : ℝ)

theorem original_headers : ∀ i : Fin 14,
    (archive i).cellId = originalId i ∧ (archive i).dimension = 8 ∧
    (archive i).physicalJacobian = 1 ∧
    (∀ v : Fin (archive i).vertices.size, ((archive i).vertices[v]).size = 8) ∧
    0 < (archive i).simplices.size := by decide

theorem original_patterns : ∀ i : Fin 14,
    (archive i).leftMasks.toList.toFinset =
      P4AOriginalAscending14Literal42.literalLeftMasks (sourceId (atlasCell i)) ∧
    Disjoint (archive i).leftMasks.toList.toFinset (archive i).rightMasks.toList.toFinset ∧
    (archive i).leftMasks.toList.toFinset ∪ (archive i).rightMasks.toList.toFinset =
      Finset.Icc 1 63 ∧ 6 ∈ (archive i).rightMasks.toList.toFinset := by decide

theorem original_strict_centers : ∀ (i : Fin 14) (k : Fin 96),
    0 < evalQ (rows (atlasCell i) k).2 (interiorCandidate (archive i)) := by decide

theorem original_vertices_all96 : ∀ (i : Fin 14) (v : Fin (archive i).vertices.size)
    (k : Fin 96), 0 ≤ evalQ (rows (atlasCell i) k).2 (point (archive i) v.val) := by decide

theorem evalQ_cast (a : Fin 9 → ℚ) (x : QPoint) :
    evalRow a (castPoint x) = (evalQ a x : ℝ) := by
  simp [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine, castPoint, evalQ,
    Rat.cast_sum, Rat.cast_add, Rat.cast_mul]

/-- Concrete original vertices lie in the closure of their own96-row
source cell. No candidate-facet equality or completeness premise occurs. -/
theorem original_vertex_mem_closure (i : Fin 14) (v : Fin (archive i).vertices.size) :
    castPoint (point (archive i) v.val) ∈ closure (cell (atlasCell i)) := by
  apply closedRows_mem_closure (atlasCell i) (castPoint (interiorCandidate (archive i)))
  · intro k
    rw [evalQ_cast]
    exact_mod_cast original_strict_centers i k
  · intro k
    rw [evalQ_cast]
    exact_mod_cast original_vertices_all96 i v k

theorem original_facet_indices : ∀ (i : Fin 14)
    (f : Fin (archive i).facetOriginalIndices.size),
    (archive i).facetOriginalIndices[f] < 96 := by decide

theorem original_positive_normal_balance : ∀ i : Fin 14,
    (archive i).positiveNormalBalance.size = (archive i).facetOriginalIndices.size ∧
    (∀ f : Fin (archive i).facetOriginalIndices.size,
      0 < (archive i).positiveNormalBalance.getD f.val 0) ∧
    ∀ j : Fin 8,
      (∑ f : Fin (archive i).facetOriginalIndices.size,
        (archive i).positiveNormalBalance.getD f.val 0 *
          (rows (atlasCell i)
            ⟨(archive i).facetOriginalIndices[f], original_facet_indices i f⟩).2 j.succ) = 0 := by
  decide

/-- The exact original facet IDs and vertex incidence are checked against
the actual96 physical rows. The full active-basis/face-pulling theorem is
still absent: this result must not be described as a triangulation proof. -/
theorem original_facet_incidence : ∀ (i : Fin 14),
    (archive i).facetOriginalIndices.size = (archive i).facetVertices.size ∧
    ∀ (f : Fin (archive i).facetOriginalIndices.size)
      (v : Fin (archive i).vertices.size),
        (v.val ∈ ((archive i).facetVertices.getD f.val #[]).toList ↔
          evalQ (rows (atlasCell i)
            ⟨(archive i).facetOriginalIndices[f], original_facet_indices i f⟩).2
              (point (archive i) v.val) = 0) := by
  decide


/-- Arithmetic endpoint only, not the source-region integral theorem. -/
theorem original_q96_aggregate_real :
    (∑ i : Fin 14, (cellFloorNumerator i : ℝ) / (2 : ℝ) ^ 96) =
      (1222997719565324892497827 : ℝ) / (2 : ℝ) ^ 96 := by
  rw [← Finset.sum_div]
  have h := congrArg (fun z : ℤ => (z : ℝ)) original_q96_aggregate
  simpa [aggregateNumerator, historicalNumerator] using
    congrArg (fun x : ℝ => x / (2 : ℝ) ^ 96) h

end
end ImbalancedChen.P2OriginalSaving16OriginalArchive
