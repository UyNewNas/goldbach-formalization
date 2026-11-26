import ImbalancedChen.P2OriginalSaving19ArchiveCore
import ImbalancedChen.P2OriginalSaving19Geometry01ArchiveBridge
import ImbalancedChen.P2OriginalSaving19Moment01Decoded
import ImbalancedChen.P2OriginalSaving19Cell01AllOriginalFloorBridge

/-!
SOURCE CANDIDATE / NOT COMPILED. Exact cell01 transport to ArchiveCore.
The existing Geometry01ArchiveBridge supplies geometry_one unchanged.
The existing original Moment01 decoder supplies the moment alias below.
The all144 original-floor family supplies both the five original floor
clauses and the ten Q80 double bounds. No parser or numeric check is rerun.

All selectors retain the original dependent cell/row index, the original
nine-vertex order and every original array lookup. The coordinate and moment
equalities bind these selectors to the bounded concrete cell01 interface.
This owner makes no other-cell, ownership or integral claim.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01ArchiveBridge

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19MomentFloorConsumer (OriginalRowIndex originalRowCount)
open P2OriginalSaving19Geometry01Decoding (concreteGeometry01)
open P2OriginalSaving19Geometry01ArchiveBridge (geometry_one)
open P2OriginalSaving19Moment01Decoding (momentConcrete01 momentPacked01_parse_decode)
open P2OriginalSaving19RowNumericsPure (gapQ factorsQ topsOf)
open P2OriginalSaving19OriginalFloorTransport (OriginalFloorChecksFor OriginalQ80BoundsFor)
open P2OriginalSaving19Cell01OriginalFloorInterface
  (rawGeometryRow rawMomentRow rawVertices rawOriginalMoments)

theorem momentChars_one :
    momentChars (1 : Fin 13) = momentPacked01.toList := by rfl

theorem momentText_one :
    momentText (1 : Fin 13) = String.ofList momentPacked01.toList :=
  congrArg String.ofList momentChars_one

theorem momentParse_one :
    momentParse (1 : Fin 13) = .ok momentConcrete01 := by
  change (SourceJson.parse (String.ofList momentPacked01.toList) >>= decodeMoments) =
    .ok momentConcrete01
  exact momentPacked01_parse_decode

theorem moments_one : moments (1 : Fin 13) = momentConcrete01 :=
  congrArg (fun result : Except String Moments => result.toOption.getD default)
    momentParse_one

/-- Cell01 retains its original 144 ordinals inside the original dependent family. -/
def cell01RowIndex (r : Fin 144) : OriginalRowIndex := ⟨1, r⟩

noncomputable def archiveGeometryRow (r : OriginalRowIndex) : GeometryRow :=
  (geometry r.1).rows[r.2.val]!

noncomputable def archiveMomentRow (r : OriginalRowIndex) : MomentRecord :=
  (moments r.1).rows[r.2.val]!

noncomputable def archiveRawVertex (r : OriginalRowIndex) (i : Fin 9) (j : Fin 8) : ℚ :=
  ((geometry r.1).vertices[(archiveGeometryRow r).vertexIds[i.val]!]!)[j.val]!

noncomputable def archiveOriginalMoments (r : OriginalRowIndex)
    (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19HigherMoments.rationalMoment
    (fun i => gapQ (archiveRawVertex r i))
    (fun i => 1 - factorsQ (archiveRawVertex r i) j / topsOf (archiveGeometryRow r) j) k

theorem archiveGeometryRow_one (r : Fin 144) :
    archiveGeometryRow (cell01RowIndex r) = rawGeometryRow r := by
  change (geometry (1 : Fin 13)).rows[r.val]! = concreteGeometry01.rows[r.val]!
  rw [geometry_one]

theorem archiveMomentRow_one (r : Fin 144) :
    archiveMomentRow (cell01RowIndex r) = rawMomentRow r := by
  change (moments (1 : Fin 13)).rows[r.val]! = momentConcrete01.rows[r.val]!
  rw [moments_one]

theorem archiveRawVertex_one (r : Fin 144) :
    archiveRawVertex (cell01RowIndex r) = rawVertices r := by
  funext i j
  simp only [archiveRawVertex, archiveGeometryRow, cell01RowIndex,
    geometry_one, rawVertices, rawGeometryRow]

theorem archiveOriginalMoments_one (r : Fin 144) :
    archiveOriginalMoments (cell01RowIndex r) = rawOriginalMoments r := by
  funext j k
  simp only [archiveOriginalMoments, archiveRawVertex_one,
    archiveGeometryRow_one, rawOriginalMoments, topsOf]

/-- Exact original five-clause formula, including max(old, uncapped new). -/
theorem all_original_archive_floor_formula (r : Fin 144) :
    OriginalFloorChecksFor (archiveGeometryRow (cell01RowIndex r))
      (archiveMomentRow (cell01RowIndex r))
      (archiveOriginalMoments (cell01RowIndex r)) := by
  rw [archiveGeometryRow_one, archiveMomentRow_one, archiveOriginalMoments_one]
  exact P2OriginalSaving19Cell01AllOriginalFloorBridge.all_original_floor_formula r

/-- Both original Q80 inequalities for every original factor. -/
theorem all_original_archive_Q80_bounds (r : Fin 144) :
    OriginalQ80BoundsFor (archiveMomentRow (cell01RowIndex r))
      (archiveOriginalMoments (cell01RowIndex r)) := by
  rw [archiveMomentRow_one, archiveOriginalMoments_one]
  exact P2OriginalSaving19Cell01AllOriginalFloorBridge.all_original_Q80_bounds r

theorem all_original_archive_floor_and_bounds (r : Fin 144) :
    OriginalFloorChecksFor (archiveGeometryRow (cell01RowIndex r))
      (archiveMomentRow (cell01RowIndex r))
      (archiveOriginalMoments (cell01RowIndex r)) ∧
    OriginalQ80BoundsFor (archiveMomentRow (cell01RowIndex r))
      (archiveOriginalMoments (cell01RowIndex r)) :=
  ⟨all_original_archive_floor_formula r, all_original_archive_Q80_bounds r⟩

/-- The same formula at the actual original Archive cell-one selectors. -/
theorem all_original_archive_floor_formula_at_one
    (r : Fin (originalRowCount (1 : Fin 13))) :
    OriginalFloorChecksFor ((geometry (1 : Fin 13)).rows[r.val]!)
      ((moments (1 : Fin 13)).rows[r.val]!)
      (archiveOriginalMoments ⟨(1 : Fin 13), r⟩) := by
  exact all_original_archive_floor_formula r

theorem all_original_archive_Q80_bounds_at_one
    (r : Fin (originalRowCount (1 : Fin 13))) :
    OriginalQ80BoundsFor ((moments (1 : Fin 13)).rows[r.val]!)
      (archiveOriginalMoments ⟨(1 : Fin 13), r⟩) := by
  exact all_original_archive_Q80_bounds r

#print axioms momentChars_one
#print axioms momentText_one
#print axioms momentParse_one
#print axioms moments_one
#print axioms archiveGeometryRow_one
#print axioms archiveMomentRow_one
#print axioms archiveRawVertex_one
#print axioms archiveOriginalMoments_one
#print axioms all_original_archive_floor_formula
#print axioms all_original_archive_Q80_bounds
#print axioms all_original_archive_floor_and_bounds
#print axioms all_original_archive_floor_formula_at_one
#print axioms all_original_archive_Q80_bounds_at_one

end ImbalancedChen.P2OriginalSaving19Cell01ArchiveBridge

