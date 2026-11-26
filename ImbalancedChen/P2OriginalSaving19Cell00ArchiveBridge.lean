import ImbalancedChen.P2OriginalSaving19ArchiveCore
import ImbalancedChen.P2OriginalSaving19Geometry00PackedDecoded
import ImbalancedChen.P2OriginalSaving19Moment00Decoded
import ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge

/-!
SOURCE CANDIDATE, NOT COMPILED OR ACCEPTED. Exact cell00 transport to the
current ArchiveCore aliases. This new owner requires its own normal and
independent kernel receipts; imported receipt status is not asserted here.

The complete direct source dependency boundary is the four imports above:
* ArchiveCore owns the original schemas/decoders, original row-index shape,
  and the maps of all 26 separately quoted original packed inputs.
* Geometry00PackedDecoded supplies geometryPacked00_parse_decode through
  Geometry00Decoded and GeometryPackedParseTransport00.
* Moment00Decoded supplies momentPacked00_parse_decode through
  Moment00DecodeFromRows and Moment00DecodedBlock013.
* Cell00AllOriginalFloorBridge supplies all_original_raw_floor_formula
  through all 56 prefix row certificates, HigherMomentsPrefix, and the
  original Q96 arithmetic namespace bridge.
Their transitive source dependencies are retained unchanged. Only the two
cell00 parse results are used; no parser or numerical certificate is rerun.

The local selectors below reproduce the original archive row, moment-row,
and three-level physical-coordinate access on the original OriginalRowIndex.
They avoid importing the older Archive/Original28918FloorBinding monolith,
which redeclares ArchiveCore's names and contains whole-archive obligations.
The final theorem is the original floor formula at the actual cell00
Archive indices, for r : Fin 56. No all-cell or integral claim is made.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell00ArchiveBridge

set_option maxRecDepth 1000000
set_option Elab.async false

open P2OriginalSaving19Archive
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19Geometry00Decoding
open P2OriginalSaving19Moment00Decoding
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Cell00AllOriginalFloorBridge

theorem geometryParse_zero :
    geometryParse (0 : Fin 13) = .ok concreteGeometry00 := by
  change (SourceJson.parse (String.ofList geometryPacked00.toList) >>= decodeGeometry) =
    .ok concreteGeometry00
  exact geometryPacked00_parse_decode

theorem momentParse_zero :
    momentParse (0 : Fin 13) = .ok momentConcrete00 := by
  change (SourceJson.parse (String.ofList momentPacked00.toList) >>= decodeMoments) =
    .ok momentConcrete00
  exact momentPacked00_parse_decode

theorem geometry_zero : geometry (0 : Fin 13) = concreteGeometry00 := by
  exact congrArg (fun result : Except String Geometry => result.toOption.getD default)
    geometryParse_zero

theorem moments_zero : moments (0 : Fin 13) = momentConcrete00 := by
  exact congrArg (fun result : Except String Moments => result.toOption.getD default)
    momentParse_zero

/-- The original dependent archive index, restricted to its 56 cell00 rows. -/
def cell00RowIndex (r : Fin 56) : OriginalRowIndex := ⟨0, r⟩

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

theorem archiveGeometryRow_zero (r : Fin 56) :
    archiveGeometryRow (cell00RowIndex r) = concreteGeometry00.rows[r.val]! := by
  change (geometry (0 : Fin 13)).rows[r.val]! = concreteGeometry00.rows[r.val]!
  rw [geometry_zero]

theorem archiveMomentRow_zero (r : Fin 56) :
    archiveMomentRow (cell00RowIndex r) = momentConcrete00.rows[r.val]! := by
  change (moments (0 : Fin 13)).rows[r.val]! = momentConcrete00.rows[r.val]!
  rw [moments_zero]

theorem archiveRawVertex_zero (r : Fin 56) :
    archiveRawVertex (cell00RowIndex r) = rawVertices r := by
  funext i j
  simp only [archiveRawVertex, archiveGeometryRow, cell00RowIndex, geometry_zero, rawVertices]

theorem archiveOriginalMoments_zero (r : Fin 56) :
    archiveOriginalMoments (cell00RowIndex r) = rawOriginalMoments r := by
  funext j k
  simp only [archiveOriginalMoments, archiveRawVertex_zero,
    archiveGeometryRow_zero, rawOriginalMoments]

theorem all_original_archive_floor_formula (r : Fin 56) :
    OriginalFloorChecksFor (archiveGeometryRow (cell00RowIndex r))
      (archiveMomentRow (cell00RowIndex r))
      (archiveOriginalMoments (cell00RowIndex r)) := by
  rw [archiveGeometryRow_zero, archiveMomentRow_zero, archiveOriginalMoments_zero]
  exact all_original_raw_floor_formula r

/-- The same theorem with the actual archive cell and row accesses exposed. -/
theorem all_original_archive_floor_formula_at_zero
    (r : Fin (originalRowCount (0 : Fin 13))) :
    OriginalFloorChecksFor ((geometry (0 : Fin 13)).rows[r.val]!)
      ((moments (0 : Fin 13)).rows[r.val]!)
      (archiveOriginalMoments ⟨(0 : Fin 13), r⟩) := by
  exact all_original_archive_floor_formula r

#print axioms geometryParse_zero
#print axioms momentParse_zero
#print axioms geometry_zero
#print axioms moments_zero
#print axioms archiveGeometryRow_zero
#print axioms archiveMomentRow_zero
#print axioms archiveRawVertex_zero
#print axioms archiveOriginalMoments_zero
#print axioms all_original_archive_floor_formula
#print axioms all_original_archive_floor_formula_at_zero

end ImbalancedChen.P2OriginalSaving19Cell00ArchiveBridge
