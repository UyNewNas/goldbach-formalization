import ImbalancedChen.P2OriginalSaving19OriginalFloorTransport
import ImbalancedChen.P2OriginalSaving19Geometry01BoundedAccess
import ImbalancedChen.P2OriginalSaving19Moment01Shape

/-!
SOURCE CANDIDATE / NOT COMPILED. The original cell01 row interface, with
Fin 144 rows, the original ordered Fin 9 vertices and all Fin 8 coordinates.
Only already proved shape/access equalities are reused here. No floor claim
for any row, block, cell or integral is supplied by this interface.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface

set_option maxRecDepth 1000000
set_option Elab.async false

open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19Geometry01Decoding
open P2OriginalSaving19Moment01Decoding
open P2OriginalSaving19OriginalFloorTransport

noncomputable def rawGeometryRow (r : Fin 144) : GeometryRow :=
  concreteGeometry01.rows[r.val]!

noncomputable def rawMomentRow (r : Fin 144) : MomentRecord :=
  momentConcrete01.rows[r.val]!

noncomputable def rawVertices (r : Fin 144) (i : Fin 9) (j : Fin 8) : ℚ :=
  (concreteGeometry01.vertices[(rawGeometryRow r).vertexIds[i.val]!]!)[j.val]!

noncomputable def rawOriginalMoments (r : Fin 144) (j : Fin 10) (k : Nat) : ℚ :=
  P2OriginalSaving19HigherMoments.rationalMoment
    (fun i => gapQ (rawVertices r i))
    (fun i => 1 - factorsQ (rawVertices r i) j / (rawGeometryRow r).factorMaxima[j.val]!) k

/-- The five original checker clauses and both Q80 inequalities for all ten
factors. Saved new Q96 remains max(old, uncapped new) inside the five clauses. -/
def OriginalFloorAndBoundsAt (r : Fin 144) : Prop :=
  OriginalFloorChecksFor (rawGeometryRow r) (rawMomentRow r) (rawOriginalMoments r) ∧
    OriginalQ80BoundsFor (rawMomentRow r) (rawOriginalMoments r)

theorem raw_original_moments_eq_transport (r : Fin 144) :
    rawOriginalMoments r = originalMoments (rawVertices r) (rawGeometryRow r) := rfl

theorem raw_geometry_row_no_fallback (r : Fin 144) :
    rawGeometryRow r = P2OriginalSaving19Geometry01BoundedAccess.boundedRow r :=
  P2OriginalSaving19Geometry01BoundedAccess.row_lookup_no_fallback r

theorem raw_moment_row_no_fallback (r : Fin 144) :
    rawMomentRow r = momentConcrete01.rows[r.val]'(P2OriginalSaving19Moment01Shape.row_bound r) :=
  P2OriginalSaving19Moment01Shape.row_lookup_no_fallback r

theorem raw_vertex_no_fallback (r : Fin 144) (i : Fin 9) (j : Fin 8) :
    rawVertices r i j = P2OriginalSaving19Geometry01BoundedAccess.boundedRowVertex r i j :=
  P2OriginalSaving19Geometry01BoundedAccess.raw_vertex_no_fallback r i j

theorem raw_factor_maximum_no_fallback (r : Fin 144) (j : Fin 10) :
    (rawGeometryRow r).factorMaxima[j.val]! =
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow r).factorMaxima[j.val]'
        (P2OriginalSaving19Geometry01BoundedAccess.factor_maximum_bound r j) :=
  P2OriginalSaving19Geometry01BoundedAccess.factor_maximum_lookup_no_fallback r j

theorem raw_weighted_mean_no_fallback (r : Fin 144) (j : Fin 10) :
    (rawGeometryRow r).gapWeightedMeans[j.val]! =
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow r).gapWeightedMeans[j.val]'
        (P2OriginalSaving19Geometry01BoundedAccess.weighted_mean_bound r j) :=
  P2OriginalSaving19Geometry01BoundedAccess.weighted_mean_lookup_no_fallback r j

theorem raw_factor_Q80_bound (r : Fin 144) (j : Fin 10) :
    j.val < (rawMomentRow r).factorFloorsQ80.size := by
  have hs : (rawMomentRow r).factorFloorsQ80.size = 10 :=
    (P2OriginalSaving19Moment01Shape.row_ids_and_floor_sizes r).2
  rw [hs]
  exact j.isLt

theorem raw_factor_Q80_no_fallback (r : Fin 144) (j : Fin 10) :
    (rawMomentRow r).factorFloorsQ80[j.val]! =
      (rawMomentRow r).factorFloorsQ80[j.val]'(raw_factor_Q80_bound r j) :=
  getElem!_pos (rawMomentRow r).factorFloorsQ80 j.val (raw_factor_Q80_bound r j)

#print axioms raw_original_moments_eq_transport
#print axioms raw_geometry_row_no_fallback
#print axioms raw_moment_row_no_fallback
#print axioms raw_vertex_no_fallback
#print axioms raw_factor_maximum_no_fallback
#print axioms raw_weighted_mean_no_fallback
#print axioms raw_factor_Q80_bound
#print axioms raw_factor_Q80_no_fallback

end ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface
