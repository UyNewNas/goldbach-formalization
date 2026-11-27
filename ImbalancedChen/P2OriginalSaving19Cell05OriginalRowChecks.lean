import ImbalancedChen.P2OriginalSaving19Cell05GeometryCertificate
import ImbalancedChen.P2OriginalSaving19RowNumericsPureBridge

/-!
Connect the closed Cell05 finite certificate to the existing analytic
RowNumerics interface. The original coordinates, ordering, volume, means,
maxima and Q96 evaluator are retained by definitional equality.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell05OriginalRowChecks

open P2OriginalSaving19Archive
open P2OriginalSaving19Geometry05ScalableDecoding.Complete
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19Cell05AllRowArithmetic
open P2OriginalSaving19Cell05GeometryCertificate

noncomputable section

theorem all_bounded_original_row_checks (r : Fin 56) :
    P2OriginalSaving19RowNumerics.RowDataChecksFor (boundedRowVertex05 r) (boundedRow05 r) :=
  (P2OriginalSaving19RowNumericsPureBridge.rowDataChecksFor_iff_original _ _).mp
    (all_bounded_row_data_checks r)

def rowVertices (g : Geometry) (r : Fin 56) (i : Fin 9) (j : Fin 8) : ℚ :=
  (g.vertices[(g.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!

theorem all_raw_original_row_checks (r : Fin 56) :
    P2OriginalSaving19RowNumerics.RowDataChecksFor
      (rowVertices concreteGeometry05 r) (concreteGeometry05.rows[r.val]!) :=
  (P2OriginalSaving19RowNumericsPureBridge.rowDataChecksFor_iff_original _ _).mp
    (all_raw_row_data_checks r)

/-- An archive consumer decoding the same original text gets exactly the
certified geometry. Neither a fallback value nor a stored hash is a premise. -/
theorem original_decode_unique (g : Geometry)
    (hg : (SourceJson.parse (String.ofList geometryPacked05.toList) >>= decodeGeometry) = .ok g) :
    g = concreteGeometry05 := by
  have h : (Except.ok g : Except String Geometry) = .ok concreteGeometry05 :=
    hg.symm.trans geometryPacked05_parse_decode
  exact Except.ok.inj h

theorem row_checks_of_original_decode (g : Geometry)
    (hg : (SourceJson.parse (String.ofList geometryPacked05.toList) >>= decodeGeometry) = .ok g)
    (r : Fin 56) :
    P2OriginalSaving19RowNumerics.RowDataChecksFor (rowVertices g r) (g.rows[r.val]!) := by
  rw [original_decode_unique g hg]
  exact all_raw_original_row_checks r

theorem original_vertex_gap (v : Fin 28) :
    (concreteGeometry05.vertexValues[v.val]!).gap =
      P2OriginalSaving19Original28918.gapQ (vertexPoint v) :=
  (all_vertex_checks v).2.1

theorem original_vertex_factors (v : Fin 28) (j : Fin 10) :
    (concreteGeometry05.vertexValues[v.val]!).factors[j.val]! =
      P2OriginalSaving19Original28918.factorsQ (vertexPoint v) j :=
  (all_vertex_checks v).2.2.1 j

theorem original_parse_shape_and_row_checks :
    (SourceJson.parse (String.ofList geometryPacked05.toList) >>= decodeGeometry) =
      .ok concreteGeometry05 ∧
    P2OriginalSaving19Geometry05ScalableShape.GeometryShape concreteGeometry05 ∧
    (∀ r : Fin 56, P2OriginalSaving19RowNumerics.RowDataChecksFor
      (rowVertices concreteGeometry05 r) (concreteGeometry05.rows[r.val]!)) :=
  ⟨geometryPacked05_parse_decode,
    P2OriginalSaving19Geometry05ScalableShape.concreteGeometry05_shape,
    all_raw_original_row_checks⟩

#print axioms all_bounded_original_row_checks
#print axioms all_raw_original_row_checks
#print axioms original_decode_unique
#print axioms row_checks_of_original_decode
#print axioms original_vertex_gap
#print axioms original_vertex_factors
#print axioms original_parse_shape_and_row_checks

end
end ImbalancedChen.P2OriginalSaving19Cell05OriginalRowChecks
