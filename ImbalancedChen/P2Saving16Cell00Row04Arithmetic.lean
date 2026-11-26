import ImbalancedChen.P2OriginalSaving16FiniteCore
import ImbalancedChen.P2Saving16Cell00TypedPayload
import ImbalancedChen.P2Saving16Cell00StoredFloors
import ImbalancedChen.P2Winner9FastDetPure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Candidate arithmetic for the fifth original saving16 cell00 simplex.
The record and its ordered vertices come from the named typed payload
through the unchanged `simplexVertices` definition. No decoder, point
literal, determinant algorithm, geometric formula or floor is replaced.

The original `Matrix.det` specification is rewritten using the existing,
unchanged generic FastDetPure theorem. Separate closed obligations check
volume, mean gap, all ten weighted means, and the stored-field Jensen
expression. The already checked stored floor is reused by equality.

The core retains both residual factors, all eight coordinate factors,
the density multiplier 4, the geometric volume divisor 8!, and the
nine-vertex/second-moment divisors 9 and 10. Their manuscript provenance
is recorded in MANIFEST.json; this module proves no source-cell membership,
pulling ownership, original-text decode, all-cell guard or integral bound.
-/
namespace ImbalancedChen.P2Saving16Cell00Row04Arithmetic

open P2OriginalSaving16OriginalArchive
  (SimplexRecord QPoint simplexVertices edgeMatrix physicalVolumeQ
    gapTotalQ meansQ jensenQ simplexValid)
open P2OriginalSaving16JensenFloor (q96Floor)
open P2Saving16Cell00TypedPayload (cell00Payload simplex04)
open scoped BigOperators

set_option Elab.async false

noncomputable section

def row : SimplexRecord := simplex04

def vertices : Fin 9 → QPoint := simplexVertices cell00Payload row

theorem row_eq : cell00Payload.simplices[(4 : Fin 8)] = row := by
  rfl

/-- Reuse the accepted finite shape facts for this exact row. -/
theorem row_shape :
    row.simplexId = 4 ∧ row.vertexIds.size = 9 ∧
    (∀ k : Fin 9, row.vertexIds.getD k.val 0 < cell00Payload.vertices.size) ∧
    row.gapWeightedMeans.size = 10 := by
  exact P2Saving16Cell00StoredFloors.cell00_simplex_shape (4 : Fin 8)

/-- The first new closed computational obligation: the same exact 8 by 8
matrix and the same physical simplex volume. -/
theorem volume_eq : row.physicalVolume = physicalVolumeQ vertices := by
  change row.physicalVolume = |(edgeMatrix vertices).det| / (Nat.factorial 8 : ℚ)
  rw [← P2Winner9FastDetPure.fastDet_eq (edgeMatrix vertices)]
  decide +kernel

#print axioms volume_eq

theorem stored_volume_pos : 0 < row.physicalVolume := by
  decide +kernel

theorem physical_volume_pos : 0 < physicalVolumeQ vertices :=
  volume_eq ▸ stored_volume_pos

theorem mean_gap_eq : row.meanGap = gapTotalQ vertices / 9 := by
  decide +kernel

#print axioms mean_gap_eq

theorem stored_mean_gap_pos : 0 < row.meanGap := by
  decide +kernel

theorem gap_total_pos : 0 < gapTotalQ vertices := by
  have h : 0 < gapTotalQ vertices / 9 := mean_gap_eq ▸ stored_mean_gap_pos
  exact (div_pos_iff_of_pos_right (by norm_num : (0 : ℚ) < 9)).1 h

/-- Both residual means and all eight coordinate means are included. -/
theorem ten_means_eq :
    ∀ j : Fin 10, row.gapWeightedMeans.getD j.val 0 = meansQ vertices j := by
  decide +kernel

#print axioms ten_means_eq

/-- Check the stored rational fields against their complete Jensen
multiplication/division expression without recomputing the geometry. -/
theorem stored_jensen_expression :
    row.jensenBound =
      4 * row.physicalVolume * row.meanGap /
        ∏ j : Fin 10, row.gapWeightedMeans.getD j.val 0 := by
  decide +kernel

#print axioms stored_jensen_expression

/-- Compose previously certified expressions; no combined decision. -/
theorem jensen_eq : row.jensenBound = jensenQ vertices := by
  unfold jensenQ
  apply stored_jensen_expression.trans
  exact congrArg₂ (fun numerator denominator : ℚ => numerator / denominator)
    (congrArg₂ (fun volume mean : ℚ => 4 * volume * mean) volume_eq mean_gap_eq)
    (Finset.prod_congr rfl (fun j _ => ten_means_eq j))

/-- Reuse the existing stored floor, retaining the original Q96 function. -/
theorem jensen_floor_eq : row.jensenFloor = q96Floor (jensenQ vertices) := by
  exact (P2Saving16Cell00StoredFloors.simplex04_stored_jensen_floor).trans
    (congrArg q96Floor jensen_eq)

/-- The complete unchanged eleven-conjunct operation guard for row04. -/
theorem simplex_valid : simplexValid cell00Payload (4 : Fin 8) := by
  change row.simplexId = 4 ∧ row.vertexIds.size = 9 ∧
    (∀ k : Fin 9, row.vertexIds.getD k.val 0 < cell00Payload.vertices.size) ∧
    0 < physicalVolumeQ vertices ∧ 0 < gapTotalQ vertices ∧
    row.physicalVolume = physicalVolumeQ vertices ∧ row.meanGap = gapTotalQ vertices / 9 ∧
    row.gapWeightedMeans.size = 10 ∧
    (∀ j : Fin 10, row.gapWeightedMeans.getD j.val 0 = meansQ vertices j) ∧
    row.jensenBound = jensenQ vertices ∧ row.jensenFloor = q96Floor (jensenQ vertices)
  exact ⟨row_shape.1, row_shape.2.1, row_shape.2.2.1,
    physical_volume_pos, gap_total_pos, volume_eq, mean_gap_eq,
    row_shape.2.2.2, ten_means_eq, jensen_eq, jensen_floor_eq⟩

#print axioms jensen_eq
#print axioms jensen_floor_eq
#print axioms simplex_valid

end
end ImbalancedChen.P2Saving16Cell00Row04Arithmetic
