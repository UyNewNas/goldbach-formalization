import ImbalancedChen.P2OriginalSaving19Cell05AllRowArithmetic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The original Cell05 geometry, connected to its parser-bound coordinates.
This closes the saved vertex-value checks as well as the finite row checks.
The Q96 statements concern the geometry's Jensen records, not the distinct
moment-refinement records. No coverage or integral inequality is inferred.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell05GeometryCertificate

open scoped BigOperators
open P2OriginalSaving19Archive P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19Geometry05ScalableDecoding.Complete
open P2OriginalSaving19Geometry05ScalableShape
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19Cell05AllRowArithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable section

def vertexPoint (v : Fin 28) : QPoint :=
  fun j => (concreteGeometry05.vertices[v.val]!)[j.val]!

/-- Original saved vertex fields, with quantitative denominator bounds. -/
def VertexChecks (v : Fin 28) : Prop :=
  PhysicalQ (vertexPoint v) ∧
  (concreteGeometry05.vertexValues[v.val]!).gap = gapQ (vertexPoint v) ∧
  (∀ j : Fin 10,
    (concreteGeometry05.vertexValues[v.val]!).factors[j.val]! = factorsQ (vertexPoint v) j) ∧
  0 ≤ gapQ (vertexPoint v) ∧
  (∀ j : Fin 10, 53 / 13824 ≤ factorsQ (vertexPoint v) j)

instance (v : Fin 28) : Decidable (VertexChecks v) := by
  unfold VertexChecks
  infer_instance

theorem all_vertex_checks : ∀ v : Fin 28, VertexChecks v := by decide +kernel

/-- Row vertices are genuine members of the decoded original vertex array. -/
theorem row_vertex_is_original (r : Fin 56) (i : Fin 9) :
    ∃ v : Fin 28, boundedRowVertex05 r i = vertexPoint v := by
  let n := (concreteGeometry05.rows[r.val]!).vertexIds[i.val]!
  have hn : n < 28 := by
    have h := (all_rows r).2.2.2.1 i
    simpa only [vertex_count] using h
  refine ⟨⟨n, hn⟩, ?_⟩
  funext j
  exact boundedRowVertex05_eq_raw r i j

theorem row_gap_nonneg (r : Fin 56) (i : Fin 9) :
    0 ≤ gapQ (boundedRowVertex05 r i) := by
  obtain ⟨v, hv⟩ := row_vertex_is_original r i
  rw [hv]
  exact (all_vertex_checks v).2.2.2.1

theorem row_factor_lower (r : Fin 56) (i : Fin 9) (j : Fin 10) :
    53 / 13824 ≤ factorsQ (boundedRowVertex05 r i) j := by
  obtain ⟨v, hv⟩ := row_vertex_is_original r i
  rw [hv]
  exact (all_vertex_checks v).2.2.2.2 j

theorem row_volume_pos (r : Fin 56) : 0 < (boundedRow05 r).physicalVolume := by
  have h := all_bounded_row_data_checks r
  rw [h.2.2.2.1]
  exact div_pos (abs_pos.mpr h.1) (by exact_mod_cast Nat.factorial_pos 8)

theorem row_mean_gap_pos (r : Fin 56) : 0 < (boundedRow05 r).meanGap := by
  rw [(all_bounded_row_data_checks r).2.2.2.2.1]
  exact div_pos (all_row_gaps r).1 (by norm_num)

theorem row_mass_pos (r : Fin 56) : 0 < massOf (boundedRow05 r) :=
  mul_pos (row_volume_pos r) (row_mean_gap_pos r)

theorem row_mean_pos (r : Fin 56) (j : Fin 10) : 0 < meansOf (boundedRow05 r) j := by
  rw [(all_bounded_row_data_checks r).2.2.2.2.2.1 j]
  unfold computedMeanOf
  apply div_pos _ (by norm_num)
  have hs : 0 < ∑ i : Fin 9, factorsQ (boundedRowVertex05 r i) j := by
    apply Finset.sum_pos
    · intro i _
      exact lt_of_lt_of_le (by norm_num) (row_factor_lower r i j)
    · exact Finset.univ_nonempty
  have hw : 0 ≤ ∑ i : Fin 9,
      gapQ (boundedRowVertex05 r i) * factorsQ (boundedRowVertex05 r i) j := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (row_gap_nonneg r i)
      (le_trans (by norm_num) (row_factor_lower r i j))
  exact add_pos_of_pos_of_nonneg hs (div_nonneg hw (le_of_lt (all_row_gaps r).1))

theorem row_top_pos (r : Fin 56) (j : Fin 10) : 0 < topsOf (boundedRow05 r) j := by
  have h := (all_bounded_row_data_checks r).2.2.2.2.2.2.1 (0 : Fin 9) j
  exact lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num) (row_factor_lower r 0 j)) h

theorem row_jensen_pos (r : Fin 56) : 0 < (boundedRow05 r).jensenBound := by
  rw [(all_bounded_row_data_checks r).2.2.2.2.2.2.2.2.1]
  exact div_pos (mul_pos (by norm_num) (row_mass_pos r))
    (Finset.prod_pos (fun j _ => row_mean_pos r j))

/-- The original integer division is exactly rational floor at scale 2^bits. -/
theorem fixedNumerator_eq_rat_floor (bits : ℕ) (q : ℚ) :
    fixedNumerator bits q = ⌊q * (2 : ℚ) ^ bits⌋ := by
  have hq : q * (2 : ℚ) ^ bits =
      ((q.num * (2 : ℤ) ^ bits : ℤ) : ℚ) / (q.den : ℚ) := by
    calc
      _ = (q.num : ℚ) / (q.den : ℚ) * (2 : ℚ) ^ bits :=
        congrArg (fun x : ℚ => x * (2 : ℚ) ^ bits) (Rat.num_div_den q).symm
      _ = _ := by push_cast; ring
  rw [hq]
  unfold fixedNumerator
  have h := Int.floor_div_cast_of_nonneg (k := ℚ) (Int.natCast_nonneg q.den)
    (((q.num * (2 : ℤ) ^ bits : ℤ) : ℚ))
  simpa only [Int.floor_intCast, Int.cast_natCast] using h.symm

/-- Both sides of the floor interval; the strict upper error is one unit. -/
theorem roundDownQ_interval (bits : ℕ) (q : ℚ) :
    roundDownQ bits q ≤ q ∧ q < roundDownQ bits q + 1 / (2 : ℚ) ^ bits := by
  have hp : (0 : ℚ) < (2 : ℚ) ^ bits := pow_pos (by norm_num) _
  unfold roundDownQ
  rw [fixedNumerator_eq_rat_floor]
  constructor
  · exact (div_le_iff₀ hp).2 (Int.floor_le _)
  · have h := Int.lt_floor_add_one (q * (2 : ℚ) ^ bits)
    have h' := (lt_div_iff₀ hp).2 h
    simpa only [add_div] using h'

def rowJensenFloor (r : Fin 56) : ℚ :=
  ((boundedRow05 r).jensenFloorQ96 : ℚ) / (2 : ℚ) ^ 96

theorem row_jensen_floor_interval (r : Fin 56) :
    rowJensenFloor r ≤ (boundedRow05 r).jensenBound ∧
    (boundedRow05 r).jensenBound < rowJensenFloor r + 1 / (2 : ℚ) ^ 96 := by
  have h := all_bounded_row_data_checks r
  simpa only [rowJensenFloor, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2,
    oldFloorQ96, roundDownQ] using
    roundDownQ_interval 96 (oldEvaluator (massOf (boundedRow05 r)) (meansOf (boundedRow05 r)))

/-- The accumulated rounding loss is strictly less than 56 Q96 units. -/
theorem cell_jensen_floor_interval :
    (∑ r : Fin 56, rowJensenFloor r) ≤ ∑ r : Fin 56, (boundedRow05 r).jensenBound ∧
    (∑ r : Fin 56, (boundedRow05 r).jensenBound) <
      (∑ r : Fin 56, rowJensenFloor r) + 56 / (2 : ℚ) ^ 96 := by
  constructor
  · exact Finset.sum_le_sum (fun r _ => (row_jensen_floor_interval r).1)
  · have h := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 56)))
      Finset.univ_nonempty (fun r _ => (row_jensen_floor_interval r).2)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one_div, Nat.cast_ofNat] using h

/-- A single closed certificate for the original bytes, finite shape,
saved vertex fields, and all 56 ten-clause geometry row checks. -/
theorem original_geometry_certificate :
    (SourceJson.parse (String.ofList geometryPacked05.toList) >>= decodeGeometry) =
      .ok concreteGeometry05 ∧
    GeometryShape concreteGeometry05 ∧
    (∀ v : Fin 28, VertexChecks v) ∧
    (∀ r : Fin 56, RowDataChecksFor (boundedRowVertex05 r) (boundedRow05 r)) :=
  ⟨geometryPacked05_parse_decode, concreteGeometry05_shape,
    all_vertex_checks, all_bounded_row_data_checks⟩

#print axioms original_geometry_certificate
#print axioms row_mass_pos
#print axioms row_mean_pos
#print axioms row_top_pos
#print axioms row_jensen_pos
#print axioms row_jensen_floor_interval
#print axioms cell_jensen_floor_interval

end
end ImbalancedChen.P2OriginalSaving19Cell05GeometryCertificate
