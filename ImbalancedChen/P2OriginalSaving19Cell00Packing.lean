import ImbalancedChen.P2OriginalSaving19RationalAffineSeparator
import ImbalancedChen.P2OriginalSaving19Cell00PhysicalMomentRow
import ImbalancedChen.P2OriginalSaving19Cell00SeparationComplete

/-! Candidate physical packing of the original 56 Cell00 simplices.
No source-domain inclusion or global selected-saving endpoint is assumed. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00Packing
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19Cell00PhysicalMomentRow
open P2OriginalSaving19RationalAffineSeparator

theorem ordered_intersection_null (r s : Fin 56) (hrs : r < s) :
    volume (physicalSimplex r ∩ physicalSimplex s) = 0 := by
  have hc := P2OriginalSaving19Cell00Separation.all_pairs r s hrs
  apply separated_intersection_null (P2OriginalSaving19Cell00Separation.separator r s)
    (row r).linear (row s).linear (row r).base (row s).base hc.1
  · intro i
    rw [simplex_vertices, eval_cast]
    exact_mod_cast hc.2.1 i
  · intro i
    rw [simplex_vertices, eval_cast]
    exact_mod_cast hc.2.2 i

theorem pairwise_aedisjoint : Pairwise (fun r s : Fin 56 =>
    AEDisjoint volume (physicalSimplex r) (physicalSimplex s)) := by
  intro r s hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ordered_intersection_null r s hlt
  · change volume (physicalSimplex r ∩ physicalSimplex s) = 0
    rw [inter_comm]
    exact ordered_intersection_null s r hgt

theorem simplex_density_integrable (r : Fin 56) :
    IntegrableOn conservativeDensity (physicalSimplex r) := by
  have h := (simplex_reciprocal_integrable (row r).linear (row r).base
    (row r).physicalVertices).const_mul 4
  apply h.congr
  filter_upwards with t
  rw [density_factor_dictionary, mul_div_assoc]

def physicalUnion : Set Point := ⋃ r : Fin 56, physicalSimplex r

theorem union_density_integrable : IntegrableOn conservativeDensity physicalUnion :=
  integrableOn_finite_iUnion.mpr simplex_density_integrable

theorem union_integral_eq_sum :
    (∫ t in physicalUnion, conservativeDensity t) =
      ∑ r : Fin 56, ∫ t in physicalSimplex r, conservativeDensity t := by
  have h := integral_iUnion_ae
    (fun r : Fin 56 => (support_measurable (row r).linear (row r).base).nullMeasurableSet)
    pairwise_aedisjoint union_density_integrable
  simpa only [tsum_fintype, physicalUnion, physicalSimplex] using h

theorem stored_sum_le_union_integral :
    (∑ r : Fin 56,
      ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ)) ≤
      ∫ t in physicalUnion, conservativeDensity t := by
  rw [union_integral_eq_sum]
  exact sum_stored_floor_bound

#print axioms pairwise_aedisjoint
#print axioms union_integral_eq_sum
#print axioms stored_sum_le_union_integral
end
end ImbalancedChen.P2OriginalSaving19Cell00Packing
