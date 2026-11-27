import ImbalancedChen.P2OriginalSaving19RationalAffineSeparator
import ImbalancedChen.P2OriginalSaving19Cell01PhysicalMomentRow
import ImbalancedChen.P2OriginalSaving19Cell01GroupedSeparationComplete

/-! Candidate physical packing of the original 144 Cell01 simplices.
No source-domain inclusion or global selected-saving endpoint is assumed. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Packing
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19Cell01PhysicalMomentRow
open P2OriginalSaving19RationalAffineSeparator

theorem pairwise_aedisjoint : Pairwise (fun r s : Fin 144 =>
    AEDisjoint volume (physicalSimplex r) (physicalSimplex s)) :=
  P2OriginalSaving19Cell01GroupedSeparation.all_original_pairs

theorem simplex_density_integrable (r : Fin 144) :
    IntegrableOn conservativeDensity (physicalSimplex r) := by
  have h := (simplex_reciprocal_integrable (row r).linear (row r).base
    (row r).physicalVertices).const_mul 4
  apply h.congr
  filter_upwards with t
  rw [density_factor_dictionary, mul_div_assoc]

def physicalUnion : Set Point := ⋃ r : Fin 144, physicalSimplex r

theorem union_density_integrable : IntegrableOn conservativeDensity physicalUnion :=
  integrableOn_finite_iUnion.mpr simplex_density_integrable

theorem union_integral_eq_sum :
    (∫ t in physicalUnion, conservativeDensity t) =
      ∑ r : Fin 144, ∫ t in physicalSimplex r, conservativeDensity t := by
  have h := integral_iUnion_ae
    (fun r : Fin 144 => (support_measurable (row r).linear (row r).base).nullMeasurableSet)
    pairwise_aedisjoint union_density_integrable
  simpa only [tsum_fintype, physicalUnion, physicalSimplex] using h

theorem stored_sum_le_union_integral :
    (∑ r : Fin 144,
      ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ)) ≤
      ∫ t in physicalUnion, conservativeDensity t := by
  rw [union_integral_eq_sum]
  exact sum_stored_floor_bound

#print axioms pairwise_aedisjoint
#print axioms union_integral_eq_sum
#print axioms stored_sum_le_union_integral
end
end ImbalancedChen.P2OriginalSaving19Cell01Packing
