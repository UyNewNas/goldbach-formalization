import ImbalancedChen.P2Winner9CanonicalCurvatureMoment
import ImbalancedChen.P2Winner9PhysicalCurvatureProbability
import ImbalancedChen.P2Winner9Row22Rounding
import ImbalancedChen.P2Winner9SelectedRowT10

/-! The original directed curvature floors for the two physical Winner9 rows. -/

namespace ImbalancedChen.P2Winner9SelectedRowCurvatureFloor

noncomputable section

open MeasureTheory
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CanonicalCurvatureMoment
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedPhysicalMeans
open ImbalancedChen.P2Winner9SelectedPhysicalMoments
open ImbalancedChen.P2Winner9ActualRowProbability
open ImbalancedChen.P2Winner9PhysicalConstantCurvature
open ImbalancedChen.P2Winner9PhysicalCurvatureProbability
open ImbalancedChen.P2Winner9SelectedRowT10
open ImbalancedChen.P2Winner9PhysicalAffineTransfer

theorem physical_transverse_term (r : Fin 2) (j : Fin 10) :
    (∫ z, (B r j z)^2 ∂ν r) / (2 * (V r j)^2 * (upper r : ℝ)^10) =
      (value (transverse (data r) j) : ℝ) := by
  rw [weighted_integral]
  change ((∫ z in sourceSupport (vertices r), physicalGap z *
      (physicalDeviation (fun i => (means r i : ℝ)) j z)^2) / gapMass r) / _ = _
  rw [physical_weighted_deviation_sq, canonicalSupport, actualWeightedDeviationSquare_eq,
    V_typed, show (upper r : ℝ) = _ from U_typed r, transverse_value]
  push_cast
  have hL : (0 : ℝ) < ((data r).L : ℝ) := by exact_mod_cast (data r).LPos
  have hU : (0 : ℝ) < ((data r).U : ℝ) := by exact_mod_cast (data r).UPos
  have hG : (0 : ℝ) < (gapTotal (data r).gaps : ℝ) := by exact_mod_cast (data r).gapsPos
  have hV : (0 : ℝ) < ((data r).maxima j : ℝ) := by exact_mod_cast (data r).maximaPos j
  field_simp [hL.ne', hU.ne', hG.ne', hV.ne']
  ring

theorem physical_total_enclosure (r : Fin 2) :
    (((data r).jensenNum : ℝ) / (data r).jensenDen) *
      (1 + (value (total (data r)) : ℝ)) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  have hsum : (∫ z, constantCorrection r z ∂ν r) =
      (((transverseTerms (data r)).map value).sum : ℚ) := by
    rw [constantCorrection_expectation]
    simp_rw [physical_transverse_term]
    simp [transverseTerms, Fin.sum_univ_succ]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (physical_density_curvature_lower r)
  rw [total_value, Rat.cast_add, ← hsum, ← add_assoc]
  exact add_le_add (actual_T10_lower r) le_rfl

private theorem floor_of_source (r : Fin 2) (raw : ℕ)
    (harith : (raw : ℚ) / q96 ≤ ((data r).jensenNum : ℚ) / (data r).jensenDen *
      (1 + value (total (data r)))) :
    (raw : ℝ) / (q96 : ℝ) ≤
      ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  apply le_trans _ (physical_total_enclosure r)
  have hr : ((↑((raw : ℚ) / q96) : ℝ)) ≤
      (↑(((data r).jensenNum : ℚ) / (data r).jensenDen *
        (1 + value (total (data r)))) : ℝ) := Rat.cast_le.mpr harith
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_mul, Rat.cast_add, Rat.cast_one] using hr

/-- The directed row21 Q96 floor is below the actual physical integral. -/
theorem row21_original_curvature_Q96_integral_lower :
    (33473824252327663860 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport row21, physicalUpperIntegrand z :=
  floor_of_source 0 _ P2Winner9Row21SourceBridge.row21_raw_arithmetic_lower

/-- The directed row22 Q96 floor is below the actual physical integral. -/
theorem row22_original_curvature_Q96_integral_lower :
    (6447903780770652011 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport row22, physicalUpperIntegrand z := by
  exact floor_of_source 1 P2Winner9Row22Rounding.observedCurvatureRawQ96
    (total_directed_floor_semantics P2Winner9Row22Arithmetic.data
      P2Winner9Row22Rounding.observedCurvatureTotalQ80
      P2Winner9Row22Rounding.observedCurvatureRawQ96
      P2Winner9Row22Rounding.row22_original_curvature_rounding.1
      P2Winner9Row22Rounding.row22_original_curvature_rounding.2)

end

end ImbalancedChen.P2Winner9SelectedRowCurvatureFloor
