import ImbalancedChen.P2PositiveAffineSimplexLogJensen
import ImbalancedChen.P2Winner9SelectedPhysicalMeans
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Probability measures of the selected physical rows

The measures normalize the physical gap density on the original supports.
Compactness and the actual vertex bounds give integrability of the functions
used in the common-affine Jensen estimate.
-/

namespace ImbalancedChen.P2Winner9ActualRowProbability

noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedPhysicalMeans
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2PositiveAffineSimplexLogJensenSourceOnly

def μ (r : Fin 2) : Measure Ambient := volume.restrict (sourceSupport (vertices r))

def ν (r : Fin 2) : Measure Ambient := weightedProbability (μ r) physicalGap

def U (r : Fin 2) : ℝ := (upper r : ℝ)

def P (r : Fin 2) (z : Ambient) : ℝ := physicalP (fun j => (means r j : ℝ)) z

def Y (r : Fin 2) (z : Ambient) : ℝ := physicalY (fun j => (means r j : ℝ)) (U r) z

def invP10 (r : Fin 2) (z : Ambient) : ℝ := 1 / (P r z)^10

theorem U_pos (r : Fin 2) : 0 < U r := by
  unfold U
  exact_mod_cast (actual_vertex_guards r).1

theorem μ_support (r : Fin 2) : ∀ᵐ z ∂μ r, z ∈ sourceSupport (vertices r) :=
  ae_restrict_mem (sourceSupport_measurable (vertices r) (row_det_ne_zero r))

theorem gap_nonneg_ae (r : Fin 2) : ∀ᵐ z ∂μ r, 0 ≤ physicalGap z :=
  (μ_support r).mono (fun _ hz => (actual_support_caps r hz).1)

theorem gap_integrable (r : Fin 2) : Integrable physicalGap (μ r) :=
  continuous_physicalGap.continuousOn.integrableOn_compact
    (sourceSupport_compact (vertices r) (row_det_ne_zero r))

instance row_probability (r : Fin 2) : IsProbabilityMeasure (ν r) :=
  weightedProbability_isProbability (μ r) physicalGap (gap_integrable r)
    (gap_nonneg_ae r) (gapMass_pos r)

theorem ν_support (r : Fin 2) : ∀ᵐ z ∂ν r, z ∈ sourceSupport (vertices r) := by
  unfold ν weightedProbability
  exact (withDensity_absolutelyContinuous (μ r) _).ae_le (μ_support r)

theorem weighted_integral (r : Fin 2) (f : Ambient → ℝ) :
    (∫ z, f z ∂ν r) = (∫ z in sourceSupport (vertices r), physicalGap z * f z) / gapMass r :=
  integral_weightedProbability (μ r) physicalGap continuous_physicalGap.measurable
    (gap_nonneg_ae r) (gapMass_pos r) f

/-- A continuous function on the original compact support is integrable
under the normalized gap density. -/
theorem weighted_integrable (r : Fin 2) {f : Ambient → ℝ}
    (hf : ContinuousOn f (sourceSupport (vertices r))) : Integrable f (ν r) := by
  apply integrable_weightedProbability (μ r) physicalGap
    continuous_physicalGap.measurable (gap_nonneg_ae r) (gapMass_pos r)
  exact (continuous_physicalGap.continuousOn.mul hf).integrableOn_compact
    (sourceSupport_compact (vertices r) (row_det_ne_zero r))

theorem normalized_continuous (r : Fin 2) (j : Fin 10) :
    Continuous (normalizedFactor (fun k => (means r k : ℝ)) j) :=
  (continuous_physicalFactor j).div_const _

theorem P_continuous (r : Fin 2) : Continuous (P r) := by
  unfold P physicalP
  exact (continuous_finsetSum Finset.univ (fun j _ => normalized_continuous r j)).div_const _

theorem Y_continuous (r : Fin 2) : Continuous (Y r) := by
  unfold Y physicalY
  exact continuous_const.sub ((P_continuous r).div_const _)

theorem P_pos (r : Fin 2) {z : Ambient} (hz : z ∈ sourceSupport (vertices r)) :
    0 < P r z :=
  lt_of_lt_of_le (by exact_mod_cast (actual_vertex_guards r).2.1)
    (actual_support_caps r hz).2.2.1

theorem Y_mem (r : Fin 2) {z : Ambient} (hz : z ∈ sourceSupport (vertices r)) :
    Y r z ∈ Icc (0 : ℝ) (yUpper r : ℝ) :=
  ⟨(actual_uniform_Y r hz).1, (actual_uniform_Y r hz).2.1⟩

theorem q_lt_one (r : Fin 2) : (yUpper r : ℝ) < 1 := by
  have hU := U_pos r
  have hp : (0 : ℝ) < (pLower r : ℝ) := by exact_mod_cast (actual_vertex_guards r).2.1
  have he : (yUpper r : ℝ) = 1 - (pLower r : ℝ) / U r := by simp [yUpper, U]
  rw [he]
  have h := div_pos hp hU
  linarith

theorem Y_lt_one (r : Fin 2) {z : Ambient} (hz : z ∈ sourceSupport (vertices r)) :
    Y r z < 1 := lt_of_le_of_lt (Y_mem r hz).2 (q_lt_one r)

theorem fY_continuousOn (r : Fin 2) :
    ContinuousOn (fun z => 1 / (1 - Y r z)^10) (sourceSupport (vertices r)) := by
  apply continuous_const.continuousOn.div
    ((continuous_const.sub (Y_continuous r)).pow 10).continuousOn
  intro z hz
  exact pow_ne_zero _ (ne_of_gt (sub_pos.mpr (Y_lt_one r hz)))

theorem invP10_continuousOn (r : Fin 2) :
    ContinuousOn (invP10 r) (sourceSupport (vertices r)) := by
  apply continuous_const.continuousOn.div ((P_continuous r).pow 10).continuousOn
  intro z hz
  exact pow_ne_zero _ (P_pos r hz).ne'

theorem invP10_scaled (r : Fin 2) {z : Ambient}
    (_hz : z ∈ sourceSupport (vertices r)) :
    invP10 r z = (1 / (U r)^10) * (1 / (1 - Y r z)^10) := by
  have hy : 1 - Y r z = P r z / U r := by
    unfold Y physicalY P
    ring
  rw [invP10, hy, div_pow]
  simp only [one_div, inv_div]
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (U_pos r).ne'), one_mul]

end

end ImbalancedChen.P2Winner9ActualRowProbability
