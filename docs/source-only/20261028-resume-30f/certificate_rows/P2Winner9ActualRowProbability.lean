import ImbalancedChen.P2Winner9ActualT10Moments
import ImbalancedChen.P2PositiveAffineSimplexLogJensen
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual row probability measures and the T10 Jensen-GAP lower bound.
The probability measure is built from the real physical gap density on
the same actual support, with its already derived positive physical mass.
No analytic enclosure, mean identity or T10 lower bound is a premise.
-/

namespace ImbalancedChen.P2Winner9ActualRowProbability

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedPhysicalMeans
open ImbalancedChen.P2Winner9SelectedAllMixedMoments
open ImbalancedChen.P2Winner9SelectedPhysicalQ6Floor
open ImbalancedChen.P2Winner9ActualT10Moments
open ImbalancedChen.P2Winner9T10TailJensen
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2PositiveAffineSimplexLogJensenSourceOnly

def μ (r : Fin 2) : Measure Ambient := volume.restrict (sourceSupport (vertices r))

def ν (r : Fin 2) : Measure Ambient := weightedProbability (μ r) physicalGap

def U (r : Fin 2) : ℝ := (upper r : ℝ)

def P (r : Fin 2) (z : Ambient) : ℝ := physicalP (fun j => (means r j : ℝ)) z

def Y (r : Fin 2) (z : Ambient) : ℝ := physicalY (fun j => (means r j : ℝ)) (U r) z

def invP10 (r : Fin 2) (z : Ambient) : ℝ := 1 / (P r z)^10

theorem U_pos (r : Fin 2) : 0 < U r := by exact_mod_cast (actual_vertex_guards r).1

theorem μ_support (r : Fin 2) : ∀ᵐ z ∂μ r, z ∈ sourceSupport (vertices r) :=
  ae_restrict_mem (sourceSupport_measurable (vertices r) (row_det_ne_zero r))

theorem gap_nonneg_ae (r : Fin 2) : ∀ᵐ z ∂μ r, 0 ≤ physicalGap z :=
  (μ_support r).mono (fun z hz => (actual_support_caps r hz).1)

theorem gap_integrable (r : Fin 2) : Integrable physicalGap (μ r) :=
  continuous_physicalGap.continuousOn.integrableOn_compact
    (sourceSupport_compact (vertices r) (row_det_ne_zero r))

instance row_probability (r : Fin 2) : IsProbabilityMeasure (ν r) :=
  weightedProbability_isProbability (μ r) physicalGap (gap_integrable r)
    (gap_nonneg_ae r) (gapMass_pos r)

theorem ν_support (r : Fin 2) : ∀ᵐ z ∂ν r, z ∈ sourceSupport (vertices r) := by
  exact (withDensity_absolutelyContinuous _ _).ae_le (μ_support r)

theorem weighted_integral (r : Fin 2) (f : Ambient → ℝ) :
    (∫ z, f z ∂ν r) = (∫ z in sourceSupport (vertices r), physicalGap z * f z) / gapMass r :=
  integral_weightedProbability (μ r) physicalGap continuous_physicalGap.measurable
    (gap_nonneg_ae r) (gapMass_pos r) f

/-- Real compact-support continuity supplies each probability integrability
obligation, rather than assuming any desired expectation bound. -/
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
  have hn := normalized_continuous r
  unfold P physicalP
  fun_prop

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

theorem integral_Y_pow (r : Fin 2) (k : Nat) :
    (∫ z, (Y r z)^k ∂ν r) = physicalPowerMean r k := by
  rw [weighted_integral]
  rfl

theorem integral_Y (r : Fin 2) : (∫ z, Y r z ∂ν r) = 1 - 1 / U r := by
  have h := integral_Y_pow r 1
  simpa only [pow_one, actual_Y_mean, U] using h

theorem invP10_scaled (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) :
    invP10 r z = (1 / (U r)^10) * (1 / (1 - Y r z)^10) := by
  have hp := (P_pos r hz).ne'
  have hu := (U_pos r).ne'
  have hy : 1 - Y r z = P r z / U r := by
    unfold Y physicalY P
    ring
  rw [hy]
  unfold invP10
  field_simp [hu, hp] <;> ring

/-- The true T10 Jensen-GAP lower bound for the actual physical row.
The tail convexity theorem, true probability and actual power moments
are all supplied internally; no analytic enclosure is assumed. -/
theorem actual_T10_lower (r : Fin 2) :
    1 + (value (t10 (data r)) : ℝ) ≤ ∫ z, invP10 r z ∂ν r := by
  have hY := weighted_integrable r (Y_continuous r).continuousOn
  have hf := weighted_integrable r (fY_continuousOn r)
  have hp (k : Nat) (_hk : k ∈ Finset.range 11) : Integrable (fun z => (Y r z)^k) (ν r) :=
    weighted_integrable r ((Y_continuous r).pow k).continuousOn
  have hgap := probability_T10_gap (ν r) (Y r) (q_lt_one r)
    ((ν_support r).mono (fun z hz => Y_mem r hz)) hY hf hp
  have hU := U_pos r
  have hscale : 0 < 1 / (U r)^10 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hgap hscale.le
  have hI : (∫ z, invP10 r z ∂ν r) =
      (1 / (U r)^10) * ∫ z, 1 / (1 - Y r z)^10 ∂ν r := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact (ν_support r).mono (fun z hz => invP10_scaled r hz)
  have hunit : (1 / (U r)^10) * (1 / (1 - ∫ z, Y r z ∂ν r)^10) = 1 := by
    rw [integral_Y]
    have hu := (U_pos r).ne'
    field_simp [hu] <;> ring
  rw [← hI] at hscaled
  rw [mul_add, hunit] at hscaled
  rw [actual_T10_identity]
  simp_rw [← integral_Y_pow]
  change 1 + (1 / (U r)^10) * _ ≤ _
  simpa only [pow_one] using hscaled

end

end ImbalancedChen.P2Winner9ActualRowProbability
