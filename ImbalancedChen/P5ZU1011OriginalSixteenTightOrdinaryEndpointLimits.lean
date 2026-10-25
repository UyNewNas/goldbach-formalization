import ImbalancedChen.P5ZU1011OriginalSixteenTightGridEndpointLimits
import ImbalancedChen.P5ZU1011OriginalSixteenSingleStateLocal
import ImbalancedChen.P5ZU1011OriginalSixteenResidualWalls

/-!
# Actual literal-H248 ordinary endpoint limits and query-wall nullity

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The exact151 query walls from2 through5 are proper for every original
policy and either actual cap branch. Their union is null. This does not
discard the full clamp half-space: all raw queries below2 retain the
actual clamp value. The proved scalar interval openness and actual ratio
endpoint limits force the generated literal interval into one actual
state. The genuine ordinary endpoint width is then at most
(40/residualFloor^2)*step, with no state-agreement or cost-bound premise.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightOrdinaryEndpointLimits

noncomputable section

open Set MeasureTheory Filter Topology U11Integral Part5UpperTables
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open U1011OriginalSixteenTightGridLocalGeometry U1011OriginalSixteenTightGridEndpointLimits
open OriginalSixteenOrdinaryBoxBounds OriginalSixteenOrdinarySingleState OriginalSixteenSingleStateLocal
open U1011OriginalSixteenResidualWalls
open Classical

theorem exists_actual_cap_branch (p : Policy) (v : LogFour) :
    ∃ left : Bool, cap p v = affineCap p left v := by
  rw [cap_eq_affine_circuit]
  by_cases hp : p.val < 15
  · simp only [if_pos hp]
    by_cases hh : affineCap p true v ≤ affineCap p false v
    · exact ⟨true, min_eq_left hh⟩
    · exact ⟨false, min_eq_right (le_of_not_ge hh)⟩
  · exact ⟨true, by simp only [if_neg hp]⟩

abbrev QueryIndex := Policy × Bool × Fin 151

def queryForms (t : QueryIndex) : LogFour →L[ℝ] ℝ :=
  queryGate t.1 t.2.1 (LiteralH248IntervalBounds.grid (50 + t.2.2.val) : ℝ)
def queryBounds (t : QueryIndex) : ℝ := -capOffset t.1 t.2.1

theorem queryForms_ne_zero (t : QueryIndex) : queryForms t ≠ 0 :=
  queryGate_ne_zero _ _ _

theorem ae_actual_ratio_offKnots :
    ∀ᵐ v : LogFour ∂volume, ∀ p : Policy, v 3 ≠ 0 → OffKnots (typedResidual p v / v 3) := by
  filter_upwards [ae_primeAffineGate_no_wall queryForms queryBounds queryForms_ne_zero] with v hv
  intro p hw j heq
  obtain ⟨left, hleft⟩ := exists_actual_cap_branch p v
  have hres : typedResidual p v =
      (LiteralH248IntervalBounds.grid (50 + j.val) : ℝ) * v 3 :=
    (div_eq_iff hw).mp heq
  have hwall := (queryGate_eq_dictionary p left
    (LiteralH248IntervalBounds.grid (50 + j.val) : ℝ) v hleft).mp hres
  exact hv (p, left, j) hwall

theorem eventually_singleState (p : Policy) {v : LogFour}
    (hv : v ∈ sourceDomain) (hc : v ∈ cube)
    (hoff : OffKnots (typedResidual p v / v 3)) :
    ∀ᶠ n : ℕ in atTop, SingleState p (gridBox n (owner n v)) := by
  have hw : v 3 ≠ 0 := (originalDomain_denominators_pos ∅ v hv).1.ne'
  obtain ⟨delta, hd, hlocal⟩ := exists_singleState_margin (typedResidual p v / v 3) hoff
  have hL := (Metric.tendsto_nhds.mp (ratioLower_tendsto p hc hw)) delta hd
  have hU := (Metric.tendsto_nhds.mp (ratioUpper_tendsto p hc hw)) delta hd
  filter_upwards [hL, hU] with n hnL hnU
  apply hlocal p (gridBox n (owner n v))
  · simpa only [Real.dist_eq] using hnL
  · simpa only [Real.dist_eq] using hnU

def ordinaryRate : ℚ := 40 / residualFloor ^ 2

theorem eventually_actual_ordinary_endpoint_errors (p : Policy) {v : LogFour}
    (hv : v ∈ sourceDomain) (hc : v ∈ cube) (he : TypedEligible p v)
    (hoff : OffKnots (typedResidual p v / v 3)) :
    ∀ᶠ n : ℕ in atTop,
      |(ordinaryLower p (gridBox n (owner n v)) : ℝ) - ordinaryKernel H248 residual p.val v| ≤
        (ordinaryRate : ℝ) * (step n : ℝ) ∧
      |(ordinaryUpper p (gridBox n (owner n v)) : ℝ) - ordinaryKernel H248 residual p.val v| ≤
        (ordinaryRate : ℝ) * (step n : ℝ) := by
  filter_upwards [eventually_actual_eligible_positive_floor p hv hc he,
    eventually_singleState p hv hc hoff] with n hguard hstate
  have hwidth := (ordinary_width p (gridBox n (owner n v)) (gridBox_valid n (owner n v))
    hguard.1 residualFloor residualFloor_pos hguard.2 hstate).2
  rw [generated_sideSum] at hwidth
  have hwidthR : (ordinaryUpper p (gridBox n (owner n v)) : ℝ) -
      (ordinaryLower p (gridBox n (owner n v)) : ℝ) ≤
        (ordinaryRate : ℝ) * (step n : ℝ) := by
    have hR : ((ordinaryUpper p (gridBox n (owner n v)) -
        ordinaryLower p (gridBox n (owner n v)) : ℚ) : ℝ) ≤
        (((10 / residualFloor ^ 2 : ℚ) * (4 * step n) : ℚ) : ℝ) := by exact_mod_cast hwidth
    push_cast at hR
    dsimp only [ordinaryRate]
    push_cast
    nlinarith only [hR]
  have hb := actual_ordinary_bounds p (gridBox n (owner n v)) hguard.1
    (cell_subset_closedBox n (owner n v) (owner_mem n hc))
  rw [abs_of_nonpos (sub_nonpos.mpr hb.1), abs_of_nonneg (sub_nonneg.mpr hb.2)]
  constructor <;> linarith only [hb.1, hb.2, hwidthR]

theorem actual_ordinary_endpoints_tendsto (p : Policy) {v : LogFour}
    (hv : v ∈ sourceDomain) (hc : v ∈ cube) (he : TypedEligible p v)
    (hoff : OffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => (ordinaryLower p (gridBox n (owner n v)) : ℝ)) atTop
      (𝓝 (ordinaryKernel H248 residual p.val v)) ∧
    Tendsto (fun n => (ordinaryUpper p (gridBox n (owner n v)) : ℝ)) atTop
      (𝓝 (ordinaryKernel H248 residual p.val v)) := by
  have hz : Tendsto (fun n : ℕ => (ordinaryRate : ℝ) * (step n : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_step.const_mul (ordinaryRate : ℝ)
  have herr := eventually_actual_ordinary_endpoint_errors p hv hc he hoff
  constructor
  · rw [Metric.tendsto_nhds]
    intro eps heps
    filter_upwards [herr, hz.eventually (gt_mem_nhds heps)] with n hn hsmall
    rw [Real.dist_eq]
    exact hn.1.trans_lt hsmall
  · rw [Metric.tendsto_nhds]
    intro eps heps
    filter_upwards [herr, hz.eventually (gt_mem_nhds heps)] with n hn hsmall
    rw [Real.dist_eq]
    exact hn.2.trans_lt hsmall

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightOrdinaryEndpointLimits
