import ImbalancedChen.P5ZU1011OriginalSixteenNearCapGridBufferData
import ImbalancedChen.P5ZU1011OriginalSixteenSeparateGridCoverage

/-!
# Actual fixed native profiles and eventual separate-box policy coverage

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Certified near-cap residuals exceed the original a and the fixed physical
w-base is at least a/2. Thus the safe clips are INACTIVE on every actual
certified cell, and its fixed nativeCost equals the constructed physical
ordinary cost exactly, before any asymptotic limit.

Shrinking actual owner boxes eventually pass the CONCRETE separate
WholeBoxEligibleTest for every actually eligible policy. The a52 actual
48-width margin criterion supplies this for all16; no correlated-test
implication is substituted. Ineligible policies never pass by soundness.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenNearCapGridProfiles

noncomputable section

open Set MeasureTheory Filter Topology U11Integral
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSixteenTightGridLocalGeometry
open U1011OriginalSixteenNearCapGridBufferData
open U1011OriginalSixteenBufferedEnvelopeIntegral
open U1011OriginalSixteenSeparateGridCoverage
open scoped BigOperators

theorem meshLevel_tendsto : Tendsto meshLevel atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop k] with n hn
  unfold meshLevel
  omega

theorem tendsto_eta : Tendsto (fun n => (eta n : ℝ)) atTop (𝓝 0) :=
  tendsto_step.comp meshLevel_tendsto

theorem eventually_all_actual_wholeBox_tests {v : LogFour} (hv : v ∈ cube) :
    ∀ᶠ n : ℕ in atTop, ∀ p : Policy,
      Certified n p (owner (meshLevel n) v) ↔ TypedEligible p v := by
  apply eventually_all.mpr
  intro p
  have hsound (n : ℕ) : Certified n p (owner (meshLevel n) v) → TypedEligible p v := by
    intro ht
    exact wholeBoxEligibleTest_sound p _ ht v (cell_subset_closedBox _ _ (owner_mem _ hv))
  by_cases he : TypedEligible p v
  · have hstep : Tendsto (fun n => 48 * (eta n : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_eta.const_mul 48
    have hall : ∀ᶠ n : ℕ in atTop, ∀ g : Gate, Required p g → ∀ left : Bool,
        48 * (eta n : ℝ) < (margin p left g).eval v := by
      apply eventually_all.mpr
      intro g
      by_cases hg : Required p g
      · have hleft : ∀ᶠ n : ℕ in atTop, ∀ left : Bool,
            48 * (eta n : ℝ) < (margin p left g).eval v := by
          apply eventually_all.mpr
          intro left
          have hpos := (typedEligible_iff_positive_margins p v).mp he g hg left
          exact hstep.eventually (gt_mem_nhds hpos)
        exact hleft.mono (fun n hn _ => hn)
      · exact Eventually.of_forall (fun _ h => (hg h).elim)
    filter_upwards [hall] with n hn
    have ht : Certified n p (owner (meshLevel n) v) :=
      all_sixteen_wholeBoxTest_of_large_actual_margins p _ (eta n : ℝ)
        (cell_subset_closedBox _ _ (owner_mem _ hv)) (owner_width _ v) hn
    exact ⟨hsound n, fun _ => ht⟩
  · exact Eventually.of_forall (fun n => ⟨hsound n, fun h => (he h).elim⟩)

theorem certified_profile_floors (n : ℕ) (p : Policy) (j : Index (meshLevel n))
    (ht : Certified n p j) :
    (a : ℚ) ≤ U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p (box n j) (eta n) ∧
      (a / 2 : ℚ) ≤ (box n j).lo 3 - U1011OriginalSixteenNearCapBoxProfiles.xi p (box n j) (eta n) := by
  have hvalid := gridBox_valid (meshLevel n) j
  have hpositive := U1011OriginalSixteenRationalIntegralCertificates.grid_lo_pos (meshLevel n) j 3
  have hpars := U1011OriginalSixteenNearCapBoxProfiles.rational_parameters p (box n j) (eta n)
    hvalid hpositive ht (eta_pos n)
  have hlast := U1011OriginalSixteenNearCapBoxProfiles.fullUpper_le_G p (box n j) 3
  rw [U1011OriginalSixteenNearCapBoxProfiles.lastUpper_eq_Tplus] at hlast
  have hG : U1011OriginalSixteenNearCapBoxProfiles.Tplus (box n j) + (box n j).lo 3 ≤
      U1011OriginalSixteenNearCapBoxProfiles.G p (box n j) := by linarith only [hlast, hvalid 3]
  have hR := NearCapRationalParameters.residual_lower
    (U1011OriginalSixteenNearCapBoxProfiles.G p (box n j)) (capLower p (box n j)) (eta n)
    (U1011OriginalSixteenNearCapBoxProfiles.Tplus (box n j)) ((box n j).lo 3) hG
  have hD : 0 < U1011OriginalSixteenNearCapBoxProfiles.delta p (box n j) (eta n) := hpars.2.2.1
  have hxi := NearCapRationalParameters.xi_le_half
    (U1011OriginalSixteenNearCapBoxProfiles.G p (box n j)) (capLower p (box n j)) (eta n) ((box n j).lo 3)
  have hbase : a ≤ (box n j).lo 3 := (gridBox_corner_bounds _ j 3).1
  constructor
  · change (box n j).lo 3 + 44 * U1011OriginalSixteenNearCapBoxProfiles.delta p (box n j) (eta n) ≤
      U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p (box n j) (eta n) at hR
    linarith only [hR, hD, hbase]
  · change U1011OriginalSixteenNearCapBoxProfiles.xi p (box n j) (eta n) ≤ (box n j).lo 3 / 2 at hxi
    linarith only [hxi, hbase]

/-- The fixed native R/Z profile equals the safely clipped physical
caller on an actual certified owner, with no profile-agreement premise. -/
theorem nativeCost_eq_actual_physical (n : ℕ) (p : Policy) {v : LogFour}
    (hv : v ∈ cube) (ht : Certified n p (owner (meshLevel n) v)) :
    U1011OriginalSixteenNearCapBoxProfiles.nativeCost p (box n (owner (meshLevel n) v)) (eta n) =
      U1011OriginalSixteenBufferedEnvelopeIntegral.physicalOrdinary actualBufferData n p v := by
  let B := box n (owner (meshLevel n) v)
  have hd := actual_data_on_certified_owner n p hv ht
  have hf := certified_profile_floors n p (owner (meshLevel n) v) ht
  have hR : U1011OriginalSixteenBufferedCandidate.clip ≤
      typedResidual p v - tauData n p v := by
    rw [hd.1]
    unfold U1011OriginalSixteenNearCapBoxProfiles.tau
    have hh : (a : ℝ) ≤ (U1011OriginalSixteenNearCapBoxProfiles.physicalResidual p B (eta n) : ℝ) := by
      exact_mod_cast hf.1
    norm_num [U1011OriginalSixteenBufferedCandidate.clip, U1011OriginalSixteenBufferedCandidate.a, a] at hh ⊢
    linarith only [hh]
  have hw : U1011OriginalSixteenBufferedCandidate.clip ≤ v 3 - xiData n p v := by
    rw [hd.2.1]
    unfold U1011OriginalSixteenNearCapBoxProfiles.xiEff
    have hh : ((a / 2 : ℚ) : ℝ) ≤ ((B.lo 3 - U1011OriginalSixteenNearCapBoxProfiles.xi p B (eta n) : ℚ) : ℝ) := by
      exact_mod_cast hf.2
    push_cast at hh
    norm_num [U1011OriginalSixteenBufferedCandidate.clip, U1011OriginalSixteenBufferedCandidate.a, a] at hh ⊢
    linarith only [hh]
  have heq := U1011OriginalSixteenNearCapBoxProfiles.nativeCost_eq_physicalCost p B (eta n)
    (gridBox_valid _ _) (U1011OriginalSixteenRationalIntegralCertificates.grid_lo_pos _ _ 3) ht (eta_pos n) v
  change U1011OriginalSixteenNearCapBoxProfiles.nativeCost p B (eta n) =
    4 * (1 - Part5UpperTables.H248 (max (2 + rhoData n p v)
      (max U1011OriginalSixteenBufferedCandidate.clip (typedResidual p v - tauData n p v) /
        max U1011OriginalSixteenBufferedCandidate.clip (v 3 - xiData n p v)))) /
      max U1011OriginalSixteenBufferedCandidate.clip (typedResidual p v - tauData n p v)
  rw [max_eq_right hR, max_eq_right hw, hd.1, hd.2.1, hd.2.2]
  exact heq

end

end ImbalancedChen.P5Z.U1011OriginalSixteenNearCapGridProfiles
