import ImbalancedChen.P5ZU1011OriginalSixteenTightOrdinaryEndpointLimits

/-!
# Genuine diagonal collapse of the original16 computed box minimum

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The moving lower minimum chooses an ACTUAL attained candidate. Eventual
original eligibility classification and positive residual floors pair
that candidate with its computed upper candidate. Its width is paid by
the genuine generated switched or literal single-state ordinary width.
The finitely many policy thresholds are combined before this choice.

Thus the actual computed nonlinear minimum width tends to zero on the
diagonal m=n+1 at every original point off the actual eligibility/query
walls. No minimum-of-means or final-gap estimate is an input. Global
integration of these genuine pointwise facts is a separate next step.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightMinimumDiagonal

noncomputable section

open Set MeasureTheory Filter Topology U11Integral Part5UpperTables
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open U1011OriginalSixteenTightGridLocalGeometry U1011OriginalSixteenTightGridEndpointLimits
open U1011OriginalSixteenTightOrdinaryEndpointLimits
open OriginalSixteenOrdinaryBoxBounds OriginalSixteenSingleStateLocal
open U1011OriginalSixteenTightRationalIntegralCertificates
open Classical

def diagonalGap (n : ℕ) (v : LogFour) : ℝ :=
  ((boxUpper (n + 1) (gridBox n (owner n v)) -
    boxLower (n + 1) (gridBox n (owner n v)) : ℚ) : ℝ)

theorem diagonalGap_nonneg {v : LogFour} (hv : v ∈ sourceDomain) (hc : v ∈ cube) (n : ℕ) :
    0 ≤ diagonalGap n v := by
  have hb := box_bounds (n + 1) (by omega) (gridBox n (owner n v))
    (cell_subset_closedBox n (owner n v) (owner_mem n hc)) hv
  simp only [diagonalGap, Rat.cast_sub]
  linarith only [hb.1, hb.2]

/-- The ORIGINAL nonlinear computed minimum itself, with every actual
eligible mask and W candidate, has a vanishing diagonal enclosure width. -/
theorem diagonal_minimum_gap_tendsto {v : LogFour} (hv : v ∈ sourceDomain) (hc : v ∈ cube)
    (hno : ∀ p : Policy, ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g)
    (hqueries : ∀ p : Policy, OffKnots (typedResidual p v / v 3)) :
    Tendsto (fun n => diagonalGap n v) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have hordinary : ∀ᶠ n : ℕ in atTop, ∀ p : Policy, TypedEligible p v →
      ((ordinaryUpper p (gridBox n (owner n v)) -
        ordinaryLower p (gridBox n (owner n v)) : ℚ) : ℝ) < eps := by
    apply eventually_all.mpr
    intro p
    by_cases he : TypedEligible p v
    · have ht := actual_ordinary_endpoints_tendsto p hv hc he (hqueries p)
      have hz : Tendsto (fun n => ((ordinaryUpper p (gridBox n (owner n v)) -
          ordinaryLower p (gridBox n (owner n v)) : ℚ) : ℝ)) atTop (𝓝 0) := by
        simpa only [Rat.cast_sub, sub_self] using ht.2.sub ht.1
      filter_upwards [hz.eventually (gt_mem_nhds heps)] with n hn
      exact fun _ => hn
    · exact Eventually.of_forall (fun _ hp => (he hp).elim)
  have hguards : ∀ᶠ n : ℕ in atTop, ∀ p : Policy, TypedEligible p v →
      PositiveGuards p (gridBox n (owner n v)) := by
    apply eventually_all.mpr
    intro p
    by_cases he : TypedEligible p v
    · filter_upwards [eventually_actual_eligible_positive_floor p hv hc he] with n hn
      exact fun _ => hn.1
    · exact Eventually.of_forall (fun _ hp => (he hp).elim)
  filter_upwards [eventually_all_eligibility_tests hc hno, hguards, hordinary,
    (diagonal_switched_gap_tendsto v).eventually (gt_mem_nhds heps)] with n htest hguard hord hsw
  have hwidth : diagonalGap n v < eps := by
    let B := gridBox n (owner n v)
    have hm := Finset.min'_mem (lowerValues (n + 1) B) (lowerValues_nonempty (n + 1) B)
    change boxLower (n + 1) B ∈ lowerValues (n + 1) B at hm
    rcases Finset.mem_insert.mp hm with hs | hp
    · have hu : boxUpper (n + 1) B ≤ OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) B :=
        Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      have huR : (boxUpper (n + 1) B : ℝ) ≤
          (OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) B : ℝ) := by exact_mod_cast hu
      have hsR : (boxLower (n + 1) B : ℝ) =
          (OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) B : ℝ) := by exact_mod_cast hs
      change ((boxUpper (n + 1) B - boxLower (n + 1) B : ℚ) : ℝ) < eps
      simp only [Rat.cast_sub] at hsw ⊢
      change (OriginalSixteenTightSwitchedBoxes.switchedUpper (n + 1) B : ℝ) -
        (OriginalSixteenTightSwitchedBoxes.switchedLower (n + 1) B : ℝ) < eps at hsw
      linarith only [huR, hsR, hsw]
    · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hp
      have hpossible := (Finset.mem_filter.mp hp).2
      have he : TypedEligible p v := by
        by_contra hn
        exact hpossible ((htest p).2.mpr hn)
      have hg := hguard p he
      have hcert : certified p B := ⟨(htest p).1.mpr he, hg⟩
      have hmem : ordinaryUpper p B ∈ upperValues (n + 1) B := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcert⟩, rfl⟩)
      have hu : boxUpper (n + 1) B ≤ ordinaryUpper p B := Finset.min'_le _ _ hmem
      have hl : boxLower (n + 1) B = ordinaryLower p B := by
        rw [← heq]
        simp only [OriginalSixteenEnvelopeBoxBounds.candidateLower, if_pos hg]
      have huR : (boxUpper (n + 1) B : ℝ) ≤ (ordinaryUpper p B : ℝ) := by exact_mod_cast hu
      have hlR : (boxLower (n + 1) B : ℝ) = (ordinaryLower p B : ℝ) := by exact_mod_cast hl
      have ho := hord p he
      change ((ordinaryUpper p B - ordinaryLower p B : ℚ) : ℝ) < eps at ho
      change ((boxUpper (n + 1) B - boxLower (n + 1) B : ℚ) : ℝ) < eps
      simp only [Rat.cast_sub] at ho ⊢
      linarith only [huR, hlR, ho]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (diagonalGap_nonneg hv hc n)]
  exact hwidth

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightMinimumDiagonal
