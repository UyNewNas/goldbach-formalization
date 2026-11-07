import ImbalancedChen.P5OriginalCommonRefinedConstructor

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact ancestral identities for the independently frozen common constructor.
No bound or numerical cell instance is used by this module. -/
namespace ImbalancedChen.P5OriginalCommonRefinedAncestry
noncomputable section
open scoped Classical
open P5OriginalCommonRefinedConstructor

theorem policy8_through_eight_eq_six
    (d : OriginalData) (N : ℝ) (positive : Bool) (pre : List ℕ)
    (hlen : pre.length ≤ 8) : policy8 d N positive pre = policy6 d N positive pre := by
  simp [policy8, P5OriginalAdoptedEighthPhysicalMasks.familyPolicy,
    P5OriginalAdoptedEighthPhysicalMasks.parentPolicy,
    P4AOriginalEighthParentPhysicalLedger.parentPolicy,
    P4AActualSixthFrozenEighthAdmission.sixthPolicy, policy6, level6,
    firstExitDepthSplicePolicy, hlen]

theorem policy8_through_six_eq_fifth
    (d : OriginalData) (N : ℝ) (positive : Bool) (pre : List ℕ)
    (hlen : pre.length ≤ 6) : policy8 d N positive pre = policy5 d N positive pre := by
  rw [policy8_through_eight_eq_six d N positive pre (hlen.trans (by decide))]
  simp [policy6, firstExitDepthSplicePolicy, hlen]

theorem policy8_rank_seven_test
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (hlen : pre.length = 7) :
    policy8 d N false pre = decide (ordinaryRosserPrefixAdmissible false
      (N ^ lambda6 d N (rosserAncestor 6 pre)) pre) := by
  rw [policy8_through_eight_eq_six d N false pre (by omega)]
  exact policy6_rank_seven d N pre hlen

theorem policy8_frontier_eight_eq_six
    (d : OriginalData) (N : ℝ) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (policy8 d N) h pre positive mass carrier =
      firstExitDepthFrontier 8 (policy6 d N) h pre positive mass carrier := by
  unfold policy8 P5OriginalAdoptedEighthPhysicalMasks.familyPolicy
  rw [firstExitDepthFrontier_depthSplice_eq 8 8 (by omega)]
  rfl

theorem policy8_frontier_through_six_eq_fifth
    (d : OriginalData) (N : ℝ) (k : ℕ) (hk : k ≤ 6)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier k (policy8 d N) h pre positive mass carrier =
      firstExitDepthFrontier k (policy5 d N) h pre positive mass carrier := by
  unfold policy8 P5OriginalAdoptedEighthPhysicalMasks.familyPolicy
    P5OriginalAdoptedEighthPhysicalMasks.parentPolicy
    P4AOriginalEighthParentPhysicalLedger.parentPolicy
    P4AActualSixthFrozenEighthAdmission.sixthPolicy
  rw [firstExitDepthFrontier_depthSplice_eq k 8 (hk.trans (by decide)),
    firstExitDepthFrontier_depthSplice_eq k 6 hk]

theorem actualParent5_ancestor_six (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    actualParent5 d N (rosserAncestor 6 pre) = actualParent5 d N pre := by
  unfold actualParent5
  rw [rosserAncestor_nested 5 6 (by omega)]

end
end ImbalancedChen.P5OriginalCommonRefinedAncestry
