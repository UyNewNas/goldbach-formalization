import ImbalancedChen.P2OriginalElevenCanonicalSameQOmission
import ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A concrete compact-gated truncation of the actual common eleven-family
sixth supplier, with the actual fifth seed and the actual eighth rules.
This is the compact-source truncation step.  It is NOT identified with
the missing common fine-label endpoint compiler.  No policy-agreement or
omitted-support conclusion is supplied as a hypothesis.
-/
namespace ImbalancedChen.P2OriginalElevenCompactGatedPolicy
noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthSourceCompactCores
open P5OriginalCommonRefinedConstructor
open P1OriginalVariableFourthContinuation

def compactEligible (d : OriginalData) (n : ℕ) (N : ℝ) (c : Cell) (pre : List ℕ) : Prop :=
  eligibleSixth d N c pre ∧ primeHistoryLogCoordinates N 6 pre ∈ coreSequence c n

def compactLambda6 (d : OriginalData) (n : ℕ) (N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax allCells.toFinset (fun c => compactEligible d n N c pre)
    (fun c => newCap c (primeHistoryLogCoordinates N 6 pre)) (actualParent5 d N pre)

def compactPolicy8 (d : OriginalData) (n : ℕ) (N : ℝ) : Bool → List ℕ → Bool :=
  P5OriginalAdoptedEighthPhysicalMasks.familyPolicy N (lambda3 d N) (compactLambda6 d n N) (policy5 d N)

def BadSix (d : OriginalData) (n : ℕ) (N : ℝ) (pre : List ℕ) : Prop :=
  ∃ c : Cell, eligibleSixth d N c pre ∧ primeHistoryLogCoordinates N 6 pre ∉ coreSequence c n

def BadHistory (d : OriginalData) (n : ℕ) (N : ℝ) (pre : List ℕ) : Prop :=
  BadSix d n N (rosserAncestor 6 pre)

theorem compactLambda6_le_actual (d : OriginalData) (n : ℕ) (N : ℝ) (pre : List ℕ) :
    compactLambda6 d n N pre ≤ lambda6 d N pre := by
  apply finiteMax_le
  · exact actualParent5_le_lambda6 d N pre
  · intro c hc he
    exact eligibleSixth_newCap_le_lambda6 d N c pre he.1

theorem actual_lambda6_eq_compact_of_not_bad (d : OriginalData) (n : ℕ) (N : ℝ)
    (pre : List ℕ) (hgood : ¬BadSix d n N pre) :
    lambda6 d N pre = compactLambda6 d n N pre := by
  have heq : (fun c => compactEligible d n N c pre) = (fun c => eligibleSixth d N c pre) := by
    funext c
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h,?_⟩
      by_contra hout
      exact hgood ⟨c,h,hout⟩
  simp only [compactLambda6,lambda6,heq]

theorem changed_lambda_has_original_omitted_source (d : OriginalData) (n : ℕ) (N : ℝ)
    (pre : List ℕ) (hne : lambda6 d N pre ≠ compactLambda6 d n N pre) :
    pre.length = 6 ∧ ∃ c : Cell, primeHistoryLogCoordinates N 6 pre ∈ omittedSource c n := by
  have hb : BadSix d n N pre := by
    by_contra h
    exact hne (actual_lambda6_eq_compact_of_not_bad d n N pre h)
  obtain ⟨c,hc,hout⟩ := hb
  exact ⟨hc.1,c,hc.2.1,hout⟩

theorem compactPolicy8_even (d : OriginalData) (n : ℕ) (N : ℝ) (pre : List ℕ) :
    compactPolicy8 d n N true pre = true :=
  P5OriginalAdoptedEighthPhysicalMasks.family_even N (lambda3 d N) (compactLambda6 d n N)
    (policy5 d N) (policy5_even d N) pre

private theorem raised_eq_of_actual_six_eq (d : OriginalData) (n : ℕ) (N : ℝ)
    (pre : List ℕ)
    (hcap : lambda6 d N (rosserAncestor 6 pre) = compactLambda6 d n N (rosserAncestor 6 pre)) :
    P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N (lambda3 d N) (lambda6 d N) pre =
      P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N (lambda3 d N) (compactLambda6 d n N) pre := by
  simp only [P5OriginalAdoptedEighthPhysicalMasks.raisedExponent,
    P5OriginalAdoptedEighthPhysicalMasks.adoptedGuard,hcap]

/-- The actual rank-eight rule reads the SAME sixth ancestor.  Both the
guard and its selected cap are unchanged when that ancestor cap agrees. -/
theorem policy8_eq_compact_off_bad_history (d : OriginalData) (n : ℕ) (N : ℝ)
    (positive : Bool) (pre : List ℕ) (hgood : ¬BadHistory d n N pre) :
    policy8 d N positive pre = compactPolicy8 d n N positive pre := by
  have hcap := actual_lambda6_eq_compact_of_not_bad d n N (rosserAncestor 6 pre) hgood
  change firstExitDepthSplicePolicy 8
    (firstExitDepthSplicePolicy 6 (policy5 d N)
      (frozenParityRosserPolicy false 6 (fun q => N ^ lambda6 d N q)))
    (frozenParityRosserPolicy false 8 (fun q => N ^
      P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N (lambda3 d N) (lambda6 d N) q)) positive pre =
    firstExitDepthSplicePolicy 8
      (firstExitDepthSplicePolicy 6 (policy5 d N)
        (frozenParityRosserPolicy false 6 (fun q => N ^ compactLambda6 d n N q)))
      (frozenParityRosserPolicy false 8 (fun q => N ^
        P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N (lambda3 d N) (compactLambda6 d n N) q)) positive pre
  by_cases h8 : pre.length ≤ 8
  · simp only [firstExitDepthSplicePolicy,if_pos h8]
    by_cases h6 : pre.length ≤ 6
    · simp only [if_pos h6]
    · simp only [if_neg h6,frozenParityRosserPolicy,ancestorFrozenPolicy,hcap]
  · simp only [firstExitDepthSplicePolicy,if_neg h8,frozenParityRosserPolicy,ancestorFrozenPolicy]
    have hc : lambda6 d N (rosserAncestor 6 (rosserAncestor 8 pre)) =
        compactLambda6 d n N (rosserAncestor 6 (rosserAncestor 8 pre)) := by
      simpa only [rosserAncestor_nested 6 8 (by omega)] using hcap
    rw [raised_eq_of_actual_six_eq d n N (rosserAncestor 8 pre) hc]

end
end ImbalancedChen.P2OriginalElevenCompactGatedPolicy
