import ImbalancedChen.P4AOriginalFourteenThirteenCurrentSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original thirteen action is localized to its actual source.  Outside
that source it keeps the complete previous fourteen policy, including all
its later decisions.  An unconditional eighth splice with inheritedSixth
outside the thirteen source would erase the previous fourteen action.

This file proves the actual full-q source identity for the localized tree.
It does not supply the ordinary arithmetic lower bound or identify this
two-stage tree with the final full87 chronology.
-/
namespace ImbalancedChen.P4AOriginalThirteenLocalizedContinuation
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P4AOriginalArchiveFourteenPositivePresieve
open P4AOriginalFourteenThirteenCurrentSource
open P1Pair12RetainedSignedSource
open P2OriginalThirdMinorantLogDictionarySourceOnly
open OriginalAscendingThirteenCellOwnership

/-- The same frozen rank-eight ancestor controls every later decision.
The comparison is a tested cap guard, not a purported licence field. -/
def active (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) : Prop :=
  let ancestor := rosserAncestor 8 pre
  let t := primeHistoryLogCoordinates N 8 ancestor
  (∃ i : Fin 13, StrictRows i t) ∧
    lambda6 (data e q omega) N (rosserAncestor 6 pre) ≤ comparisonCap t

def continuation (e : ℚ) (q : ℕ) (omega N : ℝ) : Bool → List ℕ → Bool :=
  fun positive pre => if active e q omega N pre then
    frozenParityRosserPolicy false 8
      (fun ancestor => N ^ newCap (primeHistoryLogCoordinates N 8 ancestor)) positive pre
    else fourteenPolicy e q omega N positive pre

def policy (e : ℚ) (q : ℕ) (omega N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 (fourteenPolicy e q omega N)
    (continuation e q omega N)

theorem active_cons (e : ℚ) (q : ℕ) (omega N : ℝ)
    (pre : List ℕ) (hlen : 8 ≤ pre.length) (p : ℕ) :
    active e q omega N (p :: pre) ↔ active e q omega N pre := by
  simp only [active, rosserAncestor_cons 8 p pre hlen,
    rosserAncestor_cons 6 p pre (by omega : 6 ≤ pre.length)]

theorem continuation_even (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    continuation e q omega N true pre = true := by
  unfold continuation
  split_ifs
  · exact frozenParityRosserPolicy_upper_even 8 _ pre
  · exact fourteenPolicy_even e q omega N pre

theorem policy_even (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    policy e q omega N true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _
    (fourteenPolicy_even e q omega N) (continuation_even e q omega N) pre

theorem policy_through_eight (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 8) :
    policy e q omega N positive pre = fourteenPolicy e q omega N positive pre := by
  simp only [policy, firstExitDepthSplicePolicy, if_pos hlen]

theorem policy_frontier_eight (e : ℚ) (q : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (policy e q omega N) h pre positive mass carrier =
      firstExitDepthFrontier 8 (fourteenPolicy e q omega N) h pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl _ _ h pre carrier positive mass

/-- Every unselected continuation is literally the previous policy.
This includes all future leaves and arbitrary signed incoming masses. -/
theorem inactive_signed_continuation (e : ℚ) (q : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : 8 ≤ pre.length) (hinactive : ¬active e q omega N pre)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (continuation e q omega N) h T pre positive mass remaining =
      signedTest (fourteenPolicy e q omega N) h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hn : ¬active e q omega N (p :: pre) :=
      fun hp => hinactive ((active_cons e q omega N pre hlen p).mp hp)
    simp only [signedTest, continuation, if_neg hn]
    rw [ih (pre := pre) (hlen := hlen) (hinactive := hinactive)
      (positive := positive) (mass := mass),
      ih (pre := p :: pre) (hlen := by simp only [List.length_cons]; omega)
        (hinactive := hn) (positive := !positive) (mass := mass * h p)]

theorem inactive_policy_signed_continuation (e : ℚ) (q : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : 8 ≤ pre.length) (hinactive : ¬active e q omega N pre)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (policy e q omega N) h T pre positive mass remaining =
      signedTest (fourteenPolicy e q omega N) h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hn : ¬active e q omega N (p :: pre) :=
      fun hp => hinactive ((active_cons e q omega N pre hlen p).mp hp)
    have hlong : ¬(p :: pre).length ≤ 8 := by simp only [List.length_cons]; omega
    simp only [signedTest, policy, firstExitDepthSplicePolicy, if_neg hlong,
      continuation, if_neg hn]
    rw [ih (pre := pre) (hlen := hlen) (hinactive := hinactive)
      (positive := positive) (mass := mass),
      ih (pre := p :: pre) (hlen := by simp only [List.length_cons]; omega)
        (hinactive := hn) (positive := !positive) (mass := mass * h p)]

/-- The selected branch uses its one frozen original M, for the entire
continuation, rather than recomputing a child-dependent eighth cap. -/
theorem active_signed_continuation (e : ℚ) (q : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : 8 ≤ pre.length) (hactive : active e q omega N pre)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (continuation e q omega N) h T pre positive mass remaining =
      signedTest (frozenParityRosserPolicy false 8
        (fun ancestor => N ^ newCap (primeHistoryLogCoordinates N 8 ancestor)))
        h T pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
    have hn : active e q omega N (p :: pre) :=
      (active_cons e q omega N pre hlen p).mpr hactive
    simp only [signedTest, continuation, if_pos hn]
    rw [ih (pre := pre) (hlen := hlen) (hactive := hactive)
      (positive := positive) (mass := mass),
      ih (pre := p :: pre) (hlen := by simp only [List.length_cons]; omega)
        (hactive := hn) (positive := !positive) (mass := mass * h p)]

/-- The previously selected fourteen source is outside the active13
branch by its actual opposite D23/A23 halfspace. -/
theorem original_fourteen_inactive (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ)
    (ht : P2OriginalAscendingEighthCapDictionary.SelectedFamilyGuard
      P4AOriginalAscending14Literal42.literalPattern
        (primeHistoryLogCoordinates N 8 (rosserAncestor 8 pre))) :
    ¬active e q omega N pre := by
  rintro ⟨⟨i, hi⟩, _hcap⟩
  exact original_thirteen_excludes_fourteen hi ht

/-- Exact prior14 signed continuation preservation, not positivity or a
comparison of unrelated policies.  The terminal test may be full-q. -/
theorem original_fourteen_continuation_preserved (e : ℚ) (q : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (pre : List ℕ) (hlen : 8 ≤ pre.length)
    (ht : P2OriginalAscendingEighthCapDictionary.SelectedFamilyGuard
      P4AOriginalAscending14Literal42.literalPattern
        (primeHistoryLogCoordinates N 8 (rosserAncestor 8 pre)))
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (policy e q omega N) h T pre positive mass remaining =
      signedTest (fourteenPolicy e q omega N) h T pre positive mass remaining :=
  inactive_policy_signed_continuation e q omega N h T pre hlen
    (original_fourteen_inactive e q omega N pre ht) positive mass remaining

/-- On an active source the previous fourteen continuation is the actual
sixth one.  The old branch is consequently charged only once. -/
theorem active_previous_eq_sixth (e : ℚ) (q : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : 8 ≤ pre.length) (hactive : active e q omega N pre)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (fourteenPolicy e q omega N) h T pre positive mass remaining =
      signedTest (policy6 (data e q omega) N) h T pre positive mass remaining := by
  obtain ⟨i, hi⟩ := hactive.1
  exact fourteen_signed_continuation_eq_current_on_thirteen
    e q omega N i h T pre hlen hi positive mass remaining

/-- Independent occurrence-list source.  The literal full-modulus beta
test, original sign, mass and remaining carrier all stay attached. -/
def sourceChange (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier 8 (fourteenPolicy e q omega (N : ℝ))
    (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z)).map (fun state =>
      signedTest (continuation e q omega (N : ℝ)) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining -
      signedTest (fourteenPolicy e q omega (N : ℝ)) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining)).sum

theorem physical_sub_previous_eq_source (e : ℚ) (q : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ actualSmallRoughModuli (policy e q omega (N : ℝ) false) N cap w z,
      actualSmallRoughRho (policy e q omega (N : ℝ) false) N cap w z L d * G d) -
    (∑ d ∈ actualSmallRoughModuli (fourteenPolicy e q omega (N : ℝ) false) N cap w z,
      actualSmallRoughRho (fourteenPolicy e q omega (N : ℝ) false) N cap w z L d * G d) =
      sourceChange e q omega N cap w z L G := by
  have hn := physical_test_eq_signedTest (policy e q omega (N : ℝ))
    (policy_even e q omega (N : ℝ)) N cap 1 w z L G
  have ho := physical_test_eq_signedTest (fourteenPolicy e q omega (N : ℝ))
    (fourteenPolicy_even e q omega (N : ℝ)) N cap 1 w z L G
  simp only [one_mul] at hn ho
  rw [hn, ho]
  exact signedTest_splice_sub_eq_frontier 8 _ _ (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] (roughPrimeUniverse N cap w z) true 1

end
end ImbalancedChen.P4AOriginalThirteenLocalizedContinuation
