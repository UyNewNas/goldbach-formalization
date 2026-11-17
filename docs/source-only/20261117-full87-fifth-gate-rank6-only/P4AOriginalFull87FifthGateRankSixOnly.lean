import ImbalancedChen.P4AOriginalFull87ShallowOneSidedInvoice
import ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The actual RAW and LICENSED fifth queries are ODD gates. Their real fifth
levels, including the unchanged original fifth seed and the finite/inactive
fifth predecessor, are <= 299/500. Hence every actually ADMITTED fifth
history has full rough product < N^(299/500). For the original nonzero
minus small Rosser beta and epsilon <= 1/500, its complete attached
high-q term vanishes at X >= N^(3/5).

At an admitted fifth-minus root the literal stoppedTest 7 is consequently
the sum of only the accepted SIXTH-positive children. This is proved by
recursion on the ORIGINAL remaining List (not a set, a new source, or a
geometric mask). Every occurrence is retained in processing order.
No even-sixth product cap, signed saving, numerical archive or PP input
is invented. This result does not zero the surviving sixth contribution.
-/

namespace ImbalancedChen.P4AOriginalFull87FifthGateRankSixOnly
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87RankSevenStoppedHighQ
  (actual_minus_attached_highq_zero_of_rough_lt)

/-- The finite fifth predecessor has the original global ceiling on BOTH
active and inactive own-third histories, with no fifth mask imposed on
inactive predecessors. -/
private theorem finite_level5_le_original_ceiling
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (pre : List ℕ) :
    P4AOriginalFull87FiniteParentPolicy.level5Exponent
      n e q om N pre ≤ (299 / 500 : ℝ) := by
  unfold P4AOriginalFull87FiniteParentPolicy.level5Exponent
  split_ifs
  · exact P4AOriginalFull87WholeSixthCeiling.finite_cap5_le_initial_ceiling
      n e q om N he pre
  · exact P4AOriginalFull87WholeSixthCeiling.exponent5_le_initial_ceiling
      (P4AOriginalCompleteSixthChronology.data e q om) he N pre

/-- An actual ODD Rosser query at any fifth level below 299/500
controls the FULL rough product, not merely the next prime or a cap. -/
private theorem odd_gate_rough_lt_fixed_ceiling
    (N : ℕ) (hN : 1 < (N : ℝ)) (pre : List ℕ)
    (u : ℝ) (hu : u ≤ (299 / 500 : ℝ))
    (hgate : ordinaryParityRosserPolicy false ((N : ℝ) ^ u)
      false pre = true) :
    (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  have hadm : ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ u) pre := by
    simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true,
      if_false, oddFirstExitPolicy, Bool.false_or,
      decide_eq_true_eq] using hgate
  exact hadm.1.trans_le
    (Real.rpow_le_rpow_of_exponent_le hN.le hu)

/-- True RAW fifth admission reads the original fifth parent (NOT a
new sixth mask). The complete-sixth and eighth dispatch are unchanged
at this depth. -/
theorem actual_raw_fifth_gate_rough_lt
    (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ)) (pre : List ℕ)
    (hlen : pre.length = 5)
    (hgate : P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ) false pre = true) :
    (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  let d := P4AOriginalCompleteSixthChronology.data e q om
  have h5 : P5OriginalCommonRefinedConstructor.policy5 d (N : ℝ)
      false pre = true := by
    rw [P4AOriginalFull87CompleteSixthDispatch.policy_through_eight
      e q om (N : ℝ) false pre (by omega)] at hgate
    rw [P4AOriginalCompleteSixthChronology.current_policy_through_six
      e q om (N : ℝ) false pre (by omega)] at hgate
    exact hgate
  have hodd : ordinaryParityRosserPolicy false
      ((N : ℝ) ^ P5OriginalCommonRefinedConstructor.actualParent5
        d (N : ℝ) pre) false pre = true := by
    simpa only [P5OriginalCommonRefinedConstructor.policy5,
      firstExitDepthSplicePolicy,
      if_neg (show ¬pre.length ≤ 4 by omega),
      frozenParityRosserPolicy, ancestorFrozenPolicy,
      P5OriginalCommonRefinedConstructor.level5,
      P5OriginalCommonRefinedConstructor.actualParent5] using h5
  exact odd_gate_rough_lt_fixed_ceiling N hN pre
    (P5OriginalCommonRefinedConstructor.actualParent5 d (N : ℝ) pre)
    (P4AOriginalFull87WholeSixthCeiling.actualParent5_le_initial_ceiling
      d he (N : ℝ) pre) hodd

/-- True LICENSED fifth admission reads its actual finite fifth policy.
The rank-six splice cannot alter the fifth query; inactive histories
retain the full old predecessor rather than a foreign action mask. -/
theorem actual_licensed_fifth_gate_rough_lt
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ)) (pre : List ℕ)
    (hlen : pre.length = 5)
    (hgate : P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ) false pre = true) :
    (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  have h5 : P4AOriginalFull87FiniteParentPolicy.fifthPolicy
      n e q om (N : ℝ) false pre = true := by
    rw [P4AOriginalFull87LicensedSixthPolicy.through_eight
      delta n e q om (N : ℝ) false pre (by omega)] at hgate
    simpa only [P4AOriginalFull87LicensedSixthPolicy.sixthPolicy,
      firstExitDepthSplicePolicy,
      if_pos (show pre.length ≤ 6 by omega)] using hgate
  have hodd : ordinaryParityRosserPolicy false
      ((N : ℝ) ^ P4AOriginalFull87FiniteParentPolicy.level5Exponent
        n e q om (N : ℝ) pre) false pre = true := by
    simpa only [P4AOriginalFull87FiniteParentPolicy.fifthPolicy,
      firstExitDepthSplicePolicy,
      if_neg (show ¬pre.length ≤ 4 by omega),
      frozenParityRosserPolicy, ancestorFrozenPolicy,
      rosserAncestor_self_of_length 5 pre hlen] using h5
  exact odd_gate_rough_lt_fixed_ceiling N hN pre
    (P4AOriginalFull87FiniteParentPolicy.level5Exponent
      n e q om (N : ℝ) pre)
    (finite_level5_le_original_ceiling n e q om (N : ℝ) he pre) hodd

/-- At a genuinely accepted original fifth-minus history, EVERY
nonzero original minus-beta attachment has complete modulus < N^(3/5).
Consequently its exact original high-q terminal is ZERO, with the
strict high-q endpoint preserved. -/
theorem actual_admitted_fifth_attached_highq_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ)) (epsilon : ℝ)
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (pre : List ℕ) (hlen : pre.length = 5)
    (hgate : P4AOriginalFull87CompleteSixthDispatch.policy
        e q om (N : ℝ) false pre = true ∨
      P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ) false pre = true) :
    attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F) false pre = 0 := by
  have hrough : (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) :=
    hgate.elim
      (actual_raw_fifth_gate_rough_lt e q om N he hN pre hlen)
      (actual_licensed_fifth_gate_rough_lt
        delta n e q om N he hN pre hlen)
  exact actual_minus_attached_highq_zero_of_rough_lt
    N cap w hN epsilon heps X hX F pre hrough

/-- Cutoff seven at rank six sees precisely its literal terminal value:
every potential seventh selection has already reached the cutoff.
The original suffix is passed without alteration; repeated labels are
not coalesced. -/
private theorem stopped_seven_at_six_eq_literal
    (R : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 6) (mass : ℝ)
    (remaining : List ℕ) :
    stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining =
      signedTreeCoefficient true mass * T true pre := by
  have h6 : ¬ 7 ≤ pre.length := by omega
  induction remaining with
  | nil => simp [stoppedTest, h6]
  | cons p ps ih =>
      have hcut : 7 ≤ (p :: pre).length := by simp [hlen]
      have hzero :
          stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
            T (p :: pre) false (mass * (1 : ℝ)) ps = 0 := by
        cases ps with
        | nil => simp [stoppedTest, hcut]
        | cons q qs => simp [stoppedTest, hcut]
      simp [stoppedTest, h6, ih, hzero]

/-- An admitted fifth-minus root whose literal high-q terminal is zero
has a cutoff-seven invoice supported ONLY on actual accepted sixth-plus
children. The sum traverses its ORIGINAL remaining carrier in order;
a repeated prime label generates the same number of occurrences as in
stoppedTest. Crucially NO sixth-product upper bound is assumed. -/
private theorem stopped_seven_five_eq_sixth_only
    (R : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (mass : ℝ) (remaining : List ℕ)
    (hroot : T false pre = 0) :
    stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
      T pre false mass remaining =
      (remaining.map (fun p =>
        if R true (p :: pre) = true then
          signedTreeCoefficient true mass * T true (p :: pre)
        else 0)).sum := by
  have h5 : ¬ 7 ≤ pre.length := by omega
  induction remaining with
  | nil => simp [stoppedTest, h5, hroot]
  | cons p ps ih =>
      have hchild := stopped_seven_at_six_eq_literal
        R T (p :: pre) (by simp [hlen])
        (mass * (1 : ℝ)) ps
      by_cases hg : R true (p :: pre) = true
      · simp [stoppedTest, h5, hg, ih, hchild]
      · simp [stoppedTest, h5, hg, ih]

/-- Actual result for either original fifth policy, at the genuine
admitted fifth gate. This directly refines the surviving original
cutoff-seven shallow event value: rank-five physical values are zero
and only still-uncontrolled sixth-plus complete a*b tests remain. -/
theorem actual_admitted_fifth_stopped7_eq_sixth_only
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ)) (epsilon : ℝ)
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (R : Bool → List ℕ → Bool)
    (hR : R =
        P4AOriginalFull87CompleteSixthDispatch.policy
          e q om (N : ℝ) ∨
      R = P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
    (pre : List ℕ) (hlen : pre.length = 5)
    (hgate : R false pre = true)
    (mass : ℝ) (remaining : List ℕ) :
    stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre false mass remaining =
      (remaining.map (fun p =>
        if R true (p :: pre) = true then
          signedTreeCoefficient true mass *
            attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
              (highQTest X F) true (p :: pre)
        else 0)).sum := by
  have hactual :
      P4AOriginalFull87CompleteSixthDispatch.policy
        e q om (N : ℝ) false pre = true ∨
      P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ) false pre = true := by
    rcases hR with hr | hl
    · left; rw [← hr]; exact hgate
    · right; rw [← hl]; exact hgate
  have hz := actual_admitted_fifth_attached_highq_zero
    delta n e q om N cap w he hN epsilon heps X hX F
    pre hlen hactual
  exact stopped_seven_five_eq_sixth_only R
    (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F)) pre hlen mass remaining hz

end
end ImbalancedChen.P4AOriginalFull87FifthGateRankSixOnly
