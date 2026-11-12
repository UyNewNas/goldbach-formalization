import ImbalancedChen.P4AOriginalFull87PostEightAttachedLevel
import ImbalancedChen.P4AOriginalFull87SeventhExhaustion
import ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

This packet closes the literal rank-SEVEN EXCLUSIVE early-stop contribution,
not the entire pre-eight stopped contribution. It uses the ORIGINAL raw
complete-sixth and licensed-sixth policies at their actual rank-seven gate,
their separate real frozen-sixth exponents, and the unchanged sign-selected
minus small Rosser coefficient.

A selected rank-seven query has sign false. The gate then checks the FULL
Rosser prefix, including strict product support. The two true seventh gates
both imply product < N^(299/500), while actual nonzero minus beta gives
a < N^epsilon. Thus each admitted seventh terminal has complete
modulus a*b < N^(3/5) when epsilon <= 1/500 is fixed before N.
At high-q X >= N^(3/5), the actual attached terminal is zero.

At a true even-sign sixth prefix, both stoppedTest recursions therefore
have identical skip-only high-q values: every accepted seventh branch
is literally zero in its own original policy. This is a finite arithmetic
elimination of the previously retained seventh-exclusive net source,
not an assumption of a signed gain, a PP theorem, or a reserve budget.

The fifth/sixth exclusive stopped subtrees, raw eighth frontier,
whole small-epsilon compatibility, ordinary integral and numerical archive
remain OPEN. Source-only imports require path mapping for any Lean build.
-/

namespace ImbalancedChen.P4AOriginalFull87RankSevenStoppedHighQ
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SeventhExhaustion
  (stopped_seven_eq_literal_terminal stopped_difference_eq_seventh_exclusives
   seventhExclusiveEvents)

/-- A genuine admitted RAW rank-seven gate, on its OWN sixth ancestor,
controls the complete rough prefix product. It is not a scalar-cap
monotonicity assertion about arbitrary history words. -/
theorem raw_rank_seven_gate_rough_lt
    (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (pre : List ℕ) (hlen : pre.length = 7)
    (hgate : P4AOriginalFull87CompleteSixthDispatch.policy
      e q om (N : ℝ) false pre = true) :
    (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  have hp : ordinaryParityRosserPolicy false
      ((N : ℝ) ^ P4AOriginalCompleteSixthChronology.currentSixthExponent
        e q om (N : ℝ) (rosserAncestor 6 pre)) false pre = true := by
    rw [P4AOriginalFull87CompleteSixthDispatch.policy_through_eight
      e q om (N : ℝ) false pre (by omega)] at hgate
    rw [P4AOriginalCompleteSixthChronology.current_policy_after_six
      e q om (N : ℝ) false pre (by omega)] at hgate
    exact hgate
  have hadm : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ P4AOriginalCompleteSixthChronology.currentSixthExponent
        e q om (N : ℝ) (rosserAncestor 6 pre)) pre := by
    simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true,
      if_false, oddFirstExitPolicy, Bool.false_or,
      decide_eq_true_eq] using hp
  exact hadm.1.trans_le <|
    Real.rpow_le_rpow_of_exponent_le hN.le
      (P4AOriginalFull87WholeSixthCeiling.raw_currentSixth_le_initial_ceiling
        e q om (N : ℝ) he (rosserAncestor 6 pre))

/-- The independently admitted LICENSED rank-seven gate has the SAME
numerical envelope but its own actual sixth cap and own selected history.
No equality of the two sixth policies is assumed. -/
theorem licensed_rank_seven_gate_rough_lt
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (pre : List ℕ) (hlen : pre.length = 7)
    (hgate : P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ) false pre = true) :
    (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  have hp : ordinaryParityRosserPolicy false
      ((N : ℝ) ^ P4AOriginalFull87LicensedSixthPolicy.level6Exponent
        n e q om (N : ℝ) (rosserAncestor 6 pre)) false pre = true := by
    rw [P4AOriginalFull87LicensedSixthPolicy.through_eight
      delta n e q om (N : ℝ) false pre (by omega)] at hgate
    simpa only [P4AOriginalFull87LicensedSixthPolicy.sixthPolicy,
      firstExitDepthSplicePolicy,
      if_neg (show ¬pre.length ≤ 6 by omega),
      frozenParityRosserPolicy, ancestorFrozenPolicy] using hgate
  have hadm : ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ P4AOriginalFull87LicensedSixthPolicy.level6Exponent
        n e q om (N : ℝ) (rosserAncestor 6 pre)) pre := by
    simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true,
      if_false, oddFirstExitPolicy, Bool.false_or,
      decide_eq_true_eq] using hp
  exact hadm.1.trans_le <|
    P4AOriginalFull87WholeSixthCeiling.level6_power_le_initial_ceiling
      n e q om (N : ℝ) he hN.le (rosserAncestor 6 pre)

/-- Actual sign-MINUS seventh attached terminal vanishes above the full
a*b threshold. The strict small factor comes from NONZERO original beta,
not from mere membership of the displayed small carrier. -/
private theorem actual_seventh_minus_attached_highq_zero
    (N cap : ℕ) (w : ℝ)
    (hN : 1 < (N : ℝ)) (epsilon : ℝ)
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (pre : List ℕ)
    (hrough : (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ)) :
    attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F) false pre = 0 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (by norm_num) hN
  have hexp : epsilon + (299 / 500 : ℝ) ≤ (3 / 5 : ℝ) := by
    linarith
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  change actualSmallRosserMinus N cap w ((N : ℝ) ^ epsilon) a *
    highQTest X F (a * pre.prod) = 0
  by_cases hb : actualSmallRosserMinus N cap w ((N : ℝ) ^ epsilon) a = 0
  · simp [hb]
  · have hsmall : (a : ℝ) < (N : ℝ) ^ epsilon :=
      (actualSmallRosserMinus_active hb).2.1
    have hmod : ((a * pre.prod : ℕ) : ℝ) <
        (N : ℝ) ^ (3 / 5 : ℝ) := by
      calc
        ((a * pre.prod : ℕ) : ℝ) =
            (a : ℝ) * (pre.prod : ℝ) := by push_cast; ring
        _ ≤ (a : ℝ) * (N : ℝ) ^ (299 / 500 : ℝ) :=
          mul_le_mul_of_nonneg_left hrough.le (Nat.cast_nonneg a)
        _ < (N : ℝ) ^ epsilon * (N : ℝ) ^ (299 / 500 : ℝ) :=
          mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hNpos _)
        _ = (N : ℝ) ^ (epsilon + (299 / 500 : ℝ)) := by
          rw [Real.rpow_add hNpos]
        _ ≤ (N : ℝ) ^ (3 / 5 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN.le hexp
    have hcut : ¬ X < a * pre.prod := by
      apply Nat.not_lt.mpr
      exact_mod_cast ((le_of_lt hmod).trans hX)
    simp [highQTest, hcut]

/-- Both true original seventh gates pay ZERO high-q on their own actual
terminal; no policy equality, extra geometry mask, or discarded sign. -/
theorem actual_admitted_seventh_terminal_highq_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (pre : List ℕ) (hlen : pre.length = 7)
    (hgate :
      P4AOriginalFull87CompleteSixthDispatch.policy
        e q om (N : ℝ) false pre = true ∨
      P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ) false pre = true) :
    attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F) false pre = 0 := by
  have hrough : (pre.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) :=
    hgate.elim
      (raw_rank_seven_gate_rough_lt e q om N he hN pre hlen)
      (licensed_rank_seven_gate_rough_lt delta n e q om N he hN pre hlen)
  exact actual_seventh_minus_attached_highq_zero
    N cap w hN epsilon heps X hX F pre hrough

/-- Finite tree algebra only: if every true seventh selected gate has
zero literal terminal value, then at rank SIX the two stopped recursions
are identical. Their common rank-six skip-only value remains; this does
NOT declare the stopped functions themselves zero. -/
private theorem rank_six_stopped_equal_of_seventh_zero
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hpre : pre.length = 6) (mass : ℝ)
    (hzR : ∀ p, R false (p :: pre) = true → T false (p :: pre) = 0)
    (hzS : ∀ p, S false (p :: pre) = true → T false (p :: pre) = 0)
    (remaining : List ℕ) :
    stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
      pre true mass remaining =
    stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
      pre true mass remaining := by
  have hk : ¬ 8 ≤ pre.length := by omega
  induction remaining with
  | nil =>
      simp [stoppedTest, hk]
  | cons p ps ih =>
      have hlen7 : (p :: pre).length = 7 := by simp [hpre]
      have hrr := stopped_seven_eq_literal_terminal
        R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) ps hlen7
      have hss := stopped_seven_eq_literal_terminal
        S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) ps hlen7
      by_cases hr : R false (p :: pre) = true
      · have hzrr : stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
            (p :: pre) false (mass * (1 : ℝ)) ps = 0 := by
          rw [hrr, hzR p hr, mul_zero]
        by_cases hs : S false (p :: pre) = true
        · have hzss : stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
              (p :: pre) false (mass * (1 : ℝ)) ps = 0 := by
            rw [hss, hzS p hs, mul_zero]
          simp [stoppedTest, hk, hr, hs, hzrr, hzss, ih]
        · simp [stoppedTest, hk, hr, hs, hzrr, ih]
      · by_cases hs : S false (p :: pre) = true
        · have hzss : stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
              (p :: pre) false (mass * (1 : ℝ)) ps = 0 := by
            rw [hss, hzS p hs, mul_zero]
          simp [stoppedTest, hk, hr, hs, hzss, ih]
        · simp [stoppedTest, hk, hr, hs, ih]

/-- Genuine rank-six BOTH branch: independent raw and licensed seventh
decisions produce the SAME pre-eight stopped high-q contribution.
This eliminates only their rank-seven difference; fifth/sixth-exclusive
subtrees are not silently dropped. -/
theorem actual_rank_six_stopped_difference_zero_at_highq
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (pre : List ℕ) (hpre : pre.length = 6)
    (mass : ℝ) (remaining : List ℕ) :
    stoppedTest 8
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre true mass remaining -
    stoppedTest 8
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre true mass remaining = 0 := by
  apply sub_eq_zero.mpr
  refine rank_six_stopped_equal_of_seventh_zero
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
    pre hpre mass ?_ ?_ remaining
  · intro p hp
    exact actual_admitted_seventh_terminal_highq_zero
      delta n e q om N cap w he hN epsilon heps X hX F
      (p :: pre) (by simp [hpre]) (Or.inl hp)
  · intro p hp
    exact actual_admitted_seventh_terminal_highq_zero
      delta n e q om N cap w he hN epsilon heps X hX F
      (p :: pre) (by simp [hpre]) (Or.inr hp)

/-- Existing exact seventh-exclusive event sum is now ZERO on the same
real sixth prefix, rather than being carried as an unpaid seventh bill. -/
theorem actual_seventh_exclusive_signed_sum_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (pre : List ℕ) (hpre : pre.length = 6)
    (mass : ℝ) (remaining : List ℕ) :
    ((seventhExclusiveEvents
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
      pre true mass remaining).map (fun event => event.signedValue)).sum = 0 := by
  rw [← stopped_difference_eq_seventh_exclusives
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
    pre true mass remaining hpre]
  exact actual_rank_six_stopped_difference_zero_at_highq
    delta n e q om N cap w he hN epsilon heps X hX F
    pre hpre mass remaining

end
end ImbalancedChen.P4AOriginalFull87RankSevenStoppedHighQ
