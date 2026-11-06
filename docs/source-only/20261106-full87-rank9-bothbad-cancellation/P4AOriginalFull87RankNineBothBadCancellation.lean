import ImbalancedChen.P4AOriginalFull87RankNineHistoryRisk
import ImbalancedChen.P4AOriginalFull87RankNineInheritedSplit
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: cancellation of the ACTUAL rank-nine physical correction on
original87 eighth histories failing the inherited upper-square guard
at BOTH actual frozen levels.

The earlier invoice bounds the absolute inherited contribution at each
level. Here we do something DIFFERENT: extract only the first-choice
failures from the literal first-exit recursion and prove that the WHOLE
rank-nine signed correction is identical when both inherited guards fail.
No continuation below rank nine is compared, and the prioritized
total/inherited/new-square mode labels need not match.

This is not a small-error estimate, not an arithmetic full-q
identification, and not a reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNineBothBadCancellation
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier states_eq_owner_filter frontier_sign_mass)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction
  (actualFrozenPost8Level)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts
   failed_attempt_mem_valid_prefix_and_suffix)
open P4AOriginalFull87SignedDeletionLedger (physicalFailedAt)
open P4AOriginalFull87CorrectionRankTerminal
  (rankNinePhysicalFailedAt rankNineSigned ownedRankNineSigned)
open P4AOriginalFull87RankNineInheritedSplit
  (owned87_actual_rank_nine_rejected_iff)

/-- The genuine possible first-choice rejected occurrences. These are
NOT a new policy or a replacement source: the following theorem proves
that this list is the rank-nine filter of the existing recursive source.
Each candidate retains the actual smaller suffix, incoming mass and sign. -/
private def rootRejectedAttempts {α : Type*}
    (policy : Bool → List α → Bool)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FirstExitRejectedAttempt α)
  | [] => []
  | p :: ps =>
      rootRejectedAttempts policy pre positive mass ps ++
        if policy (!positive) (p :: pre) = true then []
        else [{ older := pre, rejected := p, smaller := ps,
                positive := positive, mass := mass }]

/-- Once a selected prime has been inserted after depth eight,
none of the subsequently rejected descendants can be a ninth-rank
occurrence. No statement about whether their policies pass is needed. -/
private theorem deep_firstExit_has_no_rankNine {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (hdeep : 8 < pre.length) :
    (firstExitRejectedAttempts policy h pre positive mass remaining).filter
      (fun a => decide (a.older.length ≤ 8)) = [] := by
  classical
  cases hlist :
      (firstExitRejectedAttempts policy h pre positive mass remaining).filter
        (fun a => decide (a.older.length ≤ 8)) with
  | nil => rfl
  | cons a tail =>
      have ha : a ∈
          (firstExitRejectedAttempts policy h pre positive mass remaining).filter
            (fun b => decide (b.older.length ≤ 8)) := by
        rw [hlist]
        simp
      obtain ⟨hsource, htag⟩ := List.mem_filter.mp ha
      have hle : a.older.length ≤ 8 := of_decide_eq_true htag
      obtain ⟨before, chosen, _, _, _, hword⟩ :=
        failed_attempt_mem_valid_prefix_and_suffix
          policy h pre remaining positive mass a hsource
      have hge : pre.length ≤ a.older.length := by
        rw [hword]
        simp only [List.length_append, List.length_reverse]
        omega
      omega

/-- Exact occurrence-level extraction, not just equality of signed sums.
Every genuine ninth rejection is a failed first selection of the SAME
prime and suffix in the SAME original remaining word. The accepted
select branch contributes only ranks at least ten. -/
theorem firstExit_rankNine_eq_root_rejections {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (h8 : pre.length = 8) :
    (firstExitRejectedAttempts policy h pre positive mass remaining).filter
      (fun a => decide (a.older.length ≤ 8)) =
        rootRejectedAttempts policy pre positive mass remaining := by
  classical
  induction remaining with
  | nil =>
      simp [firstExitRejectedAttempts, rootRejectedAttempts]
  | cons p ps ih =>
      by_cases hp : policy (!positive) (p :: pre) = true
      · have hdeep :
            (firstExitRejectedAttempts policy h (p :: pre) (!positive)
                (mass * h p) ps).filter
              (fun a => decide (a.older.length ≤ 8)) = [] :=
          deep_firstExit_has_no_rankNine
            policy h (p :: pre) ps (!positive) (mass * h p) (by simp [h8])
        simp [firstExitRejectedAttempts, rootRejectedAttempts, hp,
          List.filter_append, ih, hdeep]
      · simp [firstExitRejectedAttempts, rootRejectedAttempts, hp,
          List.filter_append, ih, h8]

/-- If both policies reject every first choice, the literal ninth-rank
occurrence lists coincide, even when their later branches and priority
tags differ. This lemma is purely finite select/skip arithmetic. -/
private theorem root_rejections_eq_of_all_failed {α : Type*}
    (P Q : Bool → List α → Bool)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    (∀ p ∈ remaining, P (!positive) (p :: pre) = false) →
    (∀ p ∈ remaining, Q (!positive) (p :: pre) = false) →
    rootRejectedAttempts P pre positive mass remaining =
      rootRejectedAttempts Q pre positive mass remaining := by
  induction remaining with
  | nil =>
      intro _ _
      rfl
  | cons p ps ih =>
      intro hP hQ
      have hp : P (!positive) (p :: pre) = false := hP p (by simp)
      have hq : Q (!positive) (p :: pre) = false := hQ p (by simp)
      have hPt : ∀ x ∈ ps, P (!positive) (x :: pre) = false := by
        intro x hx
        exact hP x (by simp [hx])
      have hQt : ∀ x ∈ ps, Q (!positive) (x :: pre) = false := by
        intro x hx
        exact hQ x (by simp [hx])
      simp [rootRejectedAttempts, hp, hq, ih hPt hQt]

/-- Genuine eighth source, genuine old/new frozen levels, same physical
root prefix and target-deleted remaining prime carrier. If BOTH old and
new historical upper-square conditions fail, EVERY ninth select attempt
fails at BOTH levels. Consequently their full ninth failure lists
coincide. The two inherited *mode* lists need not coincide, since the
total-priority classification can still differ. -/
theorem actual_rankNine_lists_equal_of_both_history_bad
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hbadParent :
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        (actualFrozenPost8Level n e q om N c s true)
        s.selectedPrefix.toFinset)
    (hbadCap :
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        (actualFrozenPost8Level n e q om N c s false)
        s.selectedPrefix.toFinset) :
    rankNinePhysicalFailedAt n e q om N c s true =
      rankNinePhysicalFailedAt n e q om N c s false := by
  have h8 : s.selectedPrefix.length = 8 :=
    (owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs).1
  have hfront : s ∈ frontier n e q om N cap w z := by
    have ht := hs
    rw [states_eq_owner_filter] at ht
    exact (List.mem_filter.mp ht).1
  have hpos : s.positive = true :=
    (frontier_sign_mass n e q om N cap w z s hfront).1
  have hP : ∀ p ∈ s.remaining,
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s true)
        (!s.positive) (p :: s.selectedPrefix) = false := by
    intro p hp
    have hr :=
      (owned87_actual_rank_nine_rejected_iff
        delta n e q om N cap w z c s hs true p hp).mpr
        (Or.inr (Or.inl hbadParent))
    simpa [hpos] using hr
  have hQ : ∀ p ∈ s.remaining,
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s false)
        (!s.positive) (p :: s.selectedPrefix) = false := by
    intro p hp
    have hr :=
      (owned87_actual_rank_nine_rejected_iff
        delta n e q om N cap w z c s hs false p hp).mpr
        (Or.inr (Or.inl hbadCap))
    simpa [hpos] using hr
  let rootMass : ℝ :=
    s.mass * (s.selectedPrefix.map halfProductDensity).prod
  calc
    rankNinePhysicalFailedAt n e q om N c s true =
        rootRejectedAttempts
          (ordinaryParityRosserPolicy false
            (actualFrozenPost8Level n e q om N c s true))
          s.selectedPrefix s.positive rootMass s.remaining := by
            change
              (firstExitRejectedAttempts
                (ordinaryParityRosserPolicy false
                  (actualFrozenPost8Level n e q om N c s true))
                halfProductDensity s.selectedPrefix s.positive rootMass
                s.remaining).filter
                (fun a => decide (a.older.length ≤ 8)) = _
            exact firstExit_rankNine_eq_root_rejections
              _ _ _ _ _ _ h8
    _ = rootRejectedAttempts
          (ordinaryParityRosserPolicy false
            (actualFrozenPost8Level n e q om N c s false))
          s.selectedPrefix s.positive rootMass s.remaining :=
            root_rejections_eq_of_all_failed _ _ _ _ _ _ hP hQ
    _ = rankNinePhysicalFailedAt n e q om N c s false := by
          change
            rootRejectedAttempts
              (ordinaryParityRosserPolicy false
                (actualFrozenPost8Level n e q om N c s false))
              s.selectedPrefix s.positive rootMass s.remaining =
              (firstExitRejectedAttempts
                (ordinaryParityRosserPolicy false
                  (actualFrozenPost8Level n e q om N c s false))
                halfProductDensity s.selectedPrefix s.positive rootMass
                s.remaining).filter
                (fun a => decide (a.older.length ≤ 8))
          exact (firstExit_rankNine_eq_root_rejections
            _ _ _ _ _ _ h8).symm

/-- The complete physical rank-nine signed gap vanishes in this
double-bad region. We do NOT infer that either signed sum is zero. -/
theorem actual_rankNine_gap_zero_of_both_history_bad
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hbadParent :
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        (actualFrozenPost8Level n e q om N c s true)
        s.selectedPrefix.toFinset)
    (hbadCap :
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        (actualFrozenPost8Level n e q om N c s false)
        s.selectedPrefix.toFinset) :
    rankNineSigned n e q om N c s true -
      rankNineSigned n e q om N c s false = 0 := by
  have heq := actual_rankNine_lists_equal_of_both_history_bad
    delta n e q om N cap w z c s hs hbadParent hbadCap
  unfold rankNineSigned
  rw [heq, sub_self]

/-- A support filter on the ORIGINAL ordered owner/trim eighth-state
list. At least one historical upper-square guard must pass for a
nonzero OLD-MINUS-NEW rank-nine gap. It is NOT a new sieve mask:
the original correction is merely re-expressed on this support. -/
def ownedRankNineComparisonSupport
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c).filter (fun s =>
        decide
          (LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
            (actualFrozenPost8Level n e q om N c s true)
            s.selectedPrefix.toFinset ∨
           LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
            (actualFrozenPost8Level n e q om N c s false)
            s.selectedPrefix.toFinset))

private theorem list_map_sum_sub {α : Type*} (xs : List α)
    (f g : α → ℝ) :
    ((xs.map (fun x => f x - g x)).sum) =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem list_sum_filter_of_zero {α : Type*}
    (xs : List α) (f : α → ℝ) (P : α → Prop)
    [DecidablePred P]
    (hzero : ∀ x ∈ xs, ¬ P x → f x = 0) :
    (xs.map f).sum =
      ((xs.filter (fun x => decide (P x))).map f).sum := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
      have htail : ∀ y ∈ ys, ¬ P y → f y = 0 := by
        intro y hy hnot
        exact hzero y (by simp [hy]) hnot
      by_cases hp : P x
      · simp [hp, ih htail]
      · have hx : f x = 0 := hzero x (by simp) hp
        simp [hp, hx, ih htail]

/-- Exact full87 owner-cell OLD-MINUS-NEW rank-nine signed-gap support.
The potentially large two-sided inherited invoices are NOT a necessary
cost on states where both historical guards fail: there the genuine
signed difference cancels occurrence by occurrence. The result does
not bound the surviving support or other ninth modes, does not pay
either reserve, and does not identify the full-q arithmetic saving. -/
theorem owned_rankNine_gap_eq_one_history_guard_passes
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    ownedRankNineSigned r n e q om N cap w z c true -
      ownedRankNineSigned r n e q om N cap w z c false =
      ((ownedRankNineComparisonSupport r n e q om N cap w z c).map
        (fun s => rankNineSigned n e q om N c s true -
          rankNineSigned n e q om N c s false)).sum := by
  classical
  unfold ownedRankNineSigned ownedRankNineComparisonSupport
  rw [← list_map_sum_sub]
  apply list_sum_filter_of_zero
  intro s hs hnot
  have hbadParent :
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        (actualFrozenPost8Level n e q om N c s true)
        s.selectedPrefix.toFinset := by
    intro hp
    exact hnot (Or.inl hp)
  have hbadCap :
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        (actualFrozenPost8Level n e q om N c s false)
        s.selectedPrefix.toFinset := by
    intro hp
    exact hnot (Or.inr hp)
  exact actual_rankNine_gap_zero_of_both_history_bad
    (width r) n e q om N cap w z c s hs hbadParent hbadCap

end
end ImbalancedChen.P4AOriginalFull87RankNineBothBadCancellation
