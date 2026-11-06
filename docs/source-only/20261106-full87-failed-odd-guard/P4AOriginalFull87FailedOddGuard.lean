import ImbalancedChen.P4AOriginalFull87FailedAttempts
import ImbalancedChen.P4AOriginalFull87InheritedOddSquares
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No formal acceptance claimed.

P1.4: a failed physical select attempt after at least two post-eight
successes has a preceding successfully selected ODD prefix at exactly
the same frozen ordinary level. This is reconstructed from the literal
FirstExitValidSelection witness and the actual event sign, not inferred
from a terminal leaf or a test at a different historic level.

Rank nine is deliberately excluded. The final finite implication uses
the old odd guard to remove inherited-square and total-product failure
for rank eleven and later, at the same original87 occurrence and level.
No density, asymptotic or numerical reserve is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87FailedOddGuard

noncomputable section
open scoped Classical
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier frontier_sign_mass states_eq_owner_filter)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts
   owned87_failed_attempt_actual_source
   failed_attempt_mem_valid_prefix_and_suffix)
open P4AOriginalFull87InheritedOddSquares
  (upper_reject_after_certified_odd_iff_last_square)

/-- The event sign is inherited from the literal successful select/skip
recursion. It is therefore the parity of its actual reversed prefix. -/
theorem rejected_attempt_sign_parity {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (hstart : positive = evenListLength pre)
    (a : FirstExitRejectedAttempt α)
    (ha : a ∈ firstExitRejectedAttempts policy h pre positive mass remaining) :
    a.positive = evenListLength a.older := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [firstExitRejectedAttempts] at ha
  | cons p ps ih =>
      by_cases ht : policy (!positive) (p :: pre) = true
      · rw [firstExitRejectedAttempts, if_pos ht, List.mem_append] at ha
        rcases ha with hskip | hselect
        · exact ih pre positive mass hstart a hskip
        · have hn : (!positive) = evenListLength (p :: pre) := by
            simpa [evenListLength] using congrArg (!) hstart
          exact ih (p :: pre) (!positive) (mass * h p) hn a hselect
      · rw [firstExitRejectedAttempts, if_neg ht,
          List.mem_append, List.mem_singleton] at ha
        rcases ha with hskip | hnow
        · exact ih pre positive mass hstart a hskip
        · subst a
          exact hstart

private theorem evenListLength_decide_even {α : Type*} (xs : List α) :
    evenListLength xs = decide (Even xs.length) := by
  induction xs with
  | nil => simp [evenListLength]
  | cons x xs ih =>
      simp only [evenListLength, ih, List.length_cons,
        Nat.even_add_one, decide_not]

/-- Every nonempty even-length chronology really has two last selected
occurrences. This retains the original list and its multiplicity. -/
theorem even_nonempty_has_last_pair {α : Type*}
    (xs : List α) (heven : Even xs.length) (hne : xs ≠ []) :
    ∃ (past : List α) (r q : α), xs = past ++ [r, q] := by
  cases hrev : xs.reverse with
  | nil =>
      have hx : xs = [] := by
        have h := congrArg List.reverse hrev
        simpa using h
      exact (hne hx).elim
  | cons q tail =>
      cases tail with
      | nil =>
          have hl : xs.length = 1 := by
            have h := congrArg List.length hrev
            simpa using h
          rcases heven with ⟨k, hk⟩
          omega
      | cons r pastRev =>
          refine ⟨pastRev.reverse, r, q, ?_⟩
          calc
            xs = xs.reverse.reverse := by simp
            _ = (q :: r :: pastRev).reverse := by rw [hrev]
            _ = pastRev.reverse ++ [r, q] := by
              simp [List.reverse_cons, List.append_assoc]

/-- A genuine VALID chosen chronology passing through r then q records
the test for r as the previous odd test when the prefix before r has
even selection parity. The test is at the SAME policy and level.
No assumption is made about the incoming historical prefix's tests. -/
theorem validSelection_prior_odd_guard {α : Type*}
    (policy : Bool → List α → Bool) (pre : List α)
    (positive : Bool) (past : List α) (r q : α)
    (hphase : positive = decide (Even past.length))
    (hvalid : FirstExitValidSelection policy pre positive
      (past ++ [r, q])) :
    policy false (r :: past.reverse ++ pre) = true := by
  induction past generalizing pre positive with
  | nil =>
      have hp : positive = true := by simpa using hphase
      have hr : policy (!positive) (r :: pre) = true := hvalid.1
      simpa [hp] using hr
  | cons x xs ih =>
      have htail : FirstExitValidSelection policy (x :: pre)
          (!positive) (xs ++ [r, q]) := hvalid.2
      have hphase' : (!positive) = decide (Even xs.length) := by
        simpa only [List.length_cons, Nat.even_add_one,
          decide_not, Bool.not_not] using congrArg (!) hphase
      have hr := ih (x :: pre) (!positive) hphase' htail
      simpa only [List.reverse_cons, List.append_assoc,
        List.singleton_append] using hr

/-- A REAL rank-eleven-or-later failed attempt on an owned original87
eighth-frontier occurrence has the preceding accepted odd prefix at
the same parent/new-cap level. q is the most recent accepted even-rank
prime and r the preceding accepted odd-rank prime. -/
theorem owned87_later_failure_has_prior_odd_guard
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ firstExitRejectedAttempts
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (hlater : 8 < a.older.length) :
    ∃ (past : List ℕ) (r q' : ℕ),
      a.older = q' :: r :: (past.reverse ++ s.selectedPrefix) ∧
      a.rejected < q' ∧ q' < r ∧
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent)
        false (r :: past.reverse ++ s.selectedPrefix) = true := by
  obtain ⟨hlen, _, hremaining, _, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  have hfront : s ∈ frontier n e q om N cap w z := by
    have hh := hs
    rw [states_eq_owner_filter] at hh
    exact (List.mem_filter.mp hh).1
  have hspos : s.positive = true :=
    (frontier_sign_mass n e q om N cap w z s hfront).1
  have hstart : s.positive = evenListLength s.selectedPrefix := by
    rw [hspos, evenListLength_decide_even, hlen]
    decide
  obtain ⟨before, chosen, _hrem, hsub, hvalid, holder, _hfail,
      hapos, hrank, _, habove⟩ :=
    owned87_failed_attempt_actual_source
      delta n e q om N cap w z c s hs useParent a ha
  have hevent : a.positive = evenListLength a.older :=
    rejected_attempt_sign_parity
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.remaining s.positive s.mass
      hstart a ha
  have heventEven : Even a.older.length := by
    have hh : decide (Even a.older.length) = true := by
      rw [← evenListLength_decide_even, ← hevent, hapos]
    exact of_decide_eq_true hh
  have hchosenEven : Even chosen.length := by
    rw [hrank] at heventEven
    omega
  have hchosenNe : chosen ≠ [] := by
    intro hz
    simp [hz] at hrank
    omega
  obtain ⟨past, r, q', hchosen⟩ :=
    even_nonempty_has_last_pair chosen hchosenEven hchosenNe
  have horder : chosen.Pairwise (· > ·) :=
    hremaining.sublist hsub
  have hrevorder : chosen.reverse.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using horder
  have hrev : chosen.reverse = q' :: r :: past.reverse := by
    rw [hchosen]
    simp [List.reverse_append]
  have hqrbig : q' < r := by
    have hh : (q' :: r :: past.reverse).Pairwise (· < ·) := by
      simpa only [hrev] using hrevorder
    exact (List.pairwise_cons.mp hh).1 r (by simp)
  have hqchosen : q' ∈ chosen := by
    rw [hchosen]
    simp
  have hpq : a.rejected < q' := habove q' hqchosen
  have hphasePast : s.positive = decide (Even past.length) := by
    have hl : chosen.length = past.length + 2 := by
      rw [hchosen]
      simp
    have hevenPast : Even past.length := by
      rw [hl] at hchosenEven
      omega
    rw [hspos]
    exact (decide_eq_true hevenPast).symm
  have hprior : ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent)
        false (r :: past.reverse ++ s.selectedPrefix) = true :=
    validSelection_prior_odd_guard
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      s.selectedPrefix s.positive past r q' hphasePast
      (by simpa only [hchosen] using hvalid)
  refine ⟨past, r, q', ?_, hpq, hqrbig, hprior⟩
  rw [holder, hrev]
  rfl

/-- With actual original87 sorted carrier, the last failed ODD test
at rank >= 11 is exactly the NEW least-prime square failure. Neither
the inherited squares nor the total-product cutoff may be silently
counted as a separate rejected mode. Still no log/N conversion. -/
theorem owned87_later_failure_last_square
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ firstExitRejectedAttempts
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (hlater : 8 < a.older.length) :
    actualFrozenPost8Level n e q om N c s useParent ≤
      (((a.rejected :: a.older).prod : ℕ) : ℝ) *
        (a.rejected : ℝ) ^ 2 := by
  let R := actualFrozenPost8Level n e q om N c s useParent
  obtain ⟨past, r, q', holder, hpq, hqr, hprior⟩ :=
    owned87_later_failure_has_prior_odd_guard
      delta n e q om N cap w z c s hs useParent a ha hlater
  obtain ⟨_, hselected, hremaining, hboundary, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  obtain ⟨before, chosen, _hrem, hsub, _, hchosenOld, hfailed,
      hpositive, _, _, _⟩ :=
    owned87_failed_attempt_actual_source
      delta n e q om N cap w z c s hs useParent a ha
  have hchosenSort : chosen.Pairwise (· > ·) :=
    hremaining.sublist hsub
  have hrevSort : chosen.reverse.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using hchosenSort
  have hcross : ∀ x ∈ chosen.reverse,
      ∀ y ∈ s.selectedPrefix, x < y := by
    intro x hx y hy
    exact hboundary x (hsub.subset (List.mem_reverse.mp hx)) y hy
  have hfullSort : a.older.Pairwise (· < ·) := by
    rw [hchosenOld]
    exact List.pairwise_append.mpr ⟨hrevSort, hselected, hcross⟩
  have htwoSort :
      (q' :: r :: (past.reverse ++ s.selectedPrefix)).Pairwise (· < ·) := by
    simpa only [holder] using hfullSort
  have hoddSort :
      (r :: (past.reverse ++ s.selectedPrefix)).Pairwise (· < ·) :=
    (List.pairwise_cons.mp htwoSort).2
  have hnodup : (r :: (past.reverse ++ s.selectedPrefix)).Nodup :=
    hoddSort.nodup
  have hqsmall : ∀ x ∈ (r :: past.reverse ++ s.selectedPrefix).toFinset,
      q' < x := by
    intro x hx
    exact (List.pairwise_cons.mp htwoSort).1 x (List.mem_toFinset.mp hx)
  have hsLen : s.selectedPrefix.length = 8 := by
    exact (owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs).1
  have hevent : a.positive = evenListLength a.older := by
    have hfront : s ∈ frontier n e q om N cap w z := by
      have hh := hs
      rw [states_eq_owner_filter] at hh
      exact (List.mem_filter.mp hh).1
    have hspos : s.positive = true :=
      (frontier_sign_mass n e q om N cap w z s hfront).1
    have hstart : s.positive = evenListLength s.selectedPrefix := by
      rw [hspos, evenListLength_decide_even, hsLen]
      decide
    exact rejected_attempt_sign_parity
      (ordinaryParityRosserPolicy false R) (fun _ : ℕ => 1)
      s.selectedPrefix s.remaining s.positive s.mass hstart a ha
  have hodd : Odd (r :: (past.reverse ++ s.selectedPrefix)).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup]
    have hlen : a.older.length =
        (r :: (past.reverse ++ s.selectedPrefix)).length + 1 := by
      rw [holder]
      simp
    have hEven : Even a.older.length := by
      have hh : decide (Even a.older.length) = true := by
        rw [← evenListLength_decide_even, ← hevent, hpositive]
      exact of_decide_eq_true hh
    rcases hEven with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  have hfailedOdd : ordinaryParityRosserPolicy false R false
      (a.rejected :: q' :: r :: past.reverse ++ s.selectedPrefix) = false := by
    simpa only [holder, hpositive, Bool.not_true] using hfailed
  have hbound :=
    (upper_reject_after_certified_odd_iff_last_square
      R (r :: past.reverse ++ s.selectedPrefix)
      a.rejected q' hodd hnodup hpq hqsmall hprior).mp hfailedOdd
  simpa only [holder] using hbound

end
end ImbalancedChen.P4AOriginalFull87FailedOddGuard
