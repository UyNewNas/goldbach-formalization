import ImbalancedChen.P4AOriginalFull87ActualEighthCarrier
import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

P1.4: expose actual failed *selection attempts* in the literal first-exit
select/skip recursion, instead of treating a retained terminal leaf as an
exit. An attempt keeps its occurrence (including the unprocessed strict
suffix), current selected history, incoming sign, and unsigned mass.

The enumeration is proved equal to the pre-existing signed
firstExitCorrection; hence these are the genuine physical correction
terms, not a new weight or a synthetic family of rejected prefixes.
Each enumerated failure has a VALID prior chosen sublist and a failed
actual policy test. At an owned original87 state, a failure at a rank
strictly after nine exposes the genuine last selected q and rejected p,
with p < q, in the same remaining prime carrier.

This packet proves only finite source algebra, not any external analytic
density or quantitative payment of rank-nine inherited-square failures.
-/

namespace ImbalancedChen.P4AOriginalFull87FailedAttempts

noncomputable section

open scoped Classical
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier frontier_sign_mass states_eq_owner_filter)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction
  (actualFrozenPost8Level)

/-- A physical failed select test, with its exact unprocessed suffix.
All fields are original tree data, not assumptions or result certificates. -/
structure FirstExitRejectedAttempt (α : Type*) where
  older : List α
  rejected : α
  smaller : List α
  positive : Bool
  mass : ℝ

/-- Contribution of this failed select branch to the existing signed
first-exit correction. The residual Euler product is paid exactly once. -/
def FirstExitRejectedAttempt.value {α : Type*}
    (h : α → ℝ) (a : FirstExitRejectedAttempt α) : ℝ :=
  -signedTreeCoefficient (!a.positive) (a.mass * h a.rejected) *
    (a.smaller.map (fun x => 1 - h x)).prod

/-- The literal recursion records failures only on reachable paths.
Skip remains available even when select fails. This is an occurrence list,
not a Finset, so equal-looking descendants are not deduplicated. -/
def firstExitRejectedAttempts {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FirstExitRejectedAttempt α)
  | [] => []
  | p :: ps =>
      firstExitRejectedAttempts policy h pre positive mass ps ++
        if policy (!positive) (p :: pre) = true then
          firstExitRejectedAttempts policy h (p :: pre) (!positive)
            (mass * h p) ps
        else
          [{ older := pre, rejected := p, smaller := ps,
             positive := positive, mass := mass }]

/-- The event enumeration is EXACTLY the already-proved physical correction,
not a second coefficient mean or a reweighted surrogate. -/
theorem correction_eq_failed_attempt_sum {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitCorrection policy h pre positive mass remaining =
      ((firstExitRejectedAttempts policy h pre positive mass remaining).map
        (FirstExitRejectedAttempt.value h)).sum := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [firstExitCorrection, firstExitRejectedAttempts]
  | cons p ps ih =>
      by_cases ht : policy (!positive) (p :: pre) = true
      · simp [firstExitCorrection, firstExitRejectedAttempts, ht, ih]
      · simp [firstExitCorrection, firstExitRejectedAttempts, ht, ih,
          FirstExitRejectedAttempt.value]

/-- An enumerated attempt REALLY failed its select test. Its negative
branch is not inferred from membership in the retained-leaf list. -/
theorem failed_attempt_mem_has_failed_policy {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (a : FirstExitRejectedAttempt α)
    (ha : a ∈ firstExitRejectedAttempts policy h pre positive mass remaining) :
    policy (!a.positive) (a.rejected :: a.older) = false := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [firstExitRejectedAttempts] at ha
  | cons p ps ih =>
      by_cases ht : policy (!positive) (p :: pre) = true
      · rw [firstExitRejectedAttempts, if_pos ht, List.mem_append] at ha
        rcases ha with hskip | hselect
        · exact ih pre positive mass a hskip
        · exact ih (p :: pre) (!positive) (mass * h p) a hselect
      · rw [firstExitRejectedAttempts, if_neg ht,
          List.mem_append, List.mem_singleton] at ha
        rcases ha with hskip | hnow
        · exact ih pre positive mass a hskip
        · subst a
          have hf : policy (!positive) (p :: pre) = false := by
            cases hv : policy (!positive) (p :: pre) with
            | false => rfl
            | true => exact False.elim (ht hv)
          simpa using hf

/-- Recover the actual earlier accepted choices, failed prime, and exact
post-failure suffix from the same traversal. The prefix tests are the
genuine FirstExitValidSelection predicate, not a fabricated premise. -/
theorem failed_attempt_mem_valid_prefix_and_suffix {α : Type*}
    (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (a : FirstExitRejectedAttempt α)
    (ha : a ∈ firstExitRejectedAttempts policy h pre positive mass remaining) :
    ∃ (before chosen : List α),
      remaining = before ++ a.rejected :: a.smaller ∧
      chosen <+ before ∧
      FirstExitValidSelection policy pre positive chosen ∧
      a.older = chosen.reverse ++ pre := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [firstExitRejectedAttempts] at ha
  | cons p ps ih =>
      by_cases ht : policy (!positive) (p :: pre) = true
      · rw [firstExitRejectedAttempts, if_pos ht, List.mem_append] at ha
        rcases ha with hskip | hselect
        · obtain ⟨before, chosen, hrem, hsub, hvalid, holder⟩ :=
            ih pre positive mass a hskip
          refine ⟨p :: before, chosen, ?_, hsub.cons p, hvalid, holder⟩
          simp [hrem]
        · obtain ⟨before, chosen, hrem, hsub, hvalid, holder⟩ :=
            ih (p :: pre) (!positive) (mass * h p) a hselect
          refine ⟨p :: before, p :: chosen, ?_, hsub.cons_cons p, ?_, ?_⟩
          · simp [hrem]
          · exact ⟨ht, hvalid⟩
          · simpa only [List.reverse_cons, List.append_assoc,
              List.singleton_append] using holder
      · rw [firstExitRejectedAttempts, if_neg ht,
          List.mem_append, List.mem_singleton] at ha
        rcases ha with hskip | hnow
        · obtain ⟨before, chosen, hrem, hsub, hvalid, holder⟩ :=
            ih pre positive mass a hskip
          refine ⟨p :: before, chosen, ?_, hsub.cons p, hvalid, holder⟩
          simp [hrem]
        · subst a
          exact ⟨[], [], rfl, List.Sublist.refl [], trivial, by simp⟩

/-- Instantiate the failed-attempt event source on a REAL owned original87
rank-eight state and either existing frozen level. The rejected p is
literally in the same capped, target-deleted remaining carrier. All
preceding selected q are greater than p, in the original scan order. -/
theorem owned87_failed_attempt_actual_source
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ firstExitRejectedAttempts
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining) :
    ∃ (before chosen : List ℕ),
      s.remaining = before ++ a.rejected :: a.smaller ∧
      chosen <+ before ∧
      FirstExitValidSelection
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        s.selectedPrefix s.positive chosen ∧
      a.older = chosen.reverse ++ s.selectedPrefix ∧
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent)
        (!a.positive) (a.rejected :: a.older) = false ∧
      a.positive = true ∧
      a.older.length = 8 + chosen.length ∧
      a.rejected ∈ s.remaining ∧
      (∀ x ∈ chosen, a.rejected < x) := by
  obtain ⟨hlen, _, hremaining, _, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  obtain ⟨before, chosen, hrem, hsub, hvalid, holder⟩ :=
    failed_attempt_mem_valid_prefix_and_suffix
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.remaining s.positive s.mass a ha
  have hfailed :=
    failed_attempt_mem_has_failed_policy
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.remaining s.positive s.mass a ha
  have hpositive : a.positive = true := by
    cases hp : a.positive with
    | true => rfl
    | false =>
        have hfalse : ordinaryParityRosserPolicy false
            (actualFrozenPost8Level n e q om N c s useParent)
            true (a.rejected :: a.older) = false := by
          simpa [hp] using hfailed
        simp at hfalse
  have hrank : a.older.length = 8 + chosen.length := by
    rw [holder, List.length_append, List.length_reverse, hlen]
    omega
  have hpMem : a.rejected ∈ s.remaining := by
    rw [hrem]
    simp
  have horder : (before ++ a.rejected :: a.smaller).Pairwise (· > ·) := by
    simpa only [hrem] using hremaining
  have hcross := (List.pairwise_append.mp horder).2.2
  have hselectedAbove : ∀ x ∈ chosen, a.rejected < x := by
    intro x hx
    exact hcross x (hsub.subset hx) a.rejected (by simp)
  exact ⟨before, chosen, hrem, hsub, hvalid, holder,
    hfailed, hpositive, hrank, hpMem, hselectedAbove⟩

/-- At a physically occurring later odd rejection, the two actual primes
are p = rejected and q = the last SUCCESSFULLY selected prime. Unlike
the special first rank-nine attempt, this q came from the post-eight
remaining carrier; no retained terminal leaf is used to manufacture it. -/
theorem owned87_later_failure_extract_actual_pq
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
    ∃ (p q' : ℕ) (tail chosen before : List ℕ),
      p = a.rejected ∧
      a.older = q' :: tail ∧
      q' ∈ chosen ∧
      p < q' ∧
      chosen <+ before ∧
      s.remaining = before ++ p :: a.smaller ∧
      FirstExitValidSelection
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        s.selectedPrefix s.positive chosen ∧
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent)
        false (p :: q' :: tail) = false := by
  obtain ⟨before, chosen, hrem, hsub, hvalid, holder, hfailed,
      hpos, hrank, _, habove⟩ :=
    owned87_failed_attempt_actual_source
      delta n e q om N cap w z c s hs useParent a ha
  cases hrev : chosen.reverse with
  | nil =>
      have hz : chosen.length = 0 := by
        have := congrArg List.length hrev
        simpa using this
      omega
  | cons q' rest =>
      have hqrev : q' ∈ chosen.reverse := by rw [hrev]; simp
      have hq : q' ∈ chosen := by simpa using hqrev
      have hqorder : a.rejected < q' := habove q' hq
      have htail : a.older = q' :: (rest ++ s.selectedPrefix) := by
        rw [holder, hrev]
        rfl
      have hfailedOdd : ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent)
          false (a.rejected :: a.older) = false := by
        simpa [hpos] using hfailed
      refine ⟨a.rejected, q', rest ++ s.selectedPrefix,
        chosen, before, rfl, htail, hq, hqorder, hsub, hrem, hvalid, ?_⟩
      simpa only [htail] using hfailedOdd

end
end ImbalancedChen.P4AOriginalFull87FailedAttempts
