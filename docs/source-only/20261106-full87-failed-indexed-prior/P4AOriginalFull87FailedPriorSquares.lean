import ImbalancedChen.P4AOriginalFull87FailedLogExit
import ImbalancedChen.P4AOriginalFull87Post8GuardExtraction
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT.

P1.4, original87: ALL earlier successful post-eight odd selections
belonging to one genuine failed attempt, at the same frozen level.
This is stronger than extracting only the immediately previous odd
test: each earlier split in the physical chosen occurrence chronology
supplies a strict full-square bound. Adjacent chosen primes also have
the correct strict logarithmic order. Historical ranks 1/3/5/7 are
not retested. No analytic input, alternate mask or coefficient.
-/

namespace ImbalancedChen.P4AOriginalFull87FailedPriorSquares
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier frontier_sign_mass states_eq_owner_filter)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction
  (actualFrozenPost8Level upper_odd_test_iff)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts
   owned87_failed_attempt_actual_source)

/-- A cut anywhere in a REAL valid selection recovers the decision on
the element immediately following that cut. For an even-sized past,
the odd upper decision is at the same incoming frozen policy. The
unselected suffix is not replaced by a new valid-selection witness. -/
theorem validSelection_even_past_odd_guard {α : Type*}
    (policy : Bool → List α → Bool)
    (past : List α) (r : α) (rest pre : List α)
    (positive : Bool)
    (hphase : positive = decide (Even past.length))
    (hvalid : FirstExitValidSelection policy pre positive
      (past ++ r :: rest)) :
    policy false (r :: past.reverse ++ pre) = true := by
  induction past generalizing pre positive with
  | nil =>
      have hp : positive = true := by simpa using hphase
      have hstep : policy (!positive) (r :: pre) = true := hvalid.1
      simpa [hp] using hstep
  | cons x xs ih =>
      have htail : FirstExitValidSelection policy (x :: pre)
          (!positive) (xs ++ r :: rest) := hvalid.2
      have hphase' : (!positive) = decide (Even xs.length) := by
        simpa only [List.length_cons, Nat.even_add_one,
          decide_not, Bool.not_not] using congrArg (!) hphase
      have hstep := ih (x :: pre) (!positive) hphase' htail
      simpa only [List.reverse_cons, List.append_assoc,
        List.singleton_append] using hstep

/-- For a sorted odd upper prefix, the full upper Rosser decision
includes the strict square test at its actual smallest prime.
This is a literal consequence of UpperAdmissibleSet, not of the
total-product inequality alone. -/
theorem passed_odd_smallest_full_square
    (R : ℝ) (r : ℕ) (older : List ℕ)
    (horder : (r :: older).Pairwise (· < ·))
    (hodd : Odd (r :: older).length)
    (hpassed : ordinaryParityRosserPolicy false R false
      (r :: older) = true) :
    ((((r :: older).prod : ℕ) : ℝ) * (r : ℝ) ^ 2 < R := by
  classical
  have hn : (r :: older).Nodup := horder.nodup
  have hmin : ∀ x ∈ (r :: older).toFinset, r ≤ x := by
    intro x hx
    rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with h | h
    · subst x
      exact le_rfl
    · exact ((List.pairwise_cons.mp horder).1 x h).le
  have hfilt :
      (r :: older).toFinset.filter (fun x => r ≤ x) =
        (r :: older).toFinset :=
    Finset.filter_eq_self.mpr hmin
  have hoddset : ¬ Even (r :: older).toFinset.card := by
    rw [List.toFinset_card_of_nodup hn]
    rcases hodd with ⟨k, hk⟩
    rintro ⟨j, hj⟩
    omega
  have hupper :=
    ((upper_odd_test_iff R (r :: older)).mp hpassed).2
  have htest := hupper r (by simp) (by simpa only [hfilt] using hoddset)
  have hprod : (r :: older).toFinset.prod id = (r :: older).prod := by
    simpa using List.prod_toFinset (fun x : ℕ => x) hn
  simpa only [hfilt, id_eq, hprod] using htest

/-- For the genuine failed-attempt occurrence, EVERY earlier
successful odd split (not just the last one) passes the full-square
test at the SAME actualParent/finiteCap frozen level. At the same
time, every successive pair of selected post-eight occurrences has
the strict base-N log order needed for the potential argument.

The quantification is over actual list splits. It neither invents
new selected primes nor collapses equal-looking source occurrences. -/
theorem owned87_failed_all_prior_odd_squares_and_pairs
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell)
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
      a.older = chosen.reverse ++ s.selectedPrefix ∧
      (∀ (past rest : List ℕ) (r : ℕ),
        chosen = past ++ r :: rest →
        Even past.length →
        ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent)
          false (r :: past.reverse ++ s.selectedPrefix) = true ∧
        ((((r :: past.reverse ++ s.selectedPrefix).prod : ℕ) : ℝ) *
          (r : ℝ) ^ 2 <
          actualFrozenPost8Level n e q om N c s useParent) ∧
      (∀ (past rest : List ℕ) (r q' : ℕ),
        chosen = past ++ r :: q' :: rest →
        Real.log (q' : ℝ) / Real.log (N : ℝ) <
          Real.log (r : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨hlen, hhistorySort, hremainingSort, hboundary, hlast⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  have hfront : s ∈ frontier n e q om N cap w z := by
    have hh := hs
    rw [states_eq_owner_filter] at hh
    exact (List.mem_filter.mp hh).1
  have hspos : s.positive = true :=
    (frontier_sign_mass n e q om N cap w z s hfront).1
  obtain ⟨before, chosen, hrem, hsub, hvalid, holder, _,
      _, _, _, _⟩ :=
    owned87_failed_attempt_actual_source
      delta n e q om N cap w z c s hs useParent a ha
  have hchosenSort : chosen.Pairwise (· > ·) :=
    hremainingSort.sublist hsub
  have hchosenCross :
      ∀ x ∈ chosen.reverse, ∀ y ∈ s.selectedPrefix, x < y := by
    intro x hx y hy
    exact hboundary x (hsub.subset (List.mem_reverse.mp hx)) y hy
  have hrevSort : chosen.reverse.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using hchosenSort
  have hfullSort :
      (chosen.reverse ++ s.selectedPrefix).Pairwise (· < ·) :=
    List.pairwise_append.mpr
      ⟨hrevSort, hhistorySort, hchosenCross⟩
  have hremPrime : ∀ x ∈ s.remaining, Nat.Prime x := by
    intro x hx
    obtain ⟨last, tail, _, _, hremain⟩ := hlast
    rw [hremain] at hx
    exact mem_roughPrimeUniverse_prime hx
  refine ⟨before, chosen, hrem, hsub, holder, ?_, ?_⟩
  · intro past rest r hsplit heven
    have hphase : s.positive = decide (Even past.length) := by
      rw [hspos]
      exact (decide_eq_true heven).symm
    have hvalidSplit :
        FirstExitValidSelection
          (ordinaryParityRosserPolicy false
            (actualFrozenPost8Level n e q om N c s useParent))
          s.selectedPrefix s.positive (past ++ r :: rest) := by
      simpa [hsplit] using hvalid
    have hpassed :=
      validSelection_even_past_odd_guard
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        past r rest s.selectedPrefix s.positive hphase hvalidSplit
    have heq :
        chosen.reverse ++ s.selectedPrefix =
          rest.reverse ++ (r :: past.reverse ++ s.selectedPrefix) := by
      rw [hsplit]
      simp [List.reverse_append, List.append_assoc]
    have hsrt := hfullSort
    rw [heq] at hsrt
    have hprefixSort :
        (r :: past.reverse ++ s.selectedPrefix).Pairwise (· < ·) :=
      (List.pairwise_append.mp hsrt).2.1
    have hodd :
        Odd (r :: past.reverse ++ s.selectedPrefix).length := by
      obtain ⟨k, hk⟩ := heven
      refine ⟨k + 4, ?_⟩
      simp only [List.length_cons, List.length_append,
        List.length_reverse, hlen]
      omega
    exact ⟨hpassed, passed_odd_smallest_full_square
      (actualFrozenPost8Level n e q om N c s useParent)
      r (past.reverse ++ s.selectedPrefix)
      hprefixSort hodd hpassed⟩
  · intro past rest r q' hsplit
    have htailSort : (r :: q' :: rest).Pairwise (· > ·) := by
      have hh := hchosenSort
      rw [hsplit] at hh
      exact (List.pairwise_append.mp hh).2.1
    have hq_lt_r : q' < r :=
      (List.pairwise_cons.mp htailSort).1 q' (by simp)
    have hqchosen : q' ∈ chosen := by
      rw [hsplit]
      simp
    have hqremain : q' ∈ s.remaining := by
      rw [hrem]
      exact List.mem_append.mpr
        (Or.inl (hsub.subset hqchosen))
    have hqpos : (0 : ℝ) < q' := by
      exact_mod_cast (hremPrime q' hqremain).pos
    apply (div_lt_div_iff_of_pos_right (Real.log_pos hN)).mpr
    exact Real.log_lt_log hqpos (by exact_mod_cast hq_lt_r)

end
end ImbalancedChen.P4AOriginalFull87FailedPriorSquares
