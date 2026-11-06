import ImbalancedChen.P4AOriginalFull87FailedPriorSquares
import ImbalancedChen.P4AOriginalFull87FailedLogExit
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT.

P1.4: eliminate the unproved index transport between an actual
post-eight chosen OCCURRENCE list and the finite odd-exit potential.
Induction is on pairs of actual selected entries; no artificial t
family, no new policy, and no retesting the eight historic decisions.

IMPORTANT RANK CONVENTION: if the earlier source writes
chosen.length = 2*(m+1), the rejected odd test has rank 11+2*m,
and the potential exponent is m+2 (not m+1). Every selected pair
is counted once; the rejected p is NOT an additional chosen member.
-/ 

namespace ImbalancedChen.P4AOriginalFull87FailedListPotential
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction
  (actualFrozenPost8Level)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts)
open P4AOriginalFull87FailedPriorSquares
  (owned87_failed_all_prior_log_guards_and_pairs)
open P4AOriginalFull87FailedLogExit
  (owned87_later_failure_exact_rank_log_exit)

/-- The finite two-at-a-time potential, using the ORIGINAL list
order and occurrence multiplicities. Every hypothesis applies to an
actual even-length cut of this list. This is a direct list-index bridge:
there is no premise asking for a separately indexed hprior/hpair. -/
theorem paired_list_odd_exit_potential {α : Type*}
    (f : α → ℝ) :
    ∀ (chosen : List α) (s8 beta last : ℝ),
      Even chosen.length →
      (∀ (past : List α) (r q : α) (rest : List α),
        chosen = past ++ r :: q :: rest →
        Even past.length →
        s8 + (past.map f).sum + 3 * f r < beta) →
      (∀ (past : List α) (r q : α) (rest : List α),
        chosen = past ++ r :: q :: rest → f q ≤ f r) →
      beta ≤ s8 + (chosen.map f).sum + 3 * last →
      beta - s8 ≤
        (3 : ℝ) ^ (chosen.length / 2 + 1) * last := by
  intro chosen
  induction chosen with
  | nil =>
      intro s8 beta last _ _ _ hexit
      simp only [List.length_nil, Nat.zero_div, zero_add,
        pow_one, List.map_nil, List.sum_nil, add_zero] at *
      linarith
  | cons x tail ih =>
      intro s8 beta last heven hprior hpair hexit
      cases tail with
      | nil =>
          rcases heven with ⟨k, hk⟩
          simp only [List.length_cons, List.length_nil] at hk
          omega
      | cons y rest =>
          have hevenRest : Even rest.length := by
            rcases heven with ⟨k, hk⟩
            refine ⟨k - 1, ?_⟩
            simp only [List.length_cons] at hk
            omega
          have hx : s8 + 3 * f x < beta := by
            have hh := hprior [] x y rest rfl (by simp)
            simpa using hh
          have hy : f y ≤ f x := hpair [] x y rest rfl
          let nextS8 : ℝ := s8 + f x + f y
          have hnextPrior :
              ∀ (past : List α) (r q : α) (suffix : List α),
                rest = past ++ r :: q :: suffix →
                Even past.length →
                nextS8 + (past.map f).sum + 3 * f r < beta := by
            intro past r q suffix hsplit hpast
            have hwhole :
                x :: y :: rest =
                  (x :: y :: past) ++ r :: q :: suffix := by
              simp [hsplit]
            have hwholeEven : Even (x :: y :: past).length := by
              rcases hpast with ⟨k, hk⟩
              refine ⟨k + 1, ?_⟩
              simp only [List.length_cons]
              omega
            have hh := hprior (x :: y :: past) r q suffix
              hwhole hwholeEven
            dsimp [nextS8]
            simp only [List.map_cons, List.sum_cons] at hh
            linarith
          have hnextPair :
              ∀ (past : List α) (r q : α) (suffix : List α),
                rest = past ++ r :: q :: suffix → f q ≤ f r := by
            intro past r q suffix hsplit
            apply hpair (x :: y :: past) r q suffix
            simp [hsplit]
          have hnextExit :
              beta ≤ nextS8 + (rest.map f).sum + 3 * last := by
            dsimp [nextS8]
            simp only [List.map_cons, List.sum_cons] at hexit
            linarith
          have htail := ih nextS8 beta last hevenRest
            hnextPrior hnextPair hnextExit
          have hstep : beta - s8 ≤ 3 * (beta - nextS8) := by
            dsimp [nextS8]
            linarith
          have hlen :
              (x :: y :: rest).length / 2 + 1 =
                (rest.length / 2 + 1) + 1 := by
            simp only [List.length_cons]
            omega
          calc
            beta - s8 ≤ 3 * (beta - nextS8) := hstep
            _ ≤ 3 * ((3 : ℝ) ^ (rest.length / 2 + 1) * last) :=
                mul_le_mul_of_nonneg_left htail (by norm_num)
            _ = (3 : ℝ) ^
                  ((x :: y :: rest).length / 2 + 1) * last := by
              rw [hlen, pow_succ]
              ring

/-- Exact source-occurrence log-product identity. The input is a
literal list with positive elements; neither its order nor duplicates
are modified. This is the only log-to-list-sum transport needed. -/
theorem log_prod_div_eq_map_sum (N : ℕ) :
    ∀ (xs : List ℕ),
      (∀ p ∈ xs, 0 < p) →
      Real.log (xs.prod : ℝ) / Real.log (N : ℝ) =
        (xs.map (fun p => Real.log (p : ℝ) /
          Real.log (N : ℝ))).sum := by
  intro xs
  induction xs with
  | nil =>
      intro _
      simp
  | cons p ps ih =>
      intro hpos
      have hp : 0 < p := hpos p (by simp)
      have ht : ∀ z ∈ ps, 0 < z := by
        intro z hz
        exact hpos z (by simp [hz])
      have hne : ps.prod ≠ 0 := by
        apply List.prod_ne_zero
        intro hz
        have hf := ht 0 hz
        omega
      have hps : 0 < ps.prod := Nat.pos_of_ne_zero hne
      have hpr : (0 : ℝ) < p := by exact_mod_cast hp
      have hpsr : (0 : ℝ) < ps.prod := by exact_mod_cast hps
      simp only [List.prod_cons, List.map_cons, List.sum_cons]
      rw [Nat.cast_mul, Real.log_mul hpr.ne' hpsr.ne',
        add_div, ih ht]

/-- A REAL original87 rejected occurrence of odd rank at least eleven
obeys the post-eight list potential with its ACTUAL frozen exponent.
No separate t, rank, hprior, hpair, or hEXIT is supplied by the caller.
The two earlier source witnesses of chosen are identified from the SAME
physical older list by right cancellation of the original eighth
history. The true rank convention is 11+2*m and exponent m+2. -/
theorem owned87_failed_actual_pair_list_gap
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ))
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ => 1) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ firstExitRejectedAttempts
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (hlater : 8 < a.older.length) :
    ∃ (before chosen : List ℕ) (m : ℕ),
      s.remaining = before ++ a.rejected :: a.smaller ∧
      chosen <+ before ∧
      a.older = chosen.reverse ++ s.selectedPrefix ∧
      chosen.length = 2 * (m + 1) ∧
      (if useParent then
          P4AOriginalFull87EighthKernelIntegration.actualParent
            n e q om (N : ℝ) s.selectedPrefix
       else
          (P4AOriginalFull87FiniteEighthCap.finiteCap n c
            (P4AOriginalFull87SourceDispatch.point8
              (N : ℝ) s.selectedPrefix) : ℝ)) -
        (∑ i : Fin 8,
          primeHistoryLogCoordinates
            (N : ℝ) 8 s.selectedPrefix i) ≤
        (3 : ℝ) ^ (m + 2) *
          (Real.log (a.rejected : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨before, chosen, hrem, hsub, holder, hall, hpairs⟩ :=
    owned87_failed_all_prior_log_guards_and_pairs
      delta n e q om N cap hN w z c s hs useParent a ha
  obtain ⟨_before2, chosen2, m, _hrem2, _hsub2, holder2,
      hlen2, hexit2⟩ :=
    owned87_later_failure_exact_rank_log_exit
      delta n e q om N cap hN w z c s hs useParent a ha hlater
  have hrev : chosen.reverse = chosen2.reverse :=
    List.append_right_cancel (holder.symm.trans holder2)
  have hsame : chosen = chosen2 := by
    have hh := congrArg List.reverse hrev
    simpa using hh
  have hlen : chosen.length = 2 * (m + 1) := by
    rw [hsame]
    exact hlen2
  have hEven : Even chosen.length := by
    rw [hlen]
    exact ⟨m + 1, by omega⟩
  obtain ⟨_, _, _, _, hlast⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  have hremPrime : ∀ x ∈ s.remaining, Nat.Prime x := by
    intro x hx
    obtain ⟨last, tail, _, _, hremain⟩ := hlast
    rw [hremain] at hx
    exact mem_roughPrimeUniverse_prime hx
  have hchosenPos : ∀ x ∈ chosen, 0 < x := by
    intro x hx
    have hmem : x ∈ s.remaining := by
      rw [hrem]
      exact List.mem_append.mpr (Or.inl (hsub.subset hx))
    exact (hremPrime x hmem).pos
  let f : ℕ → ℝ := fun x =>
    Real.log (x : ℝ) / Real.log (N : ℝ)
  let s8 : ℝ := ∑ i : Fin 8,
    primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix i
  let beta : ℝ :=
    if useParent then
      P4AOriginalFull87EighthKernelIntegration.actualParent
        n e q om (N : ℝ) s.selectedPrefix
    else
      (P4AOriginalFull87FiniteEighthCap.finiteCap n c
        (P4AOriginalFull87SourceDispatch.point8
          (N : ℝ) s.selectedPrefix) : ℝ)
  have hpriorList :
      ∀ (past : List ℕ) (r q' : ℕ) (rest : List ℕ),
        chosen = past ++ r :: q' :: rest →
        Even past.length →
        s8 + (past.map f).sum + 3 * f r < beta := by
    intro past r q' rest hsplit heven
    have hpastPos : ∀ x ∈ past, 0 < x := by
      intro x hx
      apply hchosenPos x
      rw [hsplit]
      exact List.mem_append.mpr (Or.inl hx)
    have hlogs := log_prod_div_eq_map_sum N past hpastPos
    have hh := hall past (q' :: rest) r (by simpa using hsplit) heven
    change s8 + (past.map f).sum + 3 * f r < beta
    rw [← hlogs]
    exact hh
  have hpairList :
      ∀ (past : List ℕ) (r q' : ℕ) (rest : List ℕ),
        chosen = past ++ r :: q' :: rest → f q' ≤ f r := by
    intro past r q' rest hsplit
    exact (hpairs past rest r q' hsplit).le
  have hsumChosen := log_prod_div_eq_map_sum N chosen hchosenPos
  have hExit : beta ≤ s8 + (chosen.map f).sum +
      3 * f a.rejected := by
    change beta ≤ s8 + (chosen.map f).sum + 3 * f a.rejected
    rw [← hsumChosen]
    change beta ≤ s8 +
      Real.log (chosen.prod : ℝ) / Real.log (N : ℝ) +
      3 * (Real.log (a.rejected : ℝ) / Real.log (N : ℝ))
    simpa only [hsame] using hexit2
  have hgap := paired_list_odd_exit_potential f chosen
    s8 beta (f a.rejected) hEven hpriorList hpairList hExit
  have hexponent : chosen.length / 2 + 1 = m + 2 := by
    rw [hlen]
    omega
  refine ⟨before, chosen, m, hrem, hsub, holder, hlen, ?_⟩
  simpa only [hexponent] using hgap

end
end ImbalancedChen.P4AOriginalFull87FailedListPotential
