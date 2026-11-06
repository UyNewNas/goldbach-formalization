import ImbalancedChen.P4AOriginalFull87FailedOddGuard
import ImbalancedChen.PrimeHistoryLogCoordinates
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT.

P1.4: exact N-log coordinate of a genuinely FAILED ordinary upper
selection from the original87 physical eighth frontier. The predecessor
is the same history, the rejected prime is the same physical occurrence,
and the exponent is the literal actualParent or rounded finiteCap.

The finite last-square failure is converted into the rank/log EXIT
inequality; no unrelated Rosser bound is subtracted. The selected
post-eight chronology stays an occurrence list, not a Finset.
This neither supplies ALL prior odd log guards nor pays the rank-nine
inherited square, the primitive/centre errors, or a limiting integral.
-/

namespace ImbalancedChen.P4AOriginalFull87FailedLogExit
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy)
open P4AOriginalFull87OwnedEighthSource
  (frontier frontier_sign_mass states_eq_owner_filter)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction
  (actualFrozenPost8Level)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts
   owned87_failed_attempt_actual_source)
open P4AOriginalFull87FailedOddGuard
  (rejected_attempt_sign_parity owned87_later_failure_last_square)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)

/-- The actual rejected minimum-square bound implies its EXACT
base-N logarithmic inequality. Here the entire product is physical,
so the logarithm must be applied to that very same product. -/
theorem failed_square_to_exact_N_log
    (N p : ℕ) (older : List ℕ) (beta : ℝ)
    (hN : 1 < (N : ℝ)) (hp : 0 < p)
    (hfailed : (N : ℝ) ^ beta ≤
      (((p :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2) :
    beta ≤
      Real.log (((p :: older).prod : ℕ) : ℝ) / Real.log (N : ℝ) +
        2 * (Real.log (p : ℝ) / Real.log (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := (by norm_num : (0 : ℝ) < 1).trans hN
  have hRpos : 0 < (N : ℝ) ^ beta :=
    Real.rpow_pos_of_pos hNpos _
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hprodpos : (0 : ℝ) <
      (((p :: older).prod : ℕ) : ℝ) := by
    by_contra hn
    have hz : ((((p :: older).prod : ℕ) : ℝ)) = 0 :=
      le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _)
    have hzero : (N : ℝ) ^ beta ≤ 0 := by
      simpa [hz] using hfailed
    exact (not_le_of_gt hRpos) hzero
  have hlog := Real.log_le_log hRpos hfailed
  rw [Real.log_rpow hNpos] at hlog
  have hlog_product :
      Real.log (((p :: older).prod : ℕ) : ℝ) +
        2 * Real.log (p : ℝ) =
      Real.log ((((p :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2) := by
    rw [Real.log_mul hprodpos.ne' (pow_pos hppos 2).ne',
      Real.log_pow]
  have hscaled : beta * Real.log (N : ℝ) ≤
      Real.log (((p :: older).prod : ℕ) : ℝ) +
        2 * Real.log (p : ℝ) := by
    rw [← hlog_product]
    exact hlog
  have hdiv : beta ≤
      (Real.log (((p :: older).prod : ℕ) : ℝ) +
        2 * Real.log (p : ℝ)) / Real.log (N : ℝ) := by
    exact (le_div_iff₀ (Real.log_pos hN)).mpr
      (by simpa only [mul_comm] using hscaled)
  calc
    beta ≤
      (Real.log (((p :: older).prod : ℕ) : ℝ) +
        2 * Real.log (p : ℝ)) / Real.log (N : ℝ) := hdiv
    _ = Real.log (((p :: older).prod : ℕ) : ℝ) / Real.log (N : ℝ) +
        2 * (Real.log (p : ℝ) / Real.log (N : ℝ)) := by ring

/-- A failed last-square test on the ORIGINAL selected history and
the ORIGINAL successful post-eight occurrences has the exact
S8 + Schosen + 3*t_exit logarithmic form. The three copies of the
last-prime log come from its once-in-the-product and twice-in-the-
square contributions; there is no separately assumed hEXIT. -/
theorem failed_square_to_history_chosen_log
    (N p : ℕ) (chosen history : List ℕ) (beta : ℝ)
    (hN : 1 < (N : ℝ)) (hp : 0 < p)
    (hchosen : 0 < chosen.prod) (hhistory : 0 < history.prod)
    (hfailed : (N : ℝ) ^ beta ≤
      (((p :: (chosen.reverse ++ history)).prod : ℕ) : ℝ) *
        (p : ℝ) ^ 2) :
    beta ≤
      Real.log (history.prod : ℝ) / Real.log (N : ℝ) +
        Real.log (chosen.prod : ℝ) / Real.log (N : ℝ) +
        3 * (Real.log (p : ℝ) / Real.log (N : ℝ)) := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hcpos : (0 : ℝ) < chosen.prod := by exact_mod_cast hchosen
  have hhpos : (0 : ℝ) < history.prod := by exact_mod_cast hhistory
  have hprod :
      (p :: (chosen.reverse ++ history)).prod =
        p * chosen.prod * history.prod := by
    simp only [List.prod_cons, List.prod_append, List.prod_reverse]
    ring
  have hlogprod :
      Real.log (((p :: (chosen.reverse ++ history)).prod : ℕ) : ℝ) =
        Real.log (p : ℝ) + Real.log (chosen.prod : ℝ) +
          Real.log (history.prod : ℝ) := by
    rw [hprod, Nat.cast_mul, Nat.cast_mul,
      Real.log_mul (mul_pos hppos hcpos).ne' hhpos.ne',
      Real.log_mul hppos.ne' hcpos.ne']
  have hlog :=
    failed_square_to_exact_N_log N p
      (chosen.reverse ++ history) beta hN hp hfailed
  calc
    beta ≤
      Real.log (((p :: (chosen.reverse ++ history)).prod : ℕ) : ℝ) /
        Real.log (N : ℝ) +
        2 * (Real.log (p : ℝ) / Real.log (N : ℝ)) := hlog
    _ = Real.log (history.prod : ℝ) / Real.log (N : ℝ) +
        Real.log (chosen.prod : ℝ) / Real.log (N : ℝ) +
        3 * (Real.log (p : ℝ) / Real.log (N : ℝ)) := by
      rw [hlogprod]
      ring

private theorem evenListLength_decide_even {α : Type*} (xs : List α) :
    evenListLength xs = decide (Even xs.length) := by
  induction xs with
  | nil => simp [evenListLength]
  | cons x xs ih =>
      simp only [evenListLength, ih, List.length_cons,
        Nat.even_add_one, decide_not]

/-- The genuine original87 failed event now supplies the exact log
last-square EXIT inequality without a caller-provided prime coordinate,
exit rank, beta, or positivity certificate. The actual eighth source
is the original Fin 8 tuple, and m is the true number of successful
post-eight pairs before the rejection: rank is 11+2*m.

This is NOT the all-rank series result: the ninth-rank failure is
excluded, and the preceding odd log tests still need an indexed bridge. -/
theorem owned87_later_failure_exact_rank_log_exit
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ firstExitRejectedAttempts
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (hlater : 8 < a.older.length) :
    ∃ (chosen : List ℕ) (m : ℕ),
      chosen <+ s.remaining ∧
      a.older = chosen.reverse ++ s.selectedPrefix ∧
      chosen.length = 2 * (m + 1) ∧
      (if useParent then
          actualParent n e q om (N : ℝ) s.selectedPrefix
       else
          (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)) ≤
        (∑ i : Fin 8,
            primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix i) +
        Real.log (chosen.prod : ℝ) / Real.log (N : ℝ) +
        3 * (Real.log (a.rejected : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨hlen, _, _, _, hlast⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  have hfront : s ∈ frontier n e q om N cap w z := by
    have hh := hs
    rw [states_eq_owner_filter] at hh
    exact (List.mem_filter.mp hh).1
  have hspositive : s.positive = true :=
    (frontier_sign_mass n e q om N cap w z s hfront).1
  obtain ⟨before, chosen, hrem, hsub, _hvalid, holder, _hfailed,
      hapos, hrank, hpMem, _⟩ :=
    owned87_failed_attempt_actual_source
      delta n e q om N cap w z c s hs useParent a ha
  have hremPrime : ∀ x ∈ s.remaining, Nat.Prime x := by
    intro x hx
    obtain ⟨last, tail, _, _, hremain⟩ := hlast
    rw [hremain] at hx
    exact mem_roughPrimeUniverse_prime hx
  have hpreSub :
      s.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z :=
    firstExitDepthFrontier_selected_reverse_sublist
      8 (sixthPolicy n e q om (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
      (roughPrimeUniverse N cap w z) s hfront
  have hhistPrime : ∀ x ∈ s.selectedPrefix, Nat.Prime x := by
    intro x hx
    exact mem_roughPrimeUniverse_prime
      (hpreSub.subset (List.mem_reverse.mpr hx))
  have hchosenPrime : ∀ x ∈ chosen, Nat.Prime x := by
    intro x hx
    apply hremPrime x
    rw [hrem]
    exact List.mem_append.mpr (Or.inl (hsub.subset hx))
  have hhistNe : s.selectedPrefix.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    exact (hhistPrime 0 hz).ne_zero rfl
  have hchosenNe : chosen.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    exact (hchosenPrime 0 hz).ne_zero rfl
  have hhistPos : 0 < s.selectedPrefix.prod := Nat.pos_of_ne_zero hhistNe
  have hchosenPos : 0 < chosen.prod := Nat.pos_of_ne_zero hchosenNe
  have hp : 0 < a.rejected := (hremPrime a.rejected hpMem).pos
  let beta : ℝ :=
    if useParent then
      actualParent n e q om (N : ℝ) s.selectedPrefix
    else (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)
  have hlevel :
      actualFrozenPost8Level n e q om N c s useParent =
        (N : ℝ) ^ beta := rfl
  have hbound :=
    owned87_later_failure_last_square
      delta n e q om N cap w z c s hs useParent a ha hlater
  have hfail : (N : ℝ) ^ beta ≤
      (((a.rejected :: (chosen.reverse ++ s.selectedPrefix)).prod : ℕ) : ℝ) *
        (a.rejected : ℝ) ^ 2 := by
    rw [← holder, ← hlevel]
    exact hbound
  have hlog :=
    failed_square_to_history_chosen_log
      N a.rejected chosen s.selectedPrefix beta
      hN hp hchosenPos hhistPos hfail
  have hsum :
      (∑ i : Fin 8,
        primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix i) =
        Real.log (s.selectedPrefix.prod : ℝ) / Real.log (N : ℝ) :=
    sum_primeHistoryLogCoordinates (N : ℝ) hN hlen
      (fun x hx => (hhistPrime x hx).pos)
  have hlogActual : beta ≤
      (∑ i : Fin 8,
        primeHistoryLogCoordinates (N : ℝ) 8 s.selectedPrefix i) +
        Real.log (chosen.prod : ℝ) / Real.log (N : ℝ) +
        3 * (Real.log (a.rejected : ℝ) / Real.log (N : ℝ)) := by
    rw [hsum]
    exact hlog
  have hstart : s.positive = evenListLength s.selectedPrefix := by
    rw [hspositive, evenListLength_decide_even, hlen]
    decide
  have hsign :=
    rejected_attempt_sign_parity
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => (1 : ℝ)) s.selectedPrefix s.remaining
      s.positive s.mass hstart a ha
  have hevenOlder : Even a.older.length := by
    have hh : decide (Even a.older.length) = true := by
      rw [← evenListLength_decide_even, ← hsign, hapos]
    exact of_decide_eq_true hh
  have hevenChosen : Even chosen.length := by
    rw [hrank] at hevenOlder
    omega
  obtain ⟨k, hk⟩ := hevenChosen
  have hkpos : 0 < k := by omega
  refine ⟨chosen, k - 1, ?_, holder, ?_, ?_⟩
  · rw [hrem]
    exact hsub.trans (List.sublist_append_left before (a.rejected :: a.smaller))
  · omega
  · exact hlogActual

end
end ImbalancedChen.P4AOriginalFull87FailedLogExit
