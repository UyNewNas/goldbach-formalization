import ImbalancedChen.P4AOriginalFull87InheritedOddSquares
import ImbalancedChen.P4AOriginalFull87Post8GuardExtraction
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

P1.4: derive odd cardinality and Nodup for the LITERAL post-eight
odd-trace lists, instead of passing these facts independently to the
inherited-square rejection theorem. The initial prefix has length 8.
The selected history is stored in reverse scan order and the remaining
carrier is in descending scan order. Nothing is sorted, deduplicated,
or reindexed by these proofs.

The three monotone-carrier invariants below (sorted history, descending
remaining carrier, and a strict cross-boundary) are STILL explicit at
the original87 state. Discharging them from the actual eighth-state
producer is the next internal obligation. In particular no lemma here
claims that a prospective rejected pair is a genuine first exit.
-/

namespace ImbalancedChen.P4AOriginalFull87Post8TraceOrder

noncomputable section

open scoped Classical
open P4AOriginalFull87Post8GuardExtraction
  (post8OddTrace actualFrozenPost8Level owned87_terminal_post8_success_guards)
open P4AOriginalFull87InheritedOddSquares
  (owned87_post8_later_odd_reject_last_square)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)

/-- Every literal odd trace has odd LIST length when the starting
Boolean is the parity of the original history. No setification occurs. -/
theorem post8OddTrace_odd_length (chosen : List ℕ) :
    ∀ (history : List ℕ) (positive : Bool),
      positive = decide (Even history.length) →
      ∀ older ∈ post8OddTrace history positive chosen,
        Odd older.length := by
  induction chosen with
  | nil =>
      intro history positive _ older hmem
      simp [post8OddTrace] at hmem
  | cons p ps ih =>
      intro history positive hparity older hmem
      change older ∈
        (if positive then [p :: history] else []) ++
          post8OddTrace (p :: history) (!positive) ps at hmem
      rcases List.mem_append.mp hmem with hnow | hlater
      · cases positive with
        | false =>
            simp at hnow
        | true =>
            simp only [ite_true, List.mem_singleton] at hnow
            subst older
            have heven : Even history.length := by
              simpa using hparity.symm
            obtain ⟨k, hk⟩ := heven
            exact ⟨k, by simp only [List.length_cons]; omega⟩
      · have hnext : (!positive) =
            decide (Even (p :: history).length) := by
          simp only [List.length_cons, Nat.even_add_one, decide_not]
          exact congrArg (!) hparity
        exact ih (p :: history) (!positive) hnext older hlater

/-- An actual descending chosen sublist, with a strictly smaller
remaining carrier than the prior history, produces strictly increasing
reverse-stored odd prefixes throughout the genuine trace. -/
theorem post8OddTrace_pairwise (chosen : List ℕ) :
    ∀ (history : List ℕ) (positive : Bool),
      history.Pairwise (· < ·) →
      chosen.Pairwise (· > ·) →
      (∀ p ∈ chosen, ∀ r ∈ history, p < r) →
      ∀ older ∈ post8OddTrace history positive chosen,
        older.Pairwise (· < ·) := by
  induction chosen with
  | nil =>
      intro history positive _ _ _ older hmem
      simp [post8OddTrace] at hmem
  | cons p ps ih =>
      intro history positive hhist hchosen hcross older hmem
      have hpHist : ∀ r ∈ history, p < r :=
        hcross p (by simp)
      have hnew : (p :: history).Pairwise (· < ·) :=
        List.pairwise_cons.mpr ⟨hpHist, hhist⟩
      have htail : ps.Pairwise (· > ·) :=
        (List.pairwise_cons.mp hchosen).2
      have htailCross :
          ∀ x ∈ ps, ∀ r ∈ p :: history, x < r := by
        intro x hx r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (List.pairwise_cons.mp hchosen).1 x hx
        · exact hcross x (List.mem_cons_of_mem p hx) r hr
      change older ∈
        (if positive then [p :: history] else []) ++
          post8OddTrace (p :: history) (!positive) ps at hmem
      rcases List.mem_append.mp hmem with hnow | hlater
      · cases positive with
        | false =>
            simp at hnow
        | true =>
            simp only [ite_true, List.mem_singleton] at hnow
            subst older
            exact hnew
      · exact ih (p :: history) (!positive)
          hnew htail htailCross older hlater

/-- For one ORIGINAL87 owned state and one actual retained ordinary
leaf, all recorded successful post-eight odd lists have Odd finset
cardinality and Nodup. The occurrence list and policy are untouched.
The carrier monotonicity assumptions are stated openly, not encoded
as a result-bearing field or silently asserted for arbitrary states. -/
theorem owned87_post8_trace_odd_nodup
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (hlen : s.selectedPrefix.length = 8)
    (hpre : s.selectedPrefix.Pairwise (· < ·))
    (hremaining : s.remaining.Pairwise (· > ·))
    (hboundary : ∀ p ∈ s.remaining,
      ∀ r ∈ s.selectedPrefix, p < r) :
    ∃ chosen : List ℕ,
      chosen <+ s.remaining ∧
      leaf.selected = chosen.reverse ++ s.selectedPrefix ∧
      ∀ older ∈ post8OddTrace s.selectedPrefix true chosen,
        Odd older.toFinset.card ∧ older.Nodup := by
  obtain ⟨chosen, hsub, hselected, _hguards⟩ :=
    owned87_terminal_post8_success_guards
      delta n e q om N cap w z c s hs useParent leaf hleaf
  have hsorted : chosen.Pairwise (· > ·) :=
    hremaining.sublist hsub
  have hchosenBoundary :
      ∀ p ∈ chosen, ∀ r ∈ s.selectedPrefix, p < r := by
    intro p hp r hr
    exact hboundary p (hsub.subset hp) r hr
  have hparity :
      true = decide (Even s.selectedPrefix.length) := by
    simp [hlen]
  refine ⟨chosen, hsub, hselected, ?_⟩
  intro older htrace
  have horder : older.Pairwise (· < ·) :=
    post8OddTrace_pairwise chosen s.selectedPrefix true
      hpre hsorted hchosenBoundary older htrace
  have hnodup : older.Nodup := horder.nodup
  have hodd : Odd older.length :=
    post8OddTrace_odd_length chosen s.selectedPrefix true
      hparity older htrace
  constructor
  · simpa only [List.toFinset_card_of_nodup hnodup] using hodd
  · exact hnodup

/-- Discharge the TWO previously explicit hypotheses `Odd older.card`
and `older.Nodup` at the real owned87 occurrence, for BOTH frozen
levels. The strict order of a PROSPECTIVE new pair remains explicit:
this theorem does not manufacture a failed branch or a new coefficient. -/
theorem owned87_post8_ordered_reject_last_square
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining)
    (hlen : s.selectedPrefix.length = 8)
    (hpre : s.selectedPrefix.Pairwise (· < ·))
    (hremaining : s.remaining.Pairwise (· > ·))
    (hboundary : ∀ p ∈ s.remaining,
      ∀ r ∈ s.selectedPrefix, p < r) :
    ∃ chosen : List ℕ,
      chosen <+ s.remaining ∧
      leaf.selected = chosen.reverse ++ s.selectedPrefix ∧
      ∀ older ∈ post8OddTrace s.selectedPrefix true chosen,
        ∀ p q : ℕ,
          p < q →
          (∀ r ∈ older.toFinset, q < r) →
          ordinaryParityRosserPolicy false
            (actualFrozenPost8Level n e q om N c s useParent)
            false (p :: q :: older) = false →
          actualFrozenPost8Level n e q om N c s useParent ≤
            (((p :: q :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2 := by
  obtain ⟨chosen, hsub, hselected, htests⟩ :=
    owned87_post8_later_odd_reject_last_square
      delta n e q om N cap w z c s hs useParent leaf hleaf
  -- The trace invariant applies directly to the SAME chosen witness,
  -- without replacing the occurrence list or identifying two witnesses.
  have hchosenSorted : chosen.Pairwise (· > ·) :=
    hremaining.sublist hsub
  have hchosenCross :
      ∀ x ∈ chosen, ∀ r ∈ s.selectedPrefix, x < r := by
    intro x hx r hr
    exact hboundary x (hsub.subset hx) r hr
  have hparity :
      true = decide (Even s.selectedPrefix.length) := by simp [hlen]
  refine ⟨chosen, hsub, hselected, ?_⟩
  intro older htrace p q hpq hqsmall hrejected
  have horder : older.Pairwise (· < ·) :=
    post8OddTrace_pairwise chosen s.selectedPrefix true
      hpre hchosenSorted hchosenCross older htrace
  have hnodup : older.Nodup := horder.nodup
  have hoddList : Odd older.length :=
    post8OddTrace_odd_length chosen s.selectedPrefix true
      hparity older htrace
  have hodd : Odd older.toFinset.card := by
    simpa only [List.toFinset_card_of_nodup hnodup] using hoddList
  exact htests older htrace p q hodd hnodup hpq hqsmall hrejected

end
end ImbalancedChen.P4AOriginalFull87Post8TraceOrder
