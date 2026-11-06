import ImbalancedChen.P4AOriginalFull87Post8TraceOrder
import ImbalancedChen.FirstExitFrontierInvariants
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

P1.4: discharge the four actual eighth-state order/length premises
needed by the literal post-eight ordinary trace, using the original
sixth-parent depth-eight frontier and existing frontier invariants.

No new mask, sorting, deduplication, parameter or policy is introduced.
The final two lemmas still refer to an arbitrary PROSPECTIVE rejected
pair. They do not assert that it occurs at a first rejected branch,
nor that the special rank-nine historical square tests have passed.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualEighthCarrier

noncomputable section

open scoped Classical
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy)
open P4AOriginalFull87OwnedEighthSource
  (frontier frontier_length states_eq_owner_filter)
open P4AOriginalFull87Post8GuardExtraction
  (post8OddTrace actualFrozenPost8Level)
open P4AOriginalFull87Post8TraceOrder
  (owned87_post8_trace_odd_nodup owned87_post8_ordered_reject_last_square)

/-- An actual owned state inherits the precise historical selection
order, descending remaining carrier, and strict cross-boundary from
the original sixth-parent frontier. Its remaining carrier is exactly
the target-deleted, capped rough-prime source cut at the LAST selected
prime; the strict upper endpoint is not rounded or changed. -/
theorem owned87_eighth_state_exact_carrier
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c) :
    s.selectedPrefix.length = 8 ∧
      s.selectedPrefix.Pairwise (· < ·) ∧
      s.remaining.Pairwise (· > ·) ∧
      (∀ p ∈ s.remaining, ∀ r ∈ s.selectedPrefix, p < r) ∧
      ∃ last : ℕ, ∃ tail : List ℕ,
        s.selectedPrefix = last :: tail ∧
        last ∈ roughPrimeUniverse N cap w z ∧
        s.remaining = roughPrimeUniverse N cap w (last : ℝ) := by
  have hfront : s ∈ frontier n e q om N cap w z := by
    have h := hs
    rw [states_eq_owner_filter] at h
    exact (List.mem_filter.mp h).1
  have hlen : s.selectedPrefix.length = 8 :=
    frontier_length n e q om N cap w z s hfront
  have hsub :
      s.selectedPrefix.reverse ++ s.remaining <+
        roughPrimeUniverse N cap w z := by
    exact firstExitDepthFrontier_selected_remaining_sublist
      8 (sixthPolicy n e q om (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
      [] (roughPrimeUniverse N cap w z) true 1 s hfront
  have hall :
      (s.selectedPrefix.reverse ++ s.remaining).Pairwise (· > ·) :=
    (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hpreRev : s.selectedPrefix.reverse.Pairwise (· > ·) :=
    (List.pairwise_append.mp hall).1
  have hpre : s.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using hpreRev
  have hremaining : s.remaining.Pairwise (· > ·) :=
    (List.pairwise_append.mp hall).2.1
  have hboundary : ∀ p ∈ s.remaining,
      ∀ r ∈ s.selectedPrefix, p < r := by
    intro p hp r hr
    exact mem_firstExitDepthFrontier_selected_gt_remaining
      8 (sixthPolicy n e q om (N : ℝ)) (fun _ : ℕ => (1 : ℝ))
      (roughPrimeUniverse N cap w z)
      (roughPrimeUniverse_pairwise_gt N cap w z)
      s hfront r hr p hp
  have hlast :
      ∃ last : ℕ, ∃ tail : List ℕ,
        s.selectedPrefix = last :: tail ∧
        last ∈ roughPrimeUniverse N cap w z ∧
        s.remaining = roughPrimeUniverse N cap w (last : ℝ) :=
    mem_firstExitDepthFrontier_roughPrime_remaining
      8 (by omega) (sixthPolicy n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) N cap w z s hfront
  exact ⟨hlen, hpre, hremaining, hboundary, hlast⟩

/-- The real original87 occurrence now supplies parity and no-repeat
facts for EVERY successful post-eight odd trace without imposing the
four source invariants as separate caller hypotheses. Both actual
ordinary frozen levels are still selected by the original Boolean. -/
theorem owned87_post8_actual_trace_odd_nodup
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining) :
    ∃ chosen : List ℕ,
      chosen <+ s.remaining ∧
      leaf.selected = chosen.reverse ++ s.selectedPrefix ∧
      ∀ older ∈ post8OddTrace s.selectedPrefix true chosen,
        Odd older.toFinset.card ∧ older.Nodup := by
  obtain ⟨hlen, hpre, hremaining, hboundary, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  exact owned87_post8_trace_odd_nodup
    delta n e q om N cap w z c s hs useParent leaf hleaf
    hlen hpre hremaining hboundary

/-- Instantiates the SAME prospective two-prime rejection inequality
on the actual 87-domain carrier, with all four eighth-frontier premises
paid by the original producer. The p,q condition and a genuine
first-rejected traversal are deliberately NOT inferred here. -/
theorem owned87_post8_actual_ordered_reject_last_square
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining) :
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
  obtain ⟨hlen, hpre, hremaining, hboundary, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  exact owned87_post8_ordered_reject_last_square
    delta n e q om N cap w z c s hs useParent leaf hleaf
    hlen hpre hremaining hboundary

end
end ImbalancedChen.P4AOriginalFull87ActualEighthCarrier
