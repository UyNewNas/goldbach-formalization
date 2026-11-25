import ImbalancedChen.Part5OriginalH430ReceiverEventFibreWeights

/-!
P5.6 / h34 — actual rank-two first-excluded EVENT OCCURRENCE CAPACITY.

The prior packet grouped genuine (U3/U4,p,q) receipts by (p,ell), but
one event witness was not a multiplicity payment. Here we inspect the
actual *recursive list* historicalRejectedEvents, not an abstract set
of invented owners. On any parent prefix, the number of rejected
events with precisely one new selected letter r equals the number of
occurrences of r in the remaining carrier that fail the immediate
retention test. Accepted branches cannot contribute such a short
prefix. For the actual roughPrimeUniverse, which is Nodup, this count
is at most one. For a genuinely own-root rejected original event key,
the previous witness upgrades it to exactly ONE real rank-two event.

The original tagged receipt fibre may contain many q and overlapping
U3/U4 tags. Therefore one rank-two historical occurrence alone cannot
be charged once per receipt. The exact excess (card fibre - 1) remains
an explicit manuscript-internal obligation, not an external assumption,
and not a proved positive or negative signed-payment amount.

SOURCE ONLY. These are Lean candidate proofs, UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430EventOccurrenceCapacity

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections

private theorem filter_none_of_forall {α : Type*}
    (f : α → Bool) (xs : List α) :
    (∀ x ∈ xs, f x = false) → xs.filter f = [] := by
  induction xs with
  | nil =>
      intro _
      rfl
  | cons x xs ih =>
      intro h
      have hx : f x = false := h x (by simp)
      have htail : ∀ y ∈ xs, f y = false := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih htail]

/-- No historical first-excluded child has a selected prefix shorter
than one additional letter beyond its actual parent. This also holds
in the recursively admitted subtree, with its LONGER parent prefix. -/
private theorem rejected_prefix_strict_growth {α : Type*}
    (retained : Bool → List α → Bool) (weight : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    ∀ e ∈ historicalRejectedEvents retained weight pre positive mass remaining,
      pre.length < e.selectedPrefix.length := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [historicalRejectedEvents]
  | cons q qs ih =>
      intro e he
      by_cases hpass : retained (!positive) (q :: pre) = true
      · simp [historicalRejectedEvents, hpass] at he
        rcases he with hskip | hbranch
        · exact ih pre positive mass e hskip
        · have hlong :=
            ih (q :: pre) (!positive) (mass * weight q) e hbranch
          simp only [List.length_cons] at hlong
          omega
      · have hfail : retained (!positive) (q :: pre) = false := by
          cases h : retained (!positive) (q :: pre) <;> simp_all
        simp [historicalRejectedEvents, hfail] at he
        rcases he with hskip | hsingleton
        · exact ih pre positive mass e hskip
        · subst e
          simp

/-- Exact actual-list count, not just existence of an event. The
immediate rejected r-children at a fixed parent are in bijection
with literal occurrences of r failing the next policy test in the
remaining list. Accepted continuations are at depth >= parent+2. -/
theorem immediate_rejected_event_occurrence_count {α : Type*}
    (retained : Bool → List α → Bool) (weight : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (r : α) :
    ((historicalRejectedEvents retained weight pre positive mass remaining).filter
       (fun e => decide (e.selectedPrefix = r :: pre))).length =
    (remaining.filter (fun q =>
       decide (q = r ∧ retained (!positive) (q :: pre) = false))).length := by
  classical
  induction remaining generalizing pre positive mass with
  | nil =>
      simp [historicalRejectedEvents]
  | cons q qs ih =>
      by_cases hpass : retained (!positive) (q :: pre) = true
      · have hlongnone :
          (historicalRejectedEvents retained weight (q :: pre)
            (!positive) (mass * weight q) qs).filter
            (fun e => decide (e.selectedPrefix = r :: pre)) = [] := by
          apply filter_none_of_forall
          intro e he
          have hg := rejected_prefix_strict_growth retained weight
            (q :: pre) (!positive) (mass * weight q) qs e he
          have hneq : e.selectedPrefix ≠ r :: pre := by
            intro heq
            rw [heq] at hg
            simp at hg
          simp [hneq]
        have hnot : ¬(q = r ∧
            retained (!positive) (q :: pre) = false) := by
          intro hh
          simp [hpass] at hh
        simpa [historicalRejectedEvents, hpass,
          List.filter_append, hlongnone, hnot]
          using ih pre positive mass
      · have hfail : retained (!positive) (q :: pre) = false := by
          cases h : retained (!positive) (q :: pre) <;> simp_all
        by_cases hqr : q = r
        · subst q
          simpa [historicalRejectedEvents, hfail,
            List.filter_append] using ih pre positive mass
        · simpa [historicalRejectedEvents, hfail, hqr,
            List.filter_append] using ih pre positive mass

/-- A Nodup carrier cannot offer the SAME immediate prime twice,
regardless of policy. The proof does not quotient arithmetic q's. -/
private theorem filtered_single_label_le_one {α : Type*}
    (remaining : List α) (r : α) (policyStep : α → Bool) :
    remaining.Nodup →
      (remaining.filter
        (fun q => decide (q = r ∧ policyStep q = false))).length ≤ 1 := by
  classical
  induction remaining with
  | nil =>
      intro _
      simp
  | cons q qs ih =>
      intro hn
      have hqnot : q ∉ qs := (List.nodup_cons.mp hn).1
      have htail : qs.Nodup := (List.nodup_cons.mp hn).2
      by_cases hqr : q = r
      · subst q
        have hnone : (qs.filter
            (fun x => decide (x = r ∧ policyStep x = false))) = [] := by
          apply filter_none_of_forall
          intro x hx
          have hneq : x ≠ r := by
            intro heq
            subst x
            exact hqnot hx
          simp [hneq]
        simp [hnone]
      · have hle := ih htail
        simpa [hqr] using hle

/-- The true first-exit list over the original distinct-prime carrier
contains at most one event with selectedPrefix=[ell,p] following the
fixed historical root [p]. There is NO per-q event replication. -/
theorem actual_rank_two_event_capacity_le_one
    (N cap p ell : ℕ) (lower : Bool) (Q : ℝ) :
    ((historicalRejectedEvents
      (ordinaryRosserRetainedPolicy lower Q)
      (fun x : ℕ => 1 / ((x : ℝ) - 1))
      [p] false (1 / ((p : ℝ) - 1))
      (roughPrimeUniverse N cap 0 (p : ℝ))).filter
      (fun e => decide (e.selectedPrefix = [ell, p]))).length ≤ 1 := by
  have hcount := immediate_rejected_event_occurrence_count
    (ordinaryRosserRetainedPolicy lower Q)
    (fun x : ℕ => 1 / ((x : ℝ) - 1))
    [p] false (1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap 0 (p : ℝ)) ell
  rw [hcount]
  exact filtered_single_label_le_one
    (roughPrimeUniverse N cap 0 (p : ℝ)) ell
    (fun x => ordinaryRosserRetainedPolicy lower Q true [x, p])
    (roughPrimeUniverse_nodup N cap 0 (p : ℝ))

/-- Each original frozenOnly fourth-lane key has EXACTLY ONE literal
rank-two rejected occurrence, conditional only on its prior physical
root/cap gates; it is not one occurrence for each q in the fibre. -/
theorem frozen_fail_key_exactly_one_rank_two_event
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (key : EventKey)
    (hk : key ∈ eventKeys
      (ownPolicyFail (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 Q lower) (frozenOnlyBad N)) :
    ((historicalRejectedEvents
      (ordinaryRosserRetainedPolicy lower Q)
      (fun x : ℕ => 1 / ((x : ℝ) - 1))
      [key.1] false (1 / ((key.1 : ℝ) - 1))
      (roughPrimeUniverse N cap 0 (key.1 : ℝ))).filter
      (fun e => decide (e.selectedPrefix = [key.2, key.1]))).length = 1 := by
  obtain ⟨event, hmem, hprefix, _, _⟩ :=
    frozen_fail_key_has_historical_event
      N n cap tau z0 Q lower hzcap key hk
  have hevent : event ∈
      (historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun x : ℕ => 1 / ((x : ℝ) - 1))
        [key.1] false (1 / ((key.1 : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (key.1 : ℝ))).filter
        (fun e => decide (e.selectedPrefix = [key.2, key.1])) := by
    simp [hmem, hprefix]
  have hle := actual_rank_two_event_capacity_le_one
    N cap key.1 key.2 lower Q
  cases hf : (historicalRejectedEvents
      (ordinaryRosserRetainedPolicy lower Q)
      (fun x : ℕ => 1 / ((x : ℝ) - 1))
      [key.1] false (1 / ((key.1 : ℝ) - 1))
      (roughPrimeUniverse N cap 0 (key.1 : ℝ))).filter
      (fun e => decide (e.selectedPrefix = [key.2, key.1])) with
  | nil => simp [hf] at hevent
  | cons e es =>
      simp [hf] at hle ⊢
      omega

/-- The OTHER actual frozen-cutoff rejection lane has the same exact
one-occurrence restriction, but its own different bad-prime map. -/
theorem rejected_frozen_fail_key_exactly_one_rank_two_event
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (key : EventKey)
    (hk : key ∈ eventKeys
      (ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower)
      (rejectedFrozenBad N n tau)) :
    ((historicalRejectedEvents
      (ordinaryRosserRetainedPolicy lower Q)
      (fun x : ℕ => 1 / ((x : ℝ) - 1))
      [key.1] false (1 / ((key.1 : ℝ) - 1))
      (roughPrimeUniverse N cap 0 (key.1 : ℝ))).filter
      (fun e => decide (e.selectedPrefix = [key.2, key.1]))).length = 1 := by
  obtain ⟨event, hmem, hprefix, _, _⟩ :=
    rejected_frozen_fail_key_has_historical_event
      N n cap tau z0 Q lower hzcap key hk
  have hevent : event ∈
      (historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun x : ℕ => 1 / ((x : ℝ) - 1))
        [key.1] false (1 / ((key.1 : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (key.1 : ℝ))).filter
        (fun e => decide (e.selectedPrefix = [key.2, key.1])) := by
    simp [hmem, hprefix]
  have hle := actual_rank_two_event_capacity_le_one
    N cap key.1 key.2 lower Q
  cases hf : (historicalRejectedEvents
      (ordinaryRosserRetainedPolicy lower Q)
      (fun x : ℕ => 1 / ((x : ℝ) - 1))
      [key.1] false (1 / ((key.1 : ℝ) - 1))
      (roughPrimeUniverse N cap 0 (key.1 : ℝ))).filter
      (fun e => decide (e.selectedPrefix = [key.2, key.1])) with
  | nil => simp [hf] at hevent
  | cons e es =>
      simp [hf] at hle ⊢
      omega

/-- The exact source-fibre surplus AFTER allocating only one rank-two
event per genuinely occurring key. This is a count identity, not a
permission to charge the same historical mass m times. -/
def excessReceipts (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (key : EventKey) : ℕ :=
  (eventFibre S bad key).card - 1

theorem fibre_card_one_plus_excess
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (key : EventKey) (hk : key ∈ eventKeys S bad) :
    (eventFibre S bad key).card = 1 + excessReceipts S bad key := by
  have hpositive : 0 < (eventFibre S bad key).card := by
    rcases Finset.mem_image.mp hk with ⟨z, hz, hkey⟩
    exact Finset.card_pos.mpr
      ⟨z, Finset.mem_filter.mpr ⟨hz, hkey⟩⟩
  unfold excessReceipts
  omega

/-- Exact signed budget: real original receipt mass equals one
event-key kernel PLUS every still-unpaid surplus q/tag occurrence.
Even if the kernel has a sign, nothing is dropped. -/
theorem signed_source_one_event_plus_excess
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (w : EventKey → ℝ) :
    (∑ z ∈ S, w (receiverEventKey bad z)) =
      (∑ key ∈ eventKeys S bad, w key) +
      ∑ key ∈ eventKeys S bad,
        ((excessReceipts S bad key : ℕ) : ℝ) * w key := by
  classical
  rw [key_weighted_fibre_sum S bad w]
  calc
    (∑ key ∈ eventKeys S bad,
      ((eventFibre S bad key).card : ℝ) * w key) =
      ∑ key ∈ eventKeys S bad,
        (w key + ((excessReceipts S bad key : ℕ) : ℝ) * w key) := by
          apply Finset.sum_congr rfl
          intro key hk
          have h := fibre_card_one_plus_excess S bad key hk
          rw [h]
          push_cast
          ring
    _ = _ := by rw [Finset.sum_add_distrib]

/-- The actual root-history event is keyed only by (p,ell), not by
the original rejection lane. For TWO sources, the first per-lane keys
must be merged BEFORE any event can be charged. Each key appearing in
BOTH lanes supplies a separate unpaid overlap charge, in addition to
the within-lane q/tag surplus. All signs are retained exactly.

The RHS first term is the one-per-DISTINCT-key historical event
candidate; the remaining three terms are explicitly NOT PAID. -/
theorem two_original_fail_lanes_unique_event_key_budget
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    let F := ownPolicyFail (frozenOnly N n tau)
      (frozenOnlyBad N) N z0 Q lower
    let R := ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower
    let KF := eventKeys F (frozenOnlyBad N)
    let KR := eventKeys R (rejectedFrozenBad N n tau)
    (∑ z ∈ F, originalEventMass
      (receiverEventKey (frozenOnlyBad N) z)) +
    (∑ z ∈ R, originalEventMass
      (receiverEventKey (rejectedFrozenBad N n tau) z)) =
    (∑ key ∈ KF ∪ KR, originalEventMass key) +
    (∑ key ∈ KF ∩ KR, originalEventMass key) +
    (∑ key ∈ KF,
      (excessReceipts F (frozenOnlyBad N) key : ℝ) *
        originalEventMass key) +
    (∑ key ∈ KR,
      (excessReceipts R (rejectedFrozenBad N n tau) key : ℝ) *
        originalEventMass key) := by
  dsimp
  let F := ownPolicyFail (frozenOnly N n tau)
      (frozenOnlyBad N) N z0 Q lower
  let R := ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower
  let KF := eventKeys F (frozenOnlyBad N)
  let KR := eventKeys R (rejectedFrozenBad N n tau)
  have hf := signed_source_one_event_plus_excess F
    (frozenOnlyBad N) originalEventMass
  have hr := signed_source_one_event_plus_excess R
    (rejectedFrozenBad N n tau) originalEventMass
  have hkeys :
      (∑ key ∈ KF, originalEventMass key) +
      (∑ key ∈ KR, originalEventMass key) =
      (∑ key ∈ KF ∪ KR, originalEventMass key) +
      (∑ key ∈ KF ∩ KR, originalEventMass key) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_union_inter KF KR originalEventMass).symm
  rw [hf, hr]
  dsimp [KF, KR] at hkeys
  rw [hkeys]
  ring

end
end ImbalancedChen.Part5OriginalH430EventOccurrenceCapacity
