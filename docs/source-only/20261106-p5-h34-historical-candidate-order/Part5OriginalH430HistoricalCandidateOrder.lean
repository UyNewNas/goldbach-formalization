import ImbalancedChen.Part5OriginalH430PhysicalCutoffOwnerOrder
import ImbalancedChen.FirstExitCandidateGeometry

/-!
P5.6 / h34: actual historical next-selection CARRIER gate for the original
tagged arithmetic first prime of N-P.

SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
A prime-divisor certificate does not imply that a historical candidate is
in the causal carrier, or that its Boolean retention policy admits it.
The already-selected root p cannot be selected AGAIN at the same frontier.
No first-excluded owner identity or count-source licence is assumed.
-/

namespace ImbalancedChen.Part5OriginalH430HistoricalCandidateOrder
noncomputable section
open scoped Classical
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430JointPrimePrefix
open Part5OriginalH430PhysicalCutoffOwnerOrder

/-- Split the ACTUAL ordered remaining list at an existing occurrence.
No deduplication by product or root label is performed. -/
private theorem member_has_position {α : Type*} {r : α}
    {xs : List α} (hr : r ∈ xs) :
    ∃ before after, xs = before ++ r :: after := by
  induction xs with
  | nil => cases hr
  | cons s ss ih =>
      rcases List.mem_cons.mp hr with heq | htail
      · subst s
        exact ⟨[], ss, rfl⟩
      · obtain ⟨before, after, hsplit⟩ := ih htail
        exact ⟨s :: before, after, by simp [hsplit]⟩

/-- The actual next-selection enumerator offers a prime precisely when
it occurs in the frontier's genuine unprocessed carrier. This is only a
candidate gate; the historical Boolean policy test is still separate. -/
theorem actual_next_candidate_iff (h : ℕ → ℝ)
    (frontier : FirstExitDepthState ℕ) (r : ℕ) :
    r ∈ frontier.remaining ↔
      ∃ candidate, candidate ∈ firstExitNextSelectionCandidates h
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
        candidate.selectedPrefix = r :: frontier.selectedPrefix := by
  constructor
  · intro hr
    obtain ⟨before, after, hsplit⟩ := member_has_position hr
    refine ⟨{ selectedPrefix := r :: frontier.selectedPrefix
              positive := !frontier.positive
              mass := frontier.mass * h r
              remaining := after }, ?_, rfl⟩
    exact (mem_firstExitNextSelectionCandidates_iff h frontier.selectedPrefix
      frontier.remaining frontier.positive frontier.mass _).2
      ⟨before, r, after, hsplit, rfl⟩
  · rintro ⟨candidate, hc, hprefix⟩
    obtain ⟨before, q, after, hsplit, heq⟩ :=
      (mem_firstExitNextSelectionCandidates_iff h frontier.selectedPrefix
        frontier.remaining frontier.positive frontier.mass candidate).1 hc
    have hqr : q = r := by
      rw [heq] at hprefix
      exact (List.cons.inj hprefix).1
    rw [hsplit]
    simp [hqr]

/-- A prime already selected on the genuine retained frontier cannot
occur again in its smaller-prime remaining suffix. This uses the
original descending roughPrimeUniverse, not an unordered divisor set. -/
theorem already_selected_not_remaining
    (k N cap : ℕ) (parent : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z0))
    {p : ℕ} (hp : p ∈ frontier.selectedPrefix) :
    p ∉ frontier.remaining := by
  intro hrem
  have hlt := mem_firstExitDepthFrontier_selected_gt_remaining k parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z0)
    (roughPrimeUniverse_pairwise_gt N cap 0 z0)
    frontier hfrontier p hp p hrem
  exact (Nat.lt_irrefl p) hlt

/-- Therefore a root prime already in the selected prefix is absent
from the NEXT candidate list, even if it is the least divisor of N-P. -/
theorem already_selected_not_next_candidate
    (k N cap : ℕ) (parent : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z0))
    {p : ℕ} (hp : p ∈ frontier.selectedPrefix) :
    ¬ ∃ candidate, candidate ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix = p :: frontier.selectedPrefix := by
  intro hc
  have hrem := (actual_next_candidate_iff
    (fun r : ℕ => 1 / ((r : ℝ) - 1)) frontier p).2 hc
  exact (already_selected_not_remaining k N cap parent z0 frontier hfrontier hp) hrem

/-- The real first prime of N-P can enter the actual next-selection
history ONLY through its original remaining carrier. When it does,
the existing geometry fixes the genuine sign, mass and strict suffix.
No retention/admission decision is asserted. -/
theorem joint_first_candidate_of_remaining
    (k N cap : ℕ) (parent : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z0))
    (receiver : TaggedReceiver) (cut : ℝ)
    (hmem : jointFirstPrime receiver cut ∈ frontier.remaining) :
    ∃ candidate, candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix = jointFirstPrime receiver cut ::
        frontier.selectedPrefix ∧
      candidate.remaining = roughPrimeUniverse N cap 0
        (jointFirstPrime receiver cut : ℝ) ∧
      candidate.positive = evenListLength candidate.selectedPrefix ∧
      candidate.mass =
        (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod := by
  obtain ⟨candidate, hc, hselected⟩ := (actual_next_candidate_iff
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier
    (jointFirstPrime receiver cut)).1 hmem
  obtain ⟨_, _, _, _, hrem, hsign, hmass, _⟩ :=
    actualPrimeNextSelection_geometry k parent N cap z0
      frontier hfrontier candidate hc
  refine ⟨candidate, hc, hselected, ?_, hsign, hmass⟩
  simpa [hselected] using hrem

/-- An actual historical candidate must also belong to the ORIGINAL
prime universe (including its physical cap and strict exclusions).
Primality or divisibility of N-P alone cannot pay this gate. -/
theorem joint_candidate_requires_global_carrier
    (k N cap : ℕ) (parent : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z0))
    (receiver : TaggedReceiver) (cut : ℝ)
    (hc : ∃ candidate, candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix = jointFirstPrime receiver cut ::
        frontier.selectedPrefix) :
    jointFirstPrime receiver cut ∈ roughPrimeUniverse N cap 0 z0 := by
  have hrem := (actual_next_candidate_iff
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier
    (jointFirstPrime receiver cut)).2 hc
  have hsub : frontier.selectedPrefix.reverse ++ frontier.remaining <+
      roughPrimeUniverse N cap 0 z0 := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) []
      (roughPrimeUniverse N cap 0 z0) true 1 frontier hfrontier
  exact hsub.subset (List.mem_append.mpr (Or.inr hrem))

/-- On a REAL frozen-only arithmetic receipt, if the genuine root p
is already selected and q is p-rough, min(p,ell)=p; it cannot be
mislabelled as the next historical excluded prime. -/
theorem frozen_only_root_first_not_next
    (N n cap k : ℕ) (tau z0 : ℝ) (parent : Bool → List ℕ → Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ frozenOnly N n tau)
    (hp : arithmeticPrime receiver ∈ frontier.selectedPrefix)
    (hq : ChenPrimeRough (arithmeticPrime receiver : ℝ)
      (arithmeticQuotientPrime receiver)) :
    ¬ ∃ candidate, candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix =
        jointFirstPrime receiver ((N : ℝ)^a) :: frontier.selectedPrefix := by
  have hfail : ¬ ChenPrimeRough ((N : ℝ)^a)
      (arithmeticQuotientPrime receiver) :=
    bad_implies_not_rough (frozen_only_tagged_first_bad N n tau hr).1
  have hfirst := joint_eq_root_of_quotient_rough receiver hfail hq
  rw [hfirst]
  exact already_selected_not_next_candidate k N cap parent z0 frontier hfrontier hp

/-- The same temporal obstruction holds for the other ACTUAL rejection
lane at its distinct frozen physical cutoff. No rejection mass is paid. -/
theorem rejected_frozen_root_first_not_next
    (N n cap k : ℕ) (tau z0 : ℝ) (parent : Bool → List ℕ → Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ rejectedFrozen N n tau)
    (hp : arithmeticPrime receiver ∈ frontier.selectedPrefix)
    (hq : ChenPrimeRough (arithmeticPrime receiver : ℝ)
      (arithmeticQuotientPrime receiver)) :
    ¬ ∃ candidate, candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix =
        jointFirstPrime receiver
          (frozenPrimeCutoff N n tau (arithmeticBand receiver)
            (arithmeticPrime receiver)) :: frontier.selectedPrefix := by
  have hfail : ¬ ChenPrimeRough
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver))
      (arithmeticQuotientPrime receiver) :=
    bad_implies_not_rough (rejected_frozen_tagged_first_bad N n tau hr)
  have hfirst := joint_eq_root_of_quotient_rough receiver hfail hq
  rw [hfirst]
  exact already_selected_not_next_candidate k N cap parent z0 frontier hfrontier hp

end
end ImbalancedChen.Part5OriginalH430HistoricalCandidateOrder
