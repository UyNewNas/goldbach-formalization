import ImbalancedChen.Part5OriginalH430HistoricalCandidateOrder
import ImbalancedChen.FirstExitFrontierAdmission
import ImbalancedChen.OrdinaryRosserFirstExitPolicy

/-!
P5.6 / h34 — literal root-stage and post-root historical policy gates.
SOURCE ONLY / UNCOMPILED / UNEVALUATED; no formal closure credit.

This does not identify a rejected arithmetic receipt with an historical
first-excluded owner. It makes the necessary *actual* carrier, cap,
non-divisor-of-N and policy tests explicit, at two different moments:
before selecting the root p, and after some prime prefix was selected.
The full tagged q and P are retained by the two quotient-first consumers.
No unsigned or signed rejection mass is paid here.
-/

namespace ImbalancedChen.Part5OriginalH430HistoricalPolicyGates

noncomputable section
open scoped Classical
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430JointPrimePrefix
open Part5OriginalH430PhysicalCutoffOwnerOrder
open Part5OriginalH430HistoricalCandidateOrder

/-- Filtering the exact *next-selection enumeration* by a real Boolean
policy is equivalent to BOTH physical remaining-carrier membership and
that policy's next-prefix test. The candidate's sign is computed by the
enumerator, not added as an arbitrary assumption. -/
theorem accepted_next_candidate_iff
    (policy : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (frontier : FirstExitDepthState ℕ) (r : ℕ) :
    (∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates h
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix = r :: frontier.selectedPrefix ∧
      policy candidate.positive candidate.selectedPrefix = true) ↔
    r ∈ frontier.remaining ∧
      policy (!frontier.positive) (r :: frontier.selectedPrefix) = true := by
  constructor
  · rintro ⟨candidate, hc, hpref, hadmit⟩
    have hremaining := (actual_next_candidate_iff h frontier r).2
      ⟨candidate, hc, hpref⟩
    obtain ⟨before, q, after, hsplit, hstate⟩ :=
      (mem_firstExitNextSelectionCandidates_iff h frontier.selectedPrefix
        frontier.remaining frontier.positive frontier.mass candidate).1 hc
    have hqr : q = r := by
      rw [hstate] at hpref
      exact (List.cons.inj hpref).1
    have hpolicy : policy (!frontier.positive)
        (r :: frontier.selectedPrefix) = true := by
      rw [hstate] at hadmit
      simpa only [hqr] using hadmit
    exact ⟨hremaining, hpolicy⟩
  · rintro ⟨hremaining, hpolicy⟩
    obtain ⟨candidate, hc, hpref⟩ :=
      (actual_next_candidate_iff h frontier r).1 hremaining
    obtain ⟨before, q, after, hsplit, hstate⟩ :=
      (mem_firstExitNextSelectionCandidates_iff h frontier.selectedPrefix
        frontier.remaining frontier.positive frontier.mass candidate).1 hc
    have hqr : q = r := by
      rw [hstate] at hpref
      exact (List.cons.inj hpref).1
    refine ⟨candidate, hc, hpref, ?_⟩
    rw [hstate]
    simpa only [hqr] using hpolicy

/-- At the *original root selection moment*, the root is still available.
Unlike a post-root first-excluded candidate, the root must pass its own
full ordinary Rosser policy test on the singleton prefix [p]. -/
theorem root_stage_ordinary_policy_iff
    (N cap : ℕ) (z : ℝ) (lower : Bool) (Q : ℝ)
    (hzcap : z ≤ (cap : ℝ)) (p : ℕ) :
    (∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z) ∧
      candidate.selectedPrefix = [p] ∧
      ordinaryRosserRetainedPolicy lower Q
        candidate.positive candidate.selectedPrefix = true) ↔
    (p.Prime ∧ ¬p ∣ N ∧ (0 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < z) ∧
      ordinaryRosserPrefixAdmissible lower Q [p] := by
  let root : FirstExitDepthState ℕ := {
    selectedPrefix := []
    positive := true
    mass := 1
    remaining := roughPrimeUniverse N cap 0 z
  }
  have h := accepted_next_candidate_iff
    (ordinaryRosserRetainedPolicy lower Q)
    (fun r : ℕ => 1 / ((r : ℝ) - 1)) root p
  simpa [root, ordinaryRosserRetainedPolicy,
    mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzcap] using h

/-- Exact root-stage gate for the actual U3/U4 arithmetic root.
Primality comes from the original band; coprimality to N, the cap,
the strict upper endpoint, and the *root policy* are still required.
No full/selected/inherited count assertion is used. -/
theorem tagged_root_stage_ordinary_policy_iff
    (N cap : ℕ) (z : ℝ) (lower : Bool) (Q : ℝ)
    (hzcap : z ≤ (cap : ℝ)) {receiver : TaggedReceiver}
    (hr : receiver ∈ rawTagged N) :
    (∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z) ∧
      candidate.selectedPrefix = [arithmeticPrime receiver] ∧
      ordinaryRosserRetainedPolicy lower Q
        candidate.positive candidate.selectedPrefix = true) ↔
    (¬arithmeticPrime receiver ∣ N ∧
      (0 : ℝ) ≤ (arithmeticPrime receiver : ℝ) ∧
      (arithmeticPrime receiver : ℝ) < z) ∧
      ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime receiver] := by
  simpa only [raw_tagged_root_prime hr, true_and] using
    (root_stage_ordinary_policy_iff N cap z lower Q hzcap
      (arithmeticPrime receiver))

/-- After selecting a genuine historical prefix, the physical
remaining list is *strictly below the last selected prime*. The
admitted next candidate must satisfy both that capped carrier test
and the policy at its actual changed-parity prefix. -/
theorem post_root_policy_candidate_iff
    (k N cap : ℕ) (hk : 0 < k)
    (policy : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k policy
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hcap : (frontier.selectedPrefix.headD 0 : ℝ) ≤ (cap : ℝ))
    (r : ℕ) :
    (∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix = r :: frontier.selectedPrefix ∧
      policy candidate.positive candidate.selectedPrefix = true) ↔
    (r.Prime ∧ ¬r ∣ N ∧ (0 : ℝ) ≤ (r : ℝ) ∧
      (r : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ)) ∧
      policy (!frontier.positive) (r :: frontier.selectedPrefix) = true := by
  obtain ⟨_, _, _, _, hremaining, _, _⟩ :=
    actualPrimeFrontier_geometry k hk policy N cap z0 frontier hfrontier
  calc
    _ ↔ r ∈ frontier.remaining ∧
        policy (!frontier.positive) (r :: frontier.selectedPrefix) = true :=
      accepted_next_candidate_iff policy
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier r
    _ ↔ _ := by
      rw [hremaining, mem_roughPrimeUniverse_iff_of_cutoff_le_cap hcap]

/-- For an actually frozen-only (U3/U4,p,P,q) receiver in the
quotient-first branch, the correct post-root candidate is the
*quotient's* first bad prime, but only after its ORIGINAL capped
remaining-carrier and actual retention policy tests are paid. -/
theorem frozen_only_quotient_first_policy_iff
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 : ℝ)
    (policy : Bool → List ℕ → Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k policy
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hcap : (frontier.selectedPrefix.headD 0 : ℝ) ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hr : receiver ∈ frozenOnly N n tau)
    (hq : ¬ChenPrimeRough (arithmeticPrime receiver : ℝ)
      (arithmeticQuotientPrime receiver)) :
    (∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix =
        jointFirstPrime receiver ((N : ℝ)^a) :: frontier.selectedPrefix ∧
      policy candidate.positive candidate.selectedPrefix = true) ↔
    let ell := firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a)
    (ell.Prime ∧ ¬ell ∣ N ∧ (0 : ℝ) ≤ (ell : ℝ) ∧
      (ell : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ)) ∧
      policy (!frontier.positive) (ell :: frontier.selectedPrefix) = true := by
  have hfail : ¬ChenPrimeRough ((N : ℝ)^a)
      (arithmeticQuotientPrime receiver) :=
    bad_implies_not_rough (frozen_only_tagged_first_bad N n tau hr).1
  have hfirst := (joint_eq_bad_of_quotient_not_rough receiver hfail hq).1
  rw [hfirst]
  exact post_root_policy_candidate_iff k N cap hk policy z0
    frontier hfrontier hcap _

/-- Identical historical policy obligation for the distinct
rejectedFrozen lane, using its TRUE physical frozen cutoff. -/
theorem rejected_frozen_quotient_first_policy_iff
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 : ℝ)
    (policy : Bool → List ℕ → Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k policy
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hcap : (frontier.selectedPrefix.headD 0 : ℝ) ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hr : receiver ∈ rejectedFrozen N n tau)
    (hq : ¬ChenPrimeRough (arithmeticPrime receiver : ℝ)
      (arithmeticQuotientPrime receiver)) :
    (∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix =
        jointFirstPrime receiver
          (frozenPrimeCutoff N n tau (arithmeticBand receiver)
            (arithmeticPrime receiver)) :: frontier.selectedPrefix ∧
      policy candidate.positive candidate.selectedPrefix = true) ↔
    let ell := firstBadPrime (arithmeticQuotientPrime receiver)
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver))
    (ell.Prime ∧ ¬ell ∣ N ∧ (0 : ℝ) ≤ (ell : ℝ) ∧
      (ell : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ)) ∧
      policy (!frontier.positive) (ell :: frontier.selectedPrefix) = true := by
  have hfail : ¬ChenPrimeRough
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver))
      (arithmeticQuotientPrime receiver) :=
    bad_implies_not_rough (rejected_frozen_tagged_first_bad N n tau hr)
  have hfirst := (joint_eq_bad_of_quotient_not_rough receiver hfail hq).1
  rw [hfirst]
  exact post_root_policy_candidate_iff k N cap hk policy z0
    frontier hfrontier hcap _

end
end ImbalancedChen.Part5OriginalH430HistoricalPolicyGates
