import ImbalancedChen.Part5OriginalH430OriginalSelectedRootFibres

/-!
P5.6 / h34: the ORIGINAL selected U3/U4 arithmetic source under each
tagged root's ACTUAL physical Q, rather than one globally supplied Q.

The two overlapping root bands and every quotient q remain separate.
The predicates here are filters on the real originalTagged source. Their
physical Q is the existing rootQ N precision k tau p for THAT band and p;
it is not the quotient q or a new chosen frozen parameter.

This supplies a source-level root-dependent gate partition and exact
signed/cardinality receipts. It does not identify a full/selected/inherited
historical owner, pay any rejected mass, or close the full count induction.
The cutoff z0 and the sign lower remain explicit physical consumers.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalSelectedRootQFibres

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430ActualRootGateCoprime
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430OriginalRootCutoffObstruction
open Part5OriginalH430RequestedHistory

/-- The genuine frozen Q for EACH actual original (U3/U4,p,q) receipt.
Its value is constant in q at fixed (tag,p), but may differ with p/tag. -/
def originalPhysicalQ (N precision : ℕ) (tau : ℝ) :
    TaggedReceiver → ℝ
  | .inl v => rootQ N precision .U3 tau v.1
  | .inr v => rootQ N precision .U4 tau v.1

/-- The existing request history really retains that tag/p-dependent Q.
This does not identify its one root mark with the number of q receivers. -/
theorem physical_Q_U3_history
    (N precision p q : ℕ) (tau : ℝ)
    {o : Occurrence N}
    (ho : o ∈ rootHistory N precision .U3 tau p) :
    (N : ℝ) ^ o.current.node.physical.total =
      originalPhysicalQ N precision tau
        (Sum.inl (⟨p,q⟩ : TaggedPair)) := by
  simpa [originalPhysicalQ] using (rootHistory_sameQ ho)

theorem physical_Q_U4_history
    (N precision p q : ℕ) (tau : ℝ)
    {o : Occurrence N}
    (ho : o ∈ rootHistory N precision .U4 tau p) :
    (N : ℝ) ^ o.current.node.physical.total =
      originalPhysicalQ N precision tau
        (Sum.inr (⟨p,q⟩ : TaggedPair)) := by
  simpa [originalPhysicalQ] using (rootHistory_sameQ ho)

/-- Literal root licence with the existing physical Q of this very
original selected receiver. No coprimality or root gate is assumed. -/
theorem original_physical_licence_iff
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N) :
    rootLicensed N z0 (originalPhysicalQ N precision tau z) lower z ↔
      (arithmeticPrime z : ℝ) < z0 ∧
      ordinaryRosserPrefixAdmissible lower
        (originalPhysicalQ N precision tau z) [arithmeticPrime z] :=
  selected_root_licensed_iff N z0
    (originalPhysicalQ N precision tau z) lower hz

/-- The root policy is evaluated at the *real Q for this p and band*,
not a common Q across both original U3/U4 prime bands. -/
def physicalPolicyRoots (N precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) (k : Root) : Finset ℕ :=
  (originalBand N k).filter (fun p =>
    (p : ℝ) < z0 ∧
    ¬ ordinaryRosserPrefixAdmissible lower
      (rootQ N precision k tau p) [p])

def physicalPolicyPairs (N precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) (k : Root) : Finset TaggedPair :=
  (physicalPolicyRoots N precision tau z0 lower k).sigma
    (fun p => originalReceiver N p)

/-- Actual original selected receiver whose rank-one Rosser test
fails after passing the strict historical cutoff. -/
def physicalPolicyBlocked (N precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  (originalTagged N).filter (fun z =>
    (arithmeticPrime z : ℝ) < z0 ∧
    ¬ ordinaryRosserPrefixAdmissible lower
      (originalPhysicalQ N precision tau z) [arithmeticPrime z])

/-- Full original selected source rejected at its own root's physical Q. -/
def physicalRootBlocked (N precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  (originalTagged N).filter (fun z =>
    ¬ rootLicensed N z0 (originalPhysicalQ N precision tau z) lower z)

/-- Original selected source actually surviving its own physical Q root
test. This remains a receiver *set*, not a history-owner certificate. -/
def physicalRootAccepted (N precision : ℕ)
    (tau z0 : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  (originalTagged N).filter (fun z =>
    rootLicensed N z0 (originalPhysicalQ N precision tau z) lower z)

/-- The two actual failure causes are exhaustive even though each root
has its own Q. The old constant-Q gateBlocked theorem is not substituted. -/
theorem physical_root_blocked_split
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    physicalRootBlocked N precision tau z0 lower =
      rootCutoffBlocked (originalTagged N) z0 ∪
      physicalPolicyBlocked N precision tau z0 lower := by
  classical
  ext z
  simp only [physicalRootBlocked, rootCutoffBlocked,
    physicalPolicyBlocked, Finset.mem_filter, Finset.mem_union]
  by_cases hz : z ∈ originalTagged N
  · simp only [hz, true_and]
    rw [original_physical_licence_iff N precision tau z0 lower hz]
    tauto
  · simp [hz]

/-- Unlike the earlier fixed-Q fibre formula, each policy fibre uses
exactly rootQ N precision k tau p, without equating the two bands. -/
theorem physical_policy_actual_fibres
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    physicalPolicyBlocked N precision tau z0 lower =
      (physicalPolicyPairs N precision tau z0 lower .U3).disjSum
        (physicalPolicyPairs N precision tau z0 lower .U4) := by
  classical
  ext z
  cases z with
  | inl v =>
      rcases v with ⟨p,q⟩
      simp [physicalPolicyBlocked, originalPhysicalQ,
        originalTagged, originalPairs, physicalPolicyPairs,
        physicalPolicyRoots, arithmeticPrime] <;> tauto
  | inr v =>
      rcases v with ⟨p,q⟩
      simp [physicalPolicyBlocked, originalPhysicalQ,
        originalTagged, originalPairs, physicalPolicyPairs,
        physicalPolicyRoots, arithmeticPrime] <;> tauto

/-- The original q multiplicity is retained inside EACH root-dependent
physical policy failure, even when the root bands overlap. -/
theorem physical_policy_actual_card
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (physicalPolicyBlocked N precision tau z0 lower).card =
      (∑ p ∈ physicalPolicyRoots N precision tau z0 lower .U3,
        (originalReceiver N p).card) +
      (∑ p ∈ physicalPolicyRoots N precision tau z0 lower .U4,
        (originalReceiver N p).card) := by
  rw [physical_policy_actual_fibres]
  simp [physicalPolicyPairs, Finset.card_disjSum, Finset.card_sigma]

/-- Arbitrary signed and q/tag-dependent policy-failure receipts, with
actual p-dependent Q tested before each whole quotient fibre is counted. -/
theorem physical_policy_actual_signed
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ physicalPolicyBlocked N precision tau z0 lower, w z) =
      (∑ p ∈ physicalPolicyRoots N precision tau z0 lower .U3,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inl (⟨p,q⟩ : TaggedPair))) +
      (∑ p ∈ physicalPolicyRoots N precision tau z0 lower .U4,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inr (⟨p,q⟩ : TaggedPair))) := by
  rw [physical_policy_actual_fibres]
  simp [physicalPolicyPairs, Finset.sum_disjSum, Finset.sum_sigma]

private theorem cutoff_policy_disjoint
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Disjoint (rootCutoffBlocked (originalTagged N) z0)
      (physicalPolicyBlocked N precision tau z0 lower) := by
  apply Finset.disjoint_left.mpr
  intro z hc hp
  exact (Finset.mem_filter.mp hc).2 (Finset.mem_filter.mp hp).2.1

/-- Actual per-root Q source failures retain the cutoff and physical
policy fibres as two disjoint count terms. -/
theorem physical_root_blocked_card
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (physicalRootBlocked N precision tau z0 lower).card =
      (rootCutoffBlocked (originalTagged N) z0).card +
      (physicalPolicyBlocked N precision tau z0 lower).card := by
  rw [physical_root_blocked_split]
  exact Finset.card_union_of_disjoint
    (cutoff_policy_disjoint N precision tau z0 lower)

/-- No positive or signed q receipt is silently discarded when the
root's true Q varies with p and U3/U4 tag. -/
theorem physical_root_blocked_signed
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ physicalRootBlocked N precision tau z0 lower, w z) =
      (∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z) +
      (∑ z ∈ physicalPolicyBlocked N precision tau z0 lower, w z) := by
  rw [physical_root_blocked_split]
  exact Finset.sum_union (cutoff_policy_disjoint N precision tau z0 lower)

/-- Exact three-way partition of the actual original selected receivers;
this does not assign accepted receivers a completed history owner. -/
theorem original_physical_accepted_blocked_union
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    originalTagged N =
      physicalRootAccepted N precision tau z0 lower ∪
      physicalRootBlocked N precision tau z0 lower := by
  classical
  ext z
  simp [physicalRootAccepted, physicalRootBlocked]
  tauto

private theorem accepted_blocked_disjoint
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Disjoint (physicalRootAccepted N precision tau z0 lower)
      (physicalRootBlocked N precision tau z0 lower) := by
  apply Finset.disjoint_left.mpr
  intro z ha hb
  exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2

/-- Genuine currentChenUpsilon3+U4 count, with its actual original
selected q/tag occurrences, equals physical-Q root-accepted receipts
PLUS two explicit UNPAID root-failure sources. No root mark is equated
with the cardinal of a quotient fibre. -/
theorem actual_physical_selected_count_three_terms
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      ((physicalRootAccepted N precision tau z0 lower).card : ℝ) +
      ((rootCutoffBlocked (originalTagged N) z0).card : ℝ) +
      ((physicalPolicyBlocked N precision tau z0 lower).card : ℝ) := by
  have htotal : (originalTagged N).card =
      (physicalRootAccepted N precision tau z0 lower).card +
      (physicalRootBlocked N precision tau z0 lower).card := by
    rw [original_physical_accepted_blocked_union]
    exact Finset.card_union_of_disjoint
      (accepted_blocked_disjoint N precision tau z0 lower)
  have hblocked := physical_root_blocked_card N precision tau z0 lower
  have hcount : (originalTagged N).card =
      (physicalRootAccepted N precision tau z0 lower).card +
      (rootCutoffBlocked (originalTagged N) z0).card +
      (physicalPolicyBlocked N precision tau z0 lower).card := by
    omega
  calc
    _ = ((originalTagged N).card : ℝ) := original_U34_eq_tagged_card N
    _ = _ := by exact_mod_cast hcount

/-- Signed version of the three-way actual count-source partition:
the source weights can depend on tag, p and q, and no positivity is used. -/
theorem actual_physical_selected_signed_three_terms
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
      (∑ z ∈ physicalRootAccepted N precision tau z0 lower, w z) +
      (∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z) +
      (∑ z ∈ physicalPolicyBlocked N precision tau z0 lower, w z) := by
  rw [original_physical_accepted_blocked_union]
  rw [Finset.sum_union (accepted_blocked_disjoint N precision tau z0 lower)]
  rw [physical_root_blocked_signed N precision tau z0 lower]
  ring

/-- The old conditional small-presieve obstruction is stable under
the *actual varying root Q*: policy failure cannot rescue an excluded p. -/
theorem physical_selected_all_cutoff_if_small
    (N precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    physicalRootBlocked N precision tau z0 lower = originalTagged N := by
  classical
  ext z
  simp only [physicalRootBlocked, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hz
    exact ⟨hz, (raw_root_not_licensed N z0
      (originalPhysicalQ N precision tau z) lower hsmall
      (original_tagged_subset_raw_unconditional N hz))⟩

end
end ImbalancedChen.Part5OriginalH430PhysicalSelectedRootQFibres
