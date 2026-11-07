import ImbalancedChen.Part5OriginalH430ActualRootGateCoprime
import ImbalancedChen.Part5OriginalH430OriginalRootCutoffObstruction

/-!
P5.6 / h34: the actual ORIGINAL U3/U4 selected-count prime/quotient
fibres under the rank-one historical root tests.

This packet does not treat one rank-one historical root mark as the
number of distinct original quotient q receivers. It takes the actual
originalTagged U3/U4 source, with its two overlapping bands and the
original strict quotient sieve. The unconditional inclusion in the
unsifted raw source avoids introducing a frozen-cutoff hypothesis merely
to establish the original root's primality and nondivisibility.

The real root cutoff is constant on each (tag,p) quotient fibre.
For a supplied Q and Rosser policy, the singleton-policy obstruction
is also constant on the entire original quotient fibre. The cardinal
and signed identities below retain every q/tag occurrence. They do
NOT establish that the supplied Q is the root-dependent physical Q,
identify a full/selected/inherited count owner, or pay any obstruction.
The special small-presieve theorem is conditional on z0 <= N^a;
no such inequality is asserted for the pinned manuscript here.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalSelectedRootFibres

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430ActualRootGateCoprime
open Part5OriginalH430OriginalRootCutoffObstruction

/-- The original sieve condition only filters the original quotient
source; it does not create additional arithmetic (p,q) occurrences. -/
theorem original_receiver_in_raw {N p q : ℕ}
    (hq : q ∈ originalReceiver N p) :
    q ∈ chenQuotientPrimeSource N p := by
  change q ∈ chenSiftedQuotientPrimeSource N p ((N : ℝ) ^ a) at hq
  unfold chenSiftedQuotientPrimeSource at hq
  exact (Finset.mem_filter.mp hq).1

/-- Unconditional inclusion, without the comparison of two sieve
cutoffs used by the frozen-source inclusion theorem. -/
theorem original_tagged_subset_raw_unconditional (N : ℕ) :
    originalTagged N ⊆ rawTagged N := by
  intro z hz
  cases z with
  | inl x =>
      have hx : x ∈ originalPairs N .U3 := by
        simpa [originalTagged] using hz
      obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp hx
      have hr : x ∈ rawPairs N .U3 :=
        Finset.mem_sigma.mpr ⟨hp, original_receiver_in_raw hq⟩
      simpa [rawTagged] using hr
  | inr x =>
      have hx : x ∈ originalPairs N .U4 := by
        simpa [originalTagged] using hz
      obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp hx
      have hr : x ∈ rawPairs N .U4 :=
        Finset.mem_sigma.mpr ⟨hp, original_receiver_in_raw hq⟩
      simpa [rawTagged] using hr

/-- All ORIGINAL selected receivers have prime roots coprime to N.
The quotient q is not asserted to be prime. -/
theorem selected_root_prime_coprime (N : ℕ)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N) :
    (arithmeticPrime z).Prime ∧
      Nat.Coprime (arithmeticPrime z) N :=
  raw_root_prime_coprime N (original_tagged_subset_raw_unconditional N hz)

/-- Exactly the original root's two surviving tests, for every
selected quotient occurrence, independent of its q label. -/
theorem selected_root_licensed_iff (N : ℕ) (z0 Q : ℝ)
    (lower : Bool) {z : TaggedReceiver}
    (hz : z ∈ originalTagged N) :
    rootLicensed N z0 Q lower z ↔
      (arithmeticPrime z : ℝ) < z0 ∧
      ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime z] :=
  raw_root_licensed_iff N z0 Q lower
    (original_tagged_subset_raw_unconditional N hz)

/-- Actual selected root primes failing the strict historical cutoff.
The entire original quotient fibre is affected, not merely one mark. -/
def originalCutoffRoots (N : ℕ) (k : Root) (z0 : ℝ) : Finset ℕ :=
  (originalBand N k).filter (fun p => ¬ (p : ℝ) < z0)

/-- Roots below the cutoff but failing the literal singleton Rosser
test for this particular supplied Q and lower/upper sign. -/
def originalPolicyRoots (N : ℕ) (k : Root)
    (z0 Q : ℝ) (lower : Bool) : Finset ℕ :=
  (originalBand N k).filter
    (fun p => (p : ℝ) < z0 ∧
      ¬ ordinaryRosserPrefixAdmissible lower Q [p])

def originalCutoffPairs (N : ℕ) (k : Root) (z0 : ℝ) :
    Finset TaggedPair :=
  (originalCutoffRoots N k z0).sigma (fun p => originalReceiver N p)

def originalPolicyPairs (N : ℕ) (k : Root)
    (z0 Q : ℝ) (lower : Bool) : Finset TaggedPair :=
  (originalPolicyRoots N k z0 Q lower).sigma
    (fun p => originalReceiver N p)

/-- For the genuine original selected U3/U4 source, every cutoff-
blocked root contributes ALL its distinct original q occurrences. -/
theorem original_selected_cutoff_fibres (N : ℕ) (z0 : ℝ) :
    rootCutoffBlocked (originalTagged N) z0 =
      (originalCutoffPairs N .U3 z0).disjSum
        (originalCutoffPairs N .U4 z0) := by
  classical
  ext z
  cases z with
  | inl v =>
      rcases v with ⟨p, q⟩
      simp [rootCutoffBlocked, originalTagged, originalPairs,
        originalCutoffPairs, originalCutoffRoots, arithmeticPrime] <;> tauto
  | inr v =>
      rcases v with ⟨p, q⟩
      simp [rootCutoffBlocked, originalTagged, originalPairs,
        originalCutoffPairs, originalCutoffRoots, arithmeticPrime] <;> tauto

/-- The second actual root obstruction also acts on a WHOLE original
p-fibre for fixed Q, not on individual quotient labels. -/
theorem original_selected_policy_fibres (N : ℕ)
    (z0 Q : ℝ) (lower : Bool) :
    rootPolicyBlocked (originalTagged N) z0 Q lower =
      (originalPolicyPairs N .U3 z0 Q lower).disjSum
        (originalPolicyPairs N .U4 z0 Q lower) := by
  classical
  ext z
  cases z with
  | inl v =>
      rcases v with ⟨p, q⟩
      simp [rootPolicyBlocked, originalTagged, originalPairs,
        originalPolicyPairs, originalPolicyRoots, arithmeticPrime] <;> tauto
  | inr v =>
      rcases v with ⟨p, q⟩
      simp [rootPolicyBlocked, originalTagged, originalPairs,
        originalPolicyPairs, originalPolicyRoots, arithmeticPrime] <;> tauto

/-- Precise original selected-count q-multiplicity in the cutoff
obstruction. In particular the two root bands are NOT deduplicated. -/
theorem original_selected_cutoff_card (N : ℕ) (z0 : ℝ) :
    (rootCutoffBlocked (originalTagged N) z0).card =
      (∑ p ∈ originalCutoffRoots N .U3 z0,
        (originalReceiver N p).card) +
      (∑ p ∈ originalCutoffRoots N .U4 z0,
        (originalReceiver N p).card) := by
  rw [original_selected_cutoff_fibres]
  simp [originalCutoffPairs, Finset.card_disjSum, Finset.card_sigma]

/-- Precise original selected-count q-multiplicity failing the
singleton retained-policy test after passing the cutoff. -/
theorem original_selected_policy_card (N : ℕ)
    (z0 Q : ℝ) (lower : Bool) :
    (rootPolicyBlocked (originalTagged N) z0 Q lower).card =
      (∑ p ∈ originalPolicyRoots N .U3 z0 Q lower,
        (originalReceiver N p).card) +
      (∑ p ∈ originalPolicyRoots N .U4 z0 Q lower,
        (originalReceiver N p).card) := by
  rw [original_selected_policy_fibres]
  simp [originalPolicyPairs, Finset.card_disjSum, Finset.card_sigma]

/-- Exact signed receipts, including arbitrary q- and tag-dependent
weights; no conversion to a single root mark is allowed. -/
theorem original_selected_cutoff_signed (N : ℕ) (z0 : ℝ)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z) =
      (∑ p ∈ originalCutoffRoots N .U3 z0,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inl (⟨p, q⟩ : TaggedPair))) +
      (∑ p ∈ originalCutoffRoots N .U4 z0,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inr (⟨p, q⟩ : TaggedPair))) := by
  rw [original_selected_cutoff_fibres]
  simp [originalCutoffPairs, Finset.sum_disjSum, Finset.sum_sigma]

theorem original_selected_policy_signed (N : ℕ)
    (z0 Q : ℝ) (lower : Bool) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rootPolicyBlocked (originalTagged N) z0 Q lower, w z) =
      (∑ p ∈ originalPolicyRoots N .U3 z0 Q lower,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inl (⟨p, q⟩ : TaggedPair))) +
      (∑ p ∈ originalPolicyRoots N .U4 z0 Q lower,
        ∑ q ∈ originalReceiver N p,
          w (Sum.inr (⟨p, q⟩ : TaggedPair))) := by
  rw [original_selected_policy_fibres]
  simp [originalPolicyPairs, Finset.sum_disjSum, Finset.sum_sigma]

/-- The literal historical root-gate failure on the ORIGINAL selected
U3/U4 arithmetic count consists of those two complete root fibres.
This still does not identify the root Q or the selected history owner. -/
theorem original_selected_gate_card (N : ℕ)
    (z0 Q : ℝ) (lower : Bool) :
    (gateBlocked (originalTagged N) N z0 Q lower).card =
      (∑ p ∈ originalCutoffRoots N .U3 z0,
        (originalReceiver N p).card) +
      (∑ p ∈ originalCutoffRoots N .U4 z0,
        (originalReceiver N p).card) +
      (∑ p ∈ originalPolicyRoots N .U3 z0 Q lower,
        (originalReceiver N p).card) +
      (∑ p ∈ originalPolicyRoots N .U4 z0 Q lower,
        (originalReceiver N p).card) := by
  have h := actual_root_gate_card N (originalTagged N)
    (original_tagged_subset_raw_unconditional N) z0 Q lower
  rw [original_selected_cutoff_card N z0,
    original_selected_policy_card N z0 Q lower] at h
  omega

/-- For a low historical presieve the COMPLETE original U3/U4
selected quotient source is cutoff-blocked, not a paid rank-one exit. -/
theorem original_selected_all_cutoff_if_small
    (N : ℕ) (z0 : ℝ) (hsmall : z0 ≤ (N : ℝ) ^ a) :
    rootCutoffBlocked (originalTagged N) z0 = originalTagged N := by
  ext z
  simp only [rootCutoffBlocked, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hz
    exact ⟨hz, raw_root_no_strict_cutoff N z0 hsmall
      (original_tagged_subset_raw_unconditional N hz)⟩

/-- Consequently the ORIGINAL U3+U4 selected-count cost remains in
the cutoff obstruction at low presieve, with every actual q and tag. -/
theorem original_selected_count_cutoff_if_small
    (N : ℕ) (z0 : ℝ) (hsmall : z0 ≤ (N : ℝ) ^ a) :
    ((rootCutoffBlocked (originalTagged N) z0).card : ℝ) =
      currentChenUpsilon3 N + currentChenUpsilon4 N := by
  rw [original_selected_all_cutoff_if_small N z0 hsmall]
  exact (original_U34_eq_tagged_card N).symm

/-- At low presieve, even the original selected p never enters the
rank-one first-exit carrier. No restriction on q is invented. -/
theorem original_selected_not_initial_carrier_if_small
    (N cap : ℕ) (z0 : ℝ)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N) :
    arithmeticPrime z ∉ roughPrimeUniverse N cap 0 z0 :=
  raw_root_not_initial_carrier N cap z0 hzcap hsmall
    (original_tagged_subset_raw_unconditional N hz)

end
end ImbalancedChen.Part5OriginalH430OriginalSelectedRootFibres
