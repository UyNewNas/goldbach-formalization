import ImbalancedChen.Part5OriginalH430TaggedReceiverFibres

/-!
P5.6 / h34: full literal quotient-receiver source, actual roughness
filters, and both directions of rejection around the frozen cutoff.

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A quotient receiver q is a positive natural quotient (possibly 1 or
composite), NOT in general a prime. Every occurrence keeps (U3/U4,p,q).
The frozen-only lane and the still-rejected-at-frozen lane are distinct.
This does not assign a feedback-table owner or prove a selected-count
inequality. The actual arithmetic source is never replaced by a root
mark, a scalar request, or an unproved filter licence.
-/

namespace ImbalancedChen.Part5OriginalH430TaggedSourceRejections

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres

/-- The complete unsifted quotient source, with the original prime p
and the original overlapping root-band tag. -/
def rawPairs (N : ℕ) (k : Root) : Finset TaggedPair :=
  (originalBand N k).sigma (fun p => chenQuotientPrimeSource N p)

def rawTagged (N : ℕ) : Finset TaggedReceiver :=
  (rawPairs N .U3).disjSum (rawPairs N .U4)

/-- Missing the frozen roughness gate, while still belonging to the
original full quotient source. This is NOT the frozen-only surplus. -/
def rejectedFrozen (N n : ℕ) (tau : ℝ) : Finset TaggedReceiver :=
  rawTagged N \ frozenTagged N n tau

/-- The literal original strict-sieve rejection lane. -/
def rejectedOriginal (N : ℕ) : Finset TaggedReceiver :=
  rawTagged N \ originalTagged N

/-- Sifting is a filter on the genuine quotient source, with no
assumption that its quotient q is prime. -/
theorem frozen_receiver_mem_raw {N n p q : ℕ} {tau : ℝ} {k : Root}
    (hq : q ∈ frozenReceiver N n tau k p) :
    q ∈ chenQuotientPrimeSource N p := by
  unfold frozenReceiver chenSiftedQuotientPrimeSource at hq
  exact (Finset.mem_filter.mp hq).1

theorem frozen_pairs_subset_raw (N n : ℕ) (tau : ℝ) (k : Root) :
    frozenPairs N n tau k ⊆ rawPairs N k := by
  intro z hz
  obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp hz
  exact Finset.mem_sigma.mpr ⟨hp, frozen_receiver_mem_raw hq⟩

theorem frozen_tagged_subset_raw (N n : ℕ) (tau : ℝ) :
    frozenTagged N n tau ⊆ rawTagged N := by
  intro z hz
  cases z with
  | inl x =>
      have hx : x ∈ frozenPairs N n tau .U3 := by
        simpa [frozenTagged] using hz
      have hr := frozen_pairs_subset_raw N n tau .U3 hx
      simpa [rawTagged] using hr
  | inr x =>
      have hx : x ∈ frozenPairs N n tau .U4 := by
        simpa [frozenTagged] using hz
      have hr := frozen_pairs_subset_raw N n tau .U4 hx
      simpa [rawTagged] using hr

/-- True receiver arithmetic constraints from the quotient source.
The q label is not asserted prime: it can be 1 or composite. -/
theorem raw_quotient_data {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    0 < arithmeticQuotientPrime z ∧
    arithmeticQuotientPrime z ≤ N ∧
    Nat.Coprime (arithmeticQuotientPrime z) N := by
  cases z with
  | inl x =>
      have hx : x ∈ rawPairs N .U3 := by
        simpa [rawTagged] using hz
      exact chenQuotientPrimeSource_data ((Finset.mem_sigma.mp hx).2)
  | inr x =>
      have hx : x ∈ rawPairs N .U4 := by
        simpa [rawTagged] using hz
      exact chenQuotientPrimeSource_data ((Finset.mem_sigma.mp hx).2)

/-- Original rejection is the complement of the literal original
roughness predicate on each (tag,p,q) source fibre. -/
theorem rejected_original_U3_iff (N p q : ℕ) :
    (Sum.inl (⟨p,q⟩ : TaggedPair) : TaggedReceiver) ∈ rejectedOriginal N ↔
      p ∈ originalBand N .U3 ∧
      q ∈ chenQuotientPrimeSource N p ∧ q ∉ originalReceiver N p := by
  simp [rejectedOriginal, rawTagged, rawPairs, originalTagged,
    originalPairs] <;> tauto

theorem rejected_original_U4_iff (N p q : ℕ) :
    (Sum.inr (⟨p,q⟩ : TaggedPair) : TaggedReceiver) ∈ rejectedOriginal N ↔
      p ∈ originalBand N .U4 ∧
      q ∈ chenQuotientPrimeSource N p ∧ q ∉ originalReceiver N p := by
  simp [rejectedOriginal, rawTagged, rawPairs, originalTagged,
    originalPairs] <;> tauto

/-- Rejected at the actual frozen physical cutoff, not at an invented
sieve level and not at the original source cutoff. -/
theorem rejected_frozen_U3_iff (N n p q : ℕ) (tau : ℝ) :
    (Sum.inl (⟨p,q⟩ : TaggedPair) : TaggedReceiver) ∈ rejectedFrozen N n tau ↔
      p ∈ originalBand N .U3 ∧
      q ∈ chenQuotientPrimeSource N p ∧
      q ∉ frozenReceiver N n tau .U3 p := by
  simp [rejectedFrozen, rawTagged, rawPairs, frozenTagged,
    frozenPairs] <;> tauto

theorem rejected_frozen_U4_iff (N n p q : ℕ) (tau : ℝ) :
    (Sum.inr (⟨p,q⟩ : TaggedPair) : TaggedReceiver) ∈ rejectedFrozen N n tau ↔
      p ∈ originalBand N .U4 ∧
      q ∈ chenQuotientPrimeSource N p ∧
      q ∉ frozenReceiver N n tau .U4 p := by
  simp [rejectedFrozen, rawTagged, rawPairs, frozenTagged,
    frozenPairs] <;> tauto

private theorem raw_rejection_pair_fibres (N n : ℕ) (tau : ℝ) (k : Root) :
    rawPairs N k \ frozenPairs N n tau k =
      (originalBand N k).sigma
        (fun p => chenQuotientPrimeSource N p \ frozenReceiver N n tau k p) := by
  ext z
  rcases z with ⟨p,q⟩
  simp only [rawPairs, frozenPairs, Finset.mem_sdiff, Finset.mem_sigma]
  constructor
  · rintro ⟨⟨hp,hq⟩,hn⟩
    exact ⟨hp,hq,fun hf => hn ⟨hp,hf⟩⟩
  · rintro ⟨hp,hq,hn⟩
    exact ⟨⟨hp,hq⟩, fun hf => hn hf.2⟩

private theorem rejected_frozen_by_tag (N n : ℕ) (tau : ℝ) :
    rejectedFrozen N n tau =
      (rawPairs N .U3 \ frozenPairs N n tau .U3).disjSum
        (rawPairs N .U4 \ frozenPairs N n tau .U4) := by
  ext z
  cases z <;> simp [rejectedFrozen, rawTagged, frozenTagged]

/-- The unpaid still-rejected mass is counted with every separate q,
the two overlapping p-bands, and the literal frozen cutoff. -/
theorem rejected_frozen_card_by_fibres (N n : ℕ) (tau : ℝ) :
    (rejectedFrozen N n tau).card =
      (∑ p ∈ originalBand N .U3,
        (chenQuotientPrimeSource N p \ frozenReceiver N n tau .U3 p).card) +
      ∑ p ∈ originalBand N .U4,
        (chenQuotientPrimeSource N p \ frozenReceiver N n tau .U4 p).card := by
  rw [rejected_frozen_by_tag, Finset.card_disjSum,
    raw_rejection_pair_fibres N n tau .U3,
    raw_rejection_pair_fibres N n tau .U4]
  simp only [Finset.card_sigma]

/-- Every original rejection is EITHER admitted by freezing but still
unpaid (frozenOnly), OR rejected even after freezing. -/
theorem rejected_original_partition (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    rejectedOriginal N =
      frozenOnly N n tau ∪ rejectedFrozen N n tau := by
  have hfraw := frozen_tagged_subset_raw N n tau
  have horig := original_tagged_subset_frozen N n tau hN htau htauhi hn
  ext z
  constructor
  · intro hz
    obtain ⟨hr,ho⟩ := Finset.mem_sdiff.mp hz
    by_cases hf : z ∈ frozenTagged N n tau
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hf,ho⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hr,hf⟩))
  · intro hz
    rcases Finset.mem_union.mp hz with he | hr
    · obtain ⟨hf,ho⟩ := Finset.mem_sdiff.mp he
      exact Finset.mem_sdiff.mpr ⟨hfraw hf,ho⟩
    · obtain ⟨hraw,hnot⟩ := Finset.mem_sdiff.mp hr
      exact Finset.mem_sdiff.mpr ⟨hraw,fun ho => hnot (horig ho)⟩

theorem frozen_only_disjoint_rejected (N n : ℕ) (tau : ℝ) :
    Disjoint (frozenOnly N n tau) (rejectedFrozen N n tau) := by
  apply Finset.disjoint_left.mpr
  intro z he hr
  exact (Finset.mem_sdiff.mp hr).2 (Finset.mem_sdiff.mp he).1

/-- Exact three-lane unsifted source count. No frozen surplus or
still-rejected receiver is discarded, and no count-to-feedback bound
is smuggled into the statement. -/
theorem rejected_original_card_split (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    (rejectedOriginal N).card =
      (frozenOnly N n tau).card + (rejectedFrozen N n tau).card := by
  rw [rejected_original_partition N n tau hN htau htauhi hn]
  exact Finset.card_union_of_disjoint
    (frozen_only_disjoint_rejected N n tau)

/-- The original sieve is a subset of this precise full quotient
carrier; this uses actual cutoff inclusion and never an owner licence. -/
theorem original_tagged_subset_raw (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    originalTagged N ⊆ rawTagged N :=
  (original_tagged_subset_frozen N n tau hN htau htauhi hn).trans
    (frozen_tagged_subset_raw N n tau)

/-- The original full unsifted arithmetic source is partitioned by
the ORIGINAL strict roughness gate (no arbitrary selected mask). -/
theorem raw_original_partition (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    rawTagged N = originalTagged N ∪ rejectedOriginal N := by
  have hs := original_tagged_subset_raw N n tau hN htau htauhi hn
  ext z
  constructor
  · intro hz
    by_cases ho : z ∈ originalTagged N
    · exact Finset.mem_union.mpr (Or.inl ho)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hz,ho⟩))
  · intro hz
    rcases Finset.mem_union.mp hz with ho | hr
    · exact hs ho
    · exact (Finset.mem_sdiff.mp hr).1

private theorem original_disjoint_rejected (N : ℕ) :
    Disjoint (originalTagged N) (rejectedOriginal N) := by
  apply Finset.disjoint_left.mpr
  intro z ho hr
  exact (Finset.mem_sdiff.mp hr).2 ho

/-- All three literal arithmetic lanes, including the original
overlap multiplier, are counted without losing any q occurrence. -/
theorem raw_tagged_card_three_lanes (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    (rawTagged N).card =
      (originalTagged N).card +
      (frozenOnly N n tau).card +
      (rejectedFrozen N n tau).card := by
  have hraw : (rawTagged N).card =
      (originalTagged N).card + (rejectedOriginal N).card := by
    rw [raw_original_partition N n tau hN htau htauhi hn]
    exact Finset.card_union_of_disjoint (original_disjoint_rejected N)
  have hreject := rejected_original_card_split N n tau hN htau htauhi hn
  omega

/-- Full original U3/U4 unsifted quotient mass minus the two distinct
actual sieve rejection lanes; no equality to feedback weights is made. -/
theorem raw_U34_plus_two_rejections (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    ((rawTagged N).card : ℝ) =
      currentChenUpsilon3 N + currentChenUpsilon4 N +
      ((frozenOnly N n tau).card : ℝ) +
      ((rejectedFrozen N n tau).card : ℝ) := by
  have h := raw_tagged_card_three_lanes N n tau hN htau htauhi hn
  have hreal : ((rawTagged N).card : ℝ) =
      ((originalTagged N).card : ℝ) +
      ((frozenOnly N n tau).card : ℝ) +
      ((rejectedFrozen N n tau).card : ℝ) := by
    exact_mod_cast h
  rw [← original_U34_eq_tagged_card] at hreal
  exact hreal

end
end ImbalancedChen.Part5OriginalH430TaggedSourceRejections
