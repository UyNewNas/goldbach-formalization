import ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers

/-!
P5.6 / h34: exact fibres and explicit surplus of the actual
tagged frozen U3/U4 arithmetic receiver source.

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
These identities work with finite (root-band, p, q) arithmetic labels.
They do NOT identify any q with a feedback request occurrence, nor
replace a selected/full/inherited filter or a count induction.
-/

namespace ImbalancedChen.Part5OriginalH430TaggedReceiverFibres

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers

/-- The root-band tag of an arithmetic receiver is data, not an
owner chosen by the generated feedback table. -/
def arithmeticBand : TaggedReceiver → Root
  | .inl _ => .U3
  | .inr _ => .U4

/-- The original selected prime is never replaced by the sieve
receiver q or by a feedback origin. -/
def arithmeticPrime : TaggedReceiver → ℕ
  | .inl z => z.1
  | .inr z => z.1

def arithmeticQuotientPrime : TaggedReceiver → ℕ
  | .inl z => z.2
  | .inr z => z.2

/-- The triple of original labels determines the tagged arithmetic
receiver.  In particular overlapping U3/U4 roots are NOT merged. -/
theorem arithmetic_labels_injective :
    Function.Injective (fun z : TaggedReceiver =>
      (arithmeticBand z, arithmeticPrime z, arithmeticQuotientPrime z)) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          obtain ⟨p,q⟩ := x
          obtain ⟨p',q'⟩ := y
          simp only [arithmeticBand, arithmeticPrime,
            arithmeticQuotientPrime, Prod.mk.injEq] at hxy
          rcases hxy with ⟨_,hp,hq⟩
          subst p'
          subst q'
          rfl
      | inr y =>
          simp [arithmeticBand] at hxy
  | inr x =>
      cases y with
      | inl y =>
          simp [arithmeticBand] at hxy
      | inr y =>
          obtain ⟨p,q⟩ := x
          obtain ⟨p',q'⟩ := y
          simp only [arithmeticBand, arithmeticPrime,
            arithmeticQuotientPrime, Prod.mk.injEq] at hxy
          rcases hxy with ⟨_,hp,hq⟩
          subst p'
          subst q'
          rfl

/-- Every frozen arithmetic receiver retains its actual original
root prime and original source band, separately for both tags. -/
theorem frozen_tagged_band {N n : ℕ} {tau : ℝ}
    {z : TaggedReceiver} (hz : z ∈ frozenTagged N n tau) :
    arithmeticPrime z ∈ originalBand N (arithmeticBand z) := by
  cases z with
  | inl x =>
      exact (Finset.mem_sigma.mp
        (by simpa [frozenTagged] using hz : x ∈ frozenPairs N n tau .U3)).1
  | inr x =>
      exact (Finset.mem_sigma.mp
        (by simpa [frozenTagged] using hz : x ∈ frozenPairs N n tau .U4)).1

/-- Exact extra-receiver membership in the U3 band.  This is a
literal arithmetic rejection lane, not an assertion of small mass. -/
theorem frozen_only_U3_iff (N n p q : ℕ) (tau : ℝ) :
    (Sum.inl (⟨p,q⟩ : TaggedPair) : TaggedReceiver) ∈ frozenOnly N n tau ↔
      p ∈ originalBand N .U3 ∧
      q ∈ frozenReceiver N n tau .U3 p ∧
      q ∉ originalReceiver N p := by
  simp [frozenOnly, frozenTagged, originalTagged,
    frozenPairs, originalPairs] <;> tauto

theorem frozen_only_U4_iff (N n p q : ℕ) (tau : ℝ) :
    (Sum.inr (⟨p,q⟩ : TaggedPair) : TaggedReceiver) ∈ frozenOnly N n tau ↔
      p ∈ originalBand N .U4 ∧
      q ∈ frozenReceiver N n tau .U4 p ∧
      q ∉ originalReceiver N p := by
  simp [frozenOnly, frozenTagged, originalTagged,
    frozenPairs, originalPairs] <;> tauto

/-- Sigma differences distribute over SAME p fibres, without
quotienting q or counting the root p only once. -/
private theorem pair_difference_fibres (N n : ℕ) (tau : ℝ) (k : Root) :
    frozenPairs N n tau k \ originalPairs N k =
      (originalBand N k).sigma
        (fun p => frozenReceiver N n tau k p \ originalReceiver N p) := by
  ext z
  rcases z with ⟨p,q⟩
  simp only [frozenPairs, originalPairs, Finset.mem_sdiff, Finset.mem_sigma]
  constructor
  · rintro ⟨⟨hp,hf⟩,hn⟩
    exact ⟨hp, hf, fun hq => hn ⟨hp,hq⟩⟩
  · rintro ⟨hp,hf,hn⟩
    exact ⟨⟨hp,hf⟩, fun ho => hn ho.2⟩

/-- Disjoint tags preserve the entire physical occurrence difference
as two separate sigma families. -/
private theorem frozen_only_by_tag (N n : ℕ) (tau : ℝ) :
    frozenOnly N n tau =
      (frozenPairs N n tau .U3 \ originalPairs N .U3).disjSum
        (frozenPairs N n tau .U4 \ originalPairs N .U4) := by
  ext z
  cases z <;> simp [frozenOnly, frozenTagged, originalTagged]

/-- Exact per-root arithmetic surplus.  No analytic estimate has
been applied to these counts, and the overlap is paid twice. -/
theorem frozen_only_card_by_fibres (N n : ℕ) (tau : ℝ) :
    (frozenOnly N n tau).card =
      (∑ p ∈ originalBand N .U3,
        (frozenReceiver N n tau .U3 p \ originalReceiver N p).card) +
      ∑ p ∈ originalBand N .U4,
        (frozenReceiver N n tau .U4 p \ originalReceiver N p).card := by
  rw [frozen_only_by_tag, Finset.card_disjSum,
    pair_difference_fibres N n tau .U3,
    pair_difference_fibres N n tau .U4]
  simp only [Finset.card_sigma]

/-- Exact set partition under the already-proved original-to-frozen
inclusion.  This is NOT the full selected-history decomposition. -/
theorem frozen_tagged_partition (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    frozenTagged N n tau = originalTagged N ∪ frozenOnly N n tau := by
  have hs := original_tagged_subset_frozen N n tau hN htau htauhi hn
  ext z
  constructor
  · intro hz
    by_cases ho : z ∈ originalTagged N
    · exact Finset.mem_union.mpr (Or.inl ho)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hz,ho⟩))
  · intro hz
    rcases Finset.mem_union.mp hz with ho | he
    · exact hs ho
    · exact (Finset.mem_sdiff.mp he).1

theorem original_extra_disjoint (N n : ℕ) (tau : ℝ) :
    Disjoint (originalTagged N) (frozenOnly N n tau) := by
  apply Finset.disjoint_left.mpr
  intro z ho he
  exact (Finset.mem_sdiff.mp he).2 ho

/-- Exact finite card equality.  The surplus is not dropped, and
there is no assumption that it vanishes. -/
theorem frozen_tagged_card_split (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    (frozenTagged N n tau).card =
      (originalTagged N).card + (frozenOnly N n tau).card := by
  rw [frozen_tagged_partition N n tau hN htau htauhi hn]
  exact Finset.card_union_of_disjoint (original_extra_disjoint N n tau)

/-- Exact original U3+U4 accounting, with EVERY additional receiver
in the frozen sieve still present as a positive, unpaid lane. -/
theorem original_U34_plus_extra_eq_frozen (N n : ℕ) (tau : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    currentChenUpsilon3 N + currentChenUpsilon4 N +
      ((frozenOnly N n tau).card : ℝ) =
      ((frozenTagged N n tau).card : ℝ) := by
  rw [original_U34_eq_tagged_card]
  exact_mod_cast (frozen_tagged_card_split N n tau hN htau htauhi hn).symm

end
end ImbalancedChen.Part5OriginalH430TaggedReceiverFibres
