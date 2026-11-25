import ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers
import ImbalancedChen.CurrentChenSinglePrimeUpperFiniteMean

/-!
P5.6 / h34 — exact ORIGINAL U3/U4 upper selected-count overlap.

The manuscript's original U4 prime band [N^a,N^(59/250)) is a
subset of its U3 band [N^a,N^(1/3)). The SAME original sifted
quotient q is counted once by each label on the overlap. This packet
splits the genuine tagged (p,q) source into U3-exclusive pairs and
two separately labelled U4 copies; it preserves arbitrary common
signed arithmetic weights and the literal negative Chen quarter.

Nothing identifies these copies with historical first-exit owners,
feedback root marks, or upper H430 density. A shared historical
event cannot be paid twice just because two arithmetic labels exist.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalUpperOverlapCount

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers

/-- U3-only original prime band, with the strict original U4 end. -/
def upperExclusiveBand (N : ℕ) : Finset ℕ :=
  originalBand N .U3 \ originalBand N .U4

/-- Original quotient q receipts attached to U3-only p labels. -/
def upperExclusivePairs (N : ℕ) : Finset TaggedPair :=
  (upperExclusiveBand N).sigma (fun p => originalReceiver N p)

/-- Exact original U4 selector inclusion, with its strict endpoint. -/
theorem original_u4_band_subset_u3 (N : ℕ) (hN : 1 ≤ N) :
    originalBand N .U4 ⊆ originalBand N .U3 := by
  simpa only [originalBand] using
    (currentChenUpsilon4_selector_subset_Upsilon3 hN)

/-- Complete disjoint U3 prime-band split, without deduplicating U4. -/
theorem original_u3_band_partition (N : ℕ) (hN : 1 ≤ N) :
    originalBand N .U3 =
      upperExclusiveBand N ∪ originalBand N .U4 := by
  ext p
  constructor
  · intro hp
    by_cases h4 : p ∈ originalBand N .U4
    · exact Finset.mem_union.mpr (Or.inr h4)
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_sdiff.mpr ⟨hp, h4⟩))
  · intro hp
    rcases Finset.mem_union.mp hp with he | h4
    · exact (Finset.mem_sdiff.mp he).1
    · exact original_u4_band_subset_u3 N hN h4

/-- Whole original (p,q) fibres split. q is not a root mark. -/
theorem original_u3_pairs_partition (N : ℕ) (hN : 1 ≤ N) :
    originalPairs N .U3 =
      upperExclusivePairs N ∪ originalPairs N .U4 := by
  ext x
  rcases x with ⟨p, q⟩
  simp only [originalPairs, upperExclusivePairs,
    Finset.mem_sigma, Finset.mem_union]
  constructor
  · rintro ⟨hp3, hq⟩
    by_cases hp4 : p ∈ originalBand N .U4
    · exact Or.inr ⟨hp4, hq⟩
    · exact Or.inl
        ⟨Finset.mem_sdiff.mpr ⟨hp3, hp4⟩, hq⟩
  · rintro (⟨he, hq⟩ | ⟨hp4, hq⟩)
    · exact ⟨(Finset.mem_sdiff.mp he).1, hq⟩
    · exact ⟨original_u4_band_subset_u3 N hN hp4, hq⟩

/-- Exclusively-U3 p fibres cannot overlap any U4 p fibre. -/
theorem original_exclusive_pairs_disjoint (N : ℕ) :
    Disjoint (upperExclusivePairs N) (originalPairs N .U4) := by
  apply Finset.disjoint_left.mpr
  intro x hx h4
  have he := (Finset.mem_sigma.mp hx).1
  have hp4 := (Finset.mem_sigma.mp h4).1
  exact (Finset.mem_sdiff.mp he).2 hp4

/-- Cardinality of every original q occurrence in the split. -/
theorem original_u3_pairs_card_partition (N : ℕ) (hN : 1 ≤ N) :
    (originalPairs N .U3).card =
      (upperExclusivePairs N).card +
        (originalPairs N .U4).card := by
  rw [original_u3_pairs_partition N hN]
  exact Finset.card_union_of_disjoint
    (original_exclusive_pairs_disjoint N)

/-- Signed sum before any historical owner or Euler-payment claim. -/
theorem original_u3_pairs_signed_partition (N : ℕ) (hN : 1 ≤ N)
    (w : TaggedPair → ℝ) :
    (∑ x ∈ originalPairs N .U3, w x) =
      (∑ x ∈ upperExclusivePairs N, w x) +
        ∑ x ∈ originalPairs N .U4, w x := by
  rw [original_u3_pairs_partition N hN,
    Finset.sum_union (original_exclusive_pairs_disjoint N)]

/-- Every original U4 (p,q) has TWO different upper-root tags.
Double arithmetic weight does not allow double historical payment. -/
theorem original_tagged_common_weight_double (N : ℕ) (hN : 1 ≤ N)
    (w : TaggedPair → ℝ) :
    (∑ z ∈ originalTagged N, Sum.elim w w z) =
      (∑ x ∈ upperExclusivePairs N, w x) +
        2 * (∑ x ∈ originalPairs N .U4, w x) := by
  have htag :
      (∑ z ∈ originalTagged N, Sum.elim w w z) =
        (∑ x ∈ originalPairs N .U3, w x) +
          (∑ x ∈ originalPairs N .U4, w x) := by
    simp [originalTagged, Finset.sum_disjSum]
  rw [htag, original_u3_pairs_signed_partition N hN w]
  ring

/-- Exact CURRENT U3+U4 integer receiver count, including both tags. -/
theorem original_U34_count_double_overlap (N : ℕ) (hN : 1 ≤ N) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      ((upperExclusivePairs N).card : ℝ) +
        2 * ((originalPairs N .U4).card : ℝ) := by
  have htag : (originalTagged N).card =
      (originalPairs N .U3).card +
        (originalPairs N .U4).card := by
    simp [originalTagged, Finset.card_disjSum]
  have hcount : (originalTagged N).card =
      (upperExclusivePairs N).card +
        2 * (originalPairs N .U4).card := by
    rw [htag, original_u3_pairs_card_partition N hN]
    omega
  rw [original_U34_eq_tagged_card]
  exact_mod_cast hcount

/-- Literal Chen negative-quarter of the two original upper labels. -/
def originalU34SignedQuarter (N : ℕ) : ℝ :=
  -(currentChenUpsilon3 N + currentChenUpsilon4 N) / 4

/-- The shared original q-fibre has -1/2, not -1/4, root weight.
This is a source identity, not an upper-count-to-history estimate. -/
theorem original_U34_negative_quarter_overlap (N : ℕ) (hN : 1 ≤ N) :
    originalU34SignedQuarter N =
      -(1 / 4 : ℝ) * ((upperExclusivePairs N).card : ℝ) -
        (1 / 2 : ℝ) * ((originalPairs N .U4).card : ℝ) := by
  rw [originalU34SignedQuarter,
    original_U34_count_double_overlap N hN]
  ring

/-- Each U3-exclusive receipt still carries its full original q fibre. -/
theorem original_exclusive_pairs_card_fibres (N : ℕ) :
    (upperExclusivePairs N).card =
      ∑ p ∈ upperExclusiveBand N,
        (originalReceiver N p).card := by
  simp [upperExclusivePairs, Finset.card_sigma]

end
end ImbalancedChen.Part5OriginalH430OriginalUpperOverlapCount
