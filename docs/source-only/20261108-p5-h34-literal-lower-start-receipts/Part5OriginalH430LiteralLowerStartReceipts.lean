import ImbalancedChen.Part5OriginalH430SmallPresieveReceiptObstruction
import ImbalancedChen.Part5OriginalH430ActualRootStageReceipts
import ImbalancedChen.Part5OriginalH430OriginalSelectedRootFibres
import ImbalancedChen.Part5OriginalH430PhysicalSelectedRootQFibres

/-!
P5.6 / h34: specialize ORIGINAL tagged U3/U4 q-receipts to the two
LITERAL ordinary lower starts w=a and w=h of the frozen manuscript.

These lower starts are not silently identified with the separate
symbolic projection presieve z0=N^omega. In particular, no numerical
omega is supplied in the pinned manuscript's projection sentence.
At the actual a-start, a selected original p cannot be a FIRST root.
At the h-start, only original receipts with N^a <= p < N^h can
be first-root candidates. Every p >= N^h remains an exact original
q/tag-count cutoff debt, with its original quotient multiplicity.

The singleton ordinary Rosser policy remains a separate test. This
module establishes only source/support and exact signed partitions,
NOT a full/selected/inherited owner, event payment or final h34 bound.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralLowerStartReceipts

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a h)
open Part5OriginalH430OriginalRootCutoffObstruction
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430SmallPresieveReceiptObstruction

/-- The genuine first ordinary lower start in the fixed manuscript. -/
def literalLowerStartA (N : ℕ) : ℝ := (N : ℝ) ^ a

/-- The genuine second ordinary lower start in the fixed manuscript. -/
def literalLowerStartH (N : ℕ) : ℝ := (N : ℝ) ^ h

/-- The two distinct rational exponents are not interchangeable. -/
theorem literal_lower_exponents_order : a < h := by
  norm_num [a, h]

/-- Every original U3/U4 tagged quotient receipt below the h cutoff.
This is a RECEIVER set, not a historical owner or a root-only set. -/
def hStartBelow (N : ℕ) : Finset TaggedReceiver :=
  (originalTagged N).filter
    (fun z => (arithmeticPrime z : ℝ) < literalLowerStartH N)

/-- Every original U3/U4 tagged quotient receipt at or above the h cutoff. -/
def hStartAtOrAbove (N : ℕ) : Finset TaggedReceiver :=
  (originalTagged N).filter
    (fun z => literalLowerStartH N ≤ (arithmeticPrime z : ℝ))

/-- The a-start admits NO original selected U3/U4 root to the genuine
stage-zero candidate enumerator; it does not make the history tree empty. -/
theorem literal_a_start_original_stage_empty
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartA N ≤ (cap : ℝ)) :
    (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau
        (literalLowerStartA N) lower) = ∅ := by
  exact original_stage_empty_of_small
    N cap precision tau (literalLowerStartA N) lower hzcap
    (by simp only [literalLowerStartA, le_refl])

/-- The entire literal U3+U4 count remains a cutoff RECEIPT debt
at the a-start, even when the selected q-fibre has multiple elements. -/
theorem literal_a_start_original_count_cutoff :
    ∀ N : ℕ,
      ((rootCutoffBlocked (originalTagged N)
        (literalLowerStartA N)).card : ℝ) =
        currentChenUpsilon3 N + currentChenUpsilon4 N := by
  intro N
  exact original_selected_count_cutoff_if_small
    N (literalLowerStartA N) (by simp only [literalLowerStartA, le_refl])

/-- Every h-start eligible ORIGINAL receipt stays inside the ACTUAL
original half-open band N^a <= p < N^h. -/
theorem h_start_below_in_original_band
    (N : ℕ) {z : TaggedReceiver}
    (hz : z ∈ hStartBelow N) :
    (N : ℝ) ^ a ≤ (arithmeticPrime z : ℝ) ∧
      (arithmeticPrime z : ℝ) < (N : ℝ) ^ h := by
  have hz' := Finset.mem_filter.mp hz
  exact ⟨raw_root_lower_power
      (original_tagged_subset_raw_unconditional N hz'.1),
    by simpa only [literalLowerStartH] using hz'.2⟩

/-- The original q/tag source is split at the TRUE h-start threshold,
without quotienting repeated p across the U3 and U4 tags. -/
theorem h_start_low_high_disjoint (N : ℕ) :
    Disjoint (hStartBelow N) (hStartAtOrAbove N) := by
  apply Finset.disjoint_left.mpr
  intro z hlo hhi
  exact (not_lt_of_ge (Finset.mem_filter.mp hhi).2)
    (Finset.mem_filter.mp hlo).2

theorem h_start_low_high_complete (N : ℕ) :
    hStartBelow N ∪ hStartAtOrAbove N = originalTagged N := by
  classical
  ext z
  by_cases hcut : (arithmeticPrime z : ℝ) < literalLowerStartH N
  · simp [hStartBelow, hStartAtOrAbove, hcut, not_le.mpr hcut]
  · have hh : literalLowerStartH N ≤ (arithmeticPrime z : ℝ) :=
      le_of_not_gt hcut
    simp [hStartBelow, hStartAtOrAbove, hcut, hh]

/-- The upper part is precisely the ORIGINAL root-cutoff exception,
not an arbitrary discarded subset or a newly invented event. -/
theorem h_start_above_eq_real_cutoff (N : ℕ) :
    hStartAtOrAbove N =
      rootCutoffBlocked (originalTagged N) (literalLowerStartH N) := by
  ext z
  simp [hStartAtOrAbove, rootCutoffBlocked, not_lt]

/-- A genuine stage-zero lower-h candidate must belong to the
lower h-band. The tag/p-dependent physical Q and Rosser predicate
are obtained from the literal original source, not assumed. -/
theorem h_start_stage_subset_below
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ)) :
    (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau
        (literalLowerStartH N) lower) ⊆ hStartBelow N := by
  intro z hz
  have hphys : z ∈ physicalRootAccepted
      N precision tau (literalLowerStartH N) lower := by
    rw [physical_accepted_eq_actual_stage
      N cap precision tau (literalLowerStartH N) lower hzcap]
    exact hz
  obtain ⟨hsrc, hlicensed⟩ := Finset.mem_filter.mp hphys
  have hcut := ((selected_root_licensed_iff
      N (literalLowerStartH N)
      (originalPhysicalQ N precision tau z) lower hsrc).mp hlicensed).1
  exact Finset.mem_filter.mpr ⟨hsrc, hcut⟩

/-- Every original high-band q/tag receipt fails this h-start first-root
test. No claim is made that another LATER owner cannot count it. -/
theorem h_start_above_no_stage
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ))
    {z : TaggedReceiver} (hz : z ∈ hStartAtOrAbove N) :
    ¬ selectedOriginalRootStage N cap precision tau
      (literalLowerStartH N) lower z := by
  intro hstage
  have hlo : z ∈ hStartBelow N :=
    h_start_stage_subset_below N cap precision tau lower hzcap
      (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, hstage⟩)
  exact (not_lt_of_ge (Finset.mem_filter.mp hz).2)
    (Finset.mem_filter.mp hlo).2

/-- Exact h-start cardinal source: genuine first-root candidates,
literal high-band cutoff receipts, and original physical-Q singleton
Rosser failures. No term is yet paid by a historical owner. -/
theorem original_U34_h_start_three_unpaid_classes
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ)) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      (((originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau
          (literalLowerStartH N) lower)).card : ℝ) +
      ((hStartAtOrAbove N).card : ℝ) +
      ((physicalPolicyBlocked N precision tau
        (literalLowerStartH N) lower).card : ℝ) := by
  calc
    _ = ((physicalRootAccepted N precision tau
            (literalLowerStartH N) lower).card : ℝ) +
          ((rootCutoffBlocked (originalTagged N)
            (literalLowerStartH N)).card : ℝ) +
          ((physicalPolicyBlocked N precision tau
            (literalLowerStartH N) lower).card : ℝ) :=
      actual_physical_selected_count_three_terms
        N precision tau (literalLowerStartH N) lower
    _ = _ := by rw [physical_accepted_eq_actual_stage
      N cap precision tau (literalLowerStartH N) lower hzcap,
      ← h_start_above_eq_real_cutoff N]

/-- Signed arithmetic q/tag weights are conserved, with ALL excluded
h-start high-band receipts and policy failures kept explicitly. -/
theorem original_h_start_signed_three_unpaid_classes
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ))
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
      (∑ z ∈ (originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau
          (literalLowerStartH N) lower), w z) +
      (∑ z ∈ hStartAtOrAbove N, w z) +
      (∑ z ∈ physicalPolicyBlocked N precision tau
        (literalLowerStartH N) lower, w z) := by
  calc
    _ = (∑ z ∈ physicalRootAccepted N precision tau
            (literalLowerStartH N) lower, w z) +
          (∑ z ∈ rootCutoffBlocked (originalTagged N)
            (literalLowerStartH N), w z) +
          (∑ z ∈ physicalPolicyBlocked N precision tau
            (literalLowerStartH N) lower, w z) :=
      actual_physical_selected_signed_three_terms
        N precision tau (literalLowerStartH N) lower w
    _ = _ := by rw [physical_accepted_eq_actual_stage
      N cap precision tau (literalLowerStartH N) lower hzcap,
      ← h_start_above_eq_real_cutoff N]

/-- At the literal h-start, the excluded original RECEIPTS retain
their full integer quotient fibre and separate U3/U4 bands. -/
theorem h_start_high_original_q_fibre_count (N : ℕ) :
    (hStartAtOrAbove N).card =
      (∑ p ∈ originalCutoffRoots N .U3 (literalLowerStartH N),
        (originalReceiver N p).card) +
      (∑ p ∈ originalCutoffRoots N .U4 (literalLowerStartH N),
        (originalReceiver N p).card) := by
  rw [h_start_above_eq_real_cutoff]
  exact original_selected_cutoff_card N (literalLowerStartH N)

/-- The high-band q-fibre accounting also holds for arbitrary SIGNED
original receiver weights, without an injection or double counting. -/
theorem h_start_high_original_q_fibre_signed
    (N : ℕ) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ hStartAtOrAbove N, w z) =
      (∑ p ∈ originalCutoffRoots N .U3 (literalLowerStartH N),
        ∑ q ∈ originalReceiver N p,
          w (Sum.inl (⟨p, q⟩ : TaggedPair))) +
      (∑ p ∈ originalCutoffRoots N .U4 (literalLowerStartH N),
        ∑ q ∈ originalReceiver N p,
          w (Sum.inr (⟨p, q⟩ : TaggedPair))) := by
  rw [h_start_above_eq_real_cutoff]
  exact original_selected_cutoff_signed
    N (literalLowerStartH N) w

end
end ImbalancedChen.Part5OriginalH430LiteralLowerStartReceipts
