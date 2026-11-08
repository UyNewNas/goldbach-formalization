import ImbalancedChen.Part5OriginalH430LiteralLowerStartReceipts
import ImbalancedChen.Part5OriginalH430OriginalSecondFactorWindow

/-!
P5.6 / h34: literal h-start, ORIGINAL U3/U4 q-dependent second-candidate
support. This connects the genuine first-stage h-start filter to the
ACTUAL original quotient's prime-factor condition, without replacing a
tagged q receipt by a historical root mark.

A candidate post-root factor is strictly smaller than the chosen
arithmetic root p; if none exists, the original q is p-rough. The
complete original source is split into: two-step candidate-eligible
q receipts, actual admitted roots without such a factor, literal
high-band cutoff, and physical-Q root policy failures. The last three
are NOT paid historical exits; the first is NOT yet an admitted rank-two
Rosser event. No full/selected/inherited owner is asserted.

Pinned manuscript: ba6ec11; SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralHSecondFactorReceipts

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a h)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430OriginalSecondFactorWindow
open Part5OriginalH430LiteralLowerStartReceipts
open Part5OriginalH430PhysicalSelectedRootQFibres

/-- Actual h-start admitted ORIGINAL q/tag receipts, with the
original p-dependent physical Q and the ordinary singleton policy. -/
def hStageReceipts
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool) :
    Finset TaggedReceiver :=
  (originalTagged N).filter
    (selectedOriginalRootStage N cap precision tau
      (literalLowerStartH N) lower)

/-- A real admitted h-start root whose ORIGINAL integer quotient q
has a prime divisor strictly smaller than its selected p. This is
candidate support, not a selected rank-two history/event owner. -/
def hStageSecondEligible
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool) :
    Finset TaggedReceiver :=
  (hStageReceipts N cap precision tau lower).filter
    hasPostRootPrimeFactor

/-- The separate genuine h-start admitted q receipts with NO such
post-root prime factor. They cannot be silently deleted. -/
def hStageNoSecondFactor
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool) :
    Finset TaggedReceiver :=
  (hStageReceipts N cap precision tau lower).filter
    (fun z => ¬ hasPostRootPrimeFactor z)

/-- A q has no prime divisor below its selected p precisely when it
is p-rough in the manuscript's ORIGINAL quotient sense. The
threshold is p, NOT the fixed N^a roughness lower bound. -/
theorem no_second_factor_iff_p_rough (z : TaggedReceiver) :
    ¬ hasPostRootPrimeFactor z ↔
      ChenPrimeRough (arithmeticPrime z : ℝ)
        (arithmeticQuotientPrime z) := by
  constructor
  · intro h ell hell hdiv
    have hnot : ¬ ell < arithmeticPrime z := by
      intro hlt
      exact h ⟨ell, hell, hdiv, hlt⟩
    exact_mod_cast (Nat.le_of_not_gt hnot)
  · intro hrough hx
    obtain ⟨ell, hell, hdiv, hlt⟩ := hx
    have hle := hrough ell hell hdiv
    have hltReal : (ell : ℝ) < (arithmeticPrime z : ℝ) := by
      exact_mod_cast hlt
    exact (not_lt_of_ge hle) hltReal

/-- On an actual h-start original receipt, its literal q-dependent
eligibility is equivalent to EXISTENCE of an actual rank-two
ENUMERATOR candidate below p. No second Rosser admission is inferred. -/
theorem h_second_eligible_iff_real_candidate
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N) :
    z ∈ hStageSecondEligible N cap precision tau lower ↔
      ∃ ell : ℕ, ell.Prime ∧
        ell ∣ arithmeticQuotientPrime z ∧
        possibleOriginalSecond N cap precision tau
          (literalLowerStartH N) lower z ell := by
  constructor
  · intro he
    obtain ⟨hs, hf⟩ := Finset.mem_filter.mp he
    have hstage := (Finset.mem_filter.mp hs).2
    obtain ⟨ell, hell, hdiv, hlt⟩ := hf
    refine ⟨ell, hell, hdiv, ?_⟩
    exact (possible_original_second_iff N cap precision tau
      (literalLowerStartH N) lower hz hell hdiv).2 ⟨hstage, hlt⟩
  · rintro ⟨ell, hell, hdiv, hcand⟩
    obtain ⟨hstage, hlt⟩ :=
      (possible_original_second_iff N cap precision tau
        (literalLowerStartH N) lower hz hell hdiv).1 hcand
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hz, hstage⟩,
        ⟨ell, hell, hdiv, hlt⟩⟩

/-- A real two-step candidate at the actual h-start has the
THREE ordered strict/weak endpoints of the original manuscript,
with its root and its q-factor both below N^h. -/
theorem h_second_candidate_literal_window
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ))
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z)
    (hcand : possibleOriginalSecond N cap precision tau
      (literalLowerStartH N) lower z ell) :
    (N : ℝ) ^ a ≤ (ell : ℝ) ∧
      (ell : ℝ) < (arithmeticPrime z : ℝ) ∧
      (arithmeticPrime z : ℝ) < (N : ℝ) ^ h := by
  have hwindow := possible_second_factor_window N cap precision tau
    (literalLowerStartH N) lower hz hell hdiv hcand
  have hstage :=
    ((possible_original_second_iff N cap precision tau
      (literalLowerStartH N) lower hz hell hdiv).1 hcand).1
  have hbelow : z ∈ hStartBelow N :=
    h_start_stage_subset_below N cap precision tau lower hzcap
      (Finset.mem_filter.mpr ⟨hz, hstage⟩)
  exact ⟨hwindow.1, hwindow.2,
    by simpa only [literalLowerStartH] using
      (Finset.mem_filter.mp hbelow).2⟩

/-- A high-band ORIGINAL q receiver is not a two-step candidate of
the lower h tree, regardless of how many small factors q has.
A different LATER-stage owner is not excluded by this statement. -/
theorem h_high_receipt_no_second_candidate
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ))
    {z : TaggedReceiver} (hz : z ∈ hStartAtOrAbove N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z) :
    ¬ possibleOriginalSecond N cap precision tau
      (literalLowerStartH N) lower z ell := by
  intro hcand
  have hzsrc := (Finset.mem_filter.mp hz).1
  have hstage :=
    ((possible_original_second_iff N cap precision tau
      (literalLowerStartH N) lower hzsrc hell hdiv).1 hcand).1
  exact (h_start_above_no_stage N cap precision tau lower
    hzcap hz) hstage

/-- The admitted original h-start receipts without a second factor
are EXACTLY those original q values that are p-rough, not empty
receipt fibres or automatically paid first-excluded events. -/
theorem h_no_second_exact_p_rough
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    {z : TaggedReceiver} :
    z ∈ hStageNoSecondFactor N cap precision tau lower ↔
      z ∈ hStageReceipts N cap precision tau lower ∧
      ChenPrimeRough (arithmeticPrime z : ℝ)
        (arithmeticQuotientPrime z) := by
  rw [hStageNoSecondFactor, Finset.mem_filter]
  simp only [no_second_factor_iff_p_rough]

/-- Exact signed split of ONLY the genuine stage-zero q receipts
by the true divisibility predicate. No mark is multiplied by q-count. -/
theorem h_stage_receipts_signed_second_split
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ hStageReceipts N cap precision tau lower, w z) =
      (∑ z ∈ hStageSecondEligible N cap precision tau lower, w z) +
      (∑ z ∈ hStageNoSecondFactor N cap precision tau lower, w z) := by
  classical
  simpa only [hStageReceipts, hStageSecondEligible,
    hStageNoSecondFactor, Finset.sum_filter, if_not] using
    (stage_second_candidate_eligibility_signed_ledger
      N cap precision tau (literalLowerStartH N) lower w)

/-- Four genuinely different signed ORIGINAL U3/U4 q/tag lanes:
two-step candidate eligibility, admitted root but p-rough q,
high-band root cutoff, and true physical-Q singleton rejection.
It is a conservation identity, NOT a count-to-history payment. -/
theorem original_h_start_four_unpaid_signed_lanes
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ))
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
      (∑ z ∈ hStageSecondEligible N cap precision tau lower, w z) +
      (∑ z ∈ hStageNoSecondFactor N cap precision tau lower, w z) +
      (∑ z ∈ hStartAtOrAbove N, w z) +
      (∑ z ∈ physicalPolicyBlocked N precision tau
        (literalLowerStartH N) lower, w z) := by
  calc
    _ = (∑ z ∈ hStageReceipts N cap precision tau lower, w z) +
          (∑ z ∈ hStartAtOrAbove N, w z) +
          (∑ z ∈ physicalPolicyBlocked N precision tau
            (literalLowerStartH N) lower, w z) := by
            simpa only [hStageReceipts] using
              original_h_start_signed_three_unpaid_classes
                N cap precision tau lower hzcap w
    _ = _ := by
      rw [h_stage_receipts_signed_second_split]
      ring

end
end ImbalancedChen.Part5OriginalH430LiteralHSecondFactorReceipts
