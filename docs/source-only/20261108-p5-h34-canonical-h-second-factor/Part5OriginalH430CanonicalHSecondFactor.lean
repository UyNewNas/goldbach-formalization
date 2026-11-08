import ImbalancedChen.Part5OriginalH430LiteralHSecondFactorReceipts
import ImbalancedChen.Part5OriginalH430ActualSecondRosserRetention

/-!
P5.6 / h34 — canonical ACTUAL retained second divisor per ORIGINAL h-start
U3/U4 quotient receipt. This is a new finite source-to-candidate allocation,
not an upper-count owner or a historical payment.

A single original q may have several distinct retained prime divisors ell<p.
Using all of them as separate receipts would multiply the original count.
Conversely, several DIFFERENT original q/tag receipts may choose the same
physical (Q,p,ell), which still cannot be charged repeatedly. This packet
establishes the first (one per q) side without claiming the second.

The h-start is the frozen manuscript's ordinary LOWER start, not a proof
that upper U3/U4 uses this z0 or this lower policy.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430CanonicalHSecondFactor

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430OriginalSecondFactorWindow
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430LiteralLowerStartReceipts
open Part5OriginalH430LiteralHSecondFactorReceipts

/-- All actually Rosser-retained second prime choices of this ORIGINAL
integer q, restricted by the real post-root ell<p carrier. The policy
uses the original tag/p-specific physical Q, not a made-up common Q. -/
def hRetainedFactors
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (z : TaggedReceiver) : Finset ℕ :=
  (Finset.range (arithmeticPrime z)).filter (fun ell =>
    ell.Prime ∧
    ell ∣ arithmeticQuotientPrime z ∧
    retainedOriginalSecond N cap precision tau
      (literalLowerStartH N) lower z ell)

/-- This finite set contains EVERY retained second prime divisor of
an original q, not just an arbitrarily selected witness. -/
theorem mem_h_retained_factors_iff
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    (ell : ℕ) :
    ell ∈ hRetainedFactors N cap precision tau lower z ↔
      ell.Prime ∧
      ell ∣ arithmeticQuotientPrime z ∧
      retainedOriginalSecond N cap precision tau
        (literalLowerStartH N) lower z ell := by
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · rintro ⟨hprime, hdiv, hret⟩
    have hlt : ell < arithmeticPrime z :=
      ((retained_original_second_iff
        N cap precision tau (literalLowerStartH N) lower
        hz hprime hdiv).mp hret).2.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hlt, ⟨hprime, hdiv, hret⟩⟩

/-- No q is declared second-eligible unless an actual retained prime
factor exists. The equivalence uses the original q and real Rosser test. -/
theorem h_retained_factors_nonempty_iff
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N) :
    (hRetainedFactors N cap precision tau lower z).Nonempty ↔
      hasRetainedOriginalSecond N cap precision tau
        (literalLowerStartH N) lower z := by
  constructor
  · rintro ⟨ell, hm⟩
    obtain ⟨hprime, hdiv, hret⟩ :=
      (mem_h_retained_factors_iff
        N cap precision tau lower hz ell).mp hm
    exact ⟨ell, hprime, hdiv, hret⟩
  · rintro ⟨ell, hprime, hdiv, hret⟩
    exact ⟨ell, (mem_h_retained_factors_iff
      N cap precision tau lower hz ell).mpr
        ⟨hprime, hdiv, hret⟩⟩

/-- Choose the LEAST actual retained factor for each ORIGINAL q receipt.
The zero fallback is never charged; a charged receipt has a proof that
the finite set is nonempty. No historical event is created by this choice. -/
def canonicalHSecond
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (z : TaggedReceiver) : ℕ :=
  if h : (hRetainedFactors N cap precision tau lower z).Nonempty then
    (hRetainedFactors N cap precision tau lower z).min' h
  else 0

theorem canonical_h_second_mem
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    (hret : hasRetainedOriginalSecond N cap precision tau
      (literalLowerStartH N) lower z) :
    canonicalHSecond N cap precision tau lower z ∈
      hRetainedFactors N cap precision tau lower z := by
  have hne : (hRetainedFactors N cap precision tau lower z).Nonempty :=
    (h_retained_factors_nonempty_iff
      N cap precision tau lower hz).mpr hret
  unfold canonicalHSecond
  simp only [dif_pos hne]
  exact Finset.min'_mem _ hne

/-- A receipt can use this one canonical second factor as its sole
candidate label. All alternative ell factors of the same q remain
unselected, while distinct q receipts are still distinct. -/
def hCanonicalReceipts
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool) :
    Finset TaggedReceiver :=
  (hStageReceipts N cap precision tau lower).filter (fun z =>
    (hRetainedFactors N cap precision tau lower z).Nonempty)

/-- The Sigma index retains the complete ORIGINAL tag,p,q occurrence.
The chosen ell is data associated with the receipt, not a quotient key. -/
def hCanonicalPairs
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool) :
    Finset (Σ _ : TaggedReceiver, ℕ) :=
  (hCanonicalReceipts N cap precision tau lower).sigma (fun z =>
    {canonicalHSecond N cap precision tau lower z})

/-- The canonical q-dependent choice does not count a receipt twice
when its original quotient has several retained prime factors. -/
theorem h_canonical_pairs_count_exact
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool) :
    (hCanonicalPairs N cap precision tau lower).card =
      (hCanonicalReceipts N cap precision tau lower).card := by
  simp [hCanonicalPairs, Finset.card_sigma]

/-- Even arbitrary signed ORIGINAL q/tag weights remain one-per-receipt.
This is not a historical signed Euler mass or a count-to-history bound. -/
theorem h_canonical_pairs_signed_exact
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ x ∈ hCanonicalPairs N cap precision tau lower, w x.1) =
      (∑ z ∈ hCanonicalReceipts N cap precision tau lower, w z) := by
  simp [hCanonicalPairs, Finset.sum_sigma]

/-- A selected canonical pair really uses an original q divisor and
passes the ACTUAL second ordinary Rosser test at its own physical Q. -/
theorem h_canonical_pair_valid
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    {x : Σ _ : TaggedReceiver, ℕ}
    (hx : x ∈ hCanonicalPairs N cap precision tau lower) :
    x.1 ∈ originalTagged N ∧
    x.2.Prime ∧
    x.2 ∣ arithmeticQuotientPrime x.1 ∧
    retainedOriginalSecond N cap precision tau
      (literalLowerStartH N) lower x.1 x.2 := by
  rcases x with ⟨z, ell⟩
  obtain ⟨hz, hell⟩ := Finset.mem_sigma.mp hx
  have hstage : z ∈ hStageReceipts N cap precision tau lower :=
    (Finset.mem_filter.mp hz).1
  have hzOriginal : z ∈ originalTagged N :=
    (Finset.mem_filter.mp hstage).1
  have hne : (hRetainedFactors N cap precision tau lower z).Nonempty :=
    (Finset.mem_filter.mp hz).2
  have hret : hasRetainedOriginalSecond N cap precision tau
      (literalLowerStartH N) lower z :=
    (h_retained_factors_nonempty_iff
      N cap precision tau lower hzOriginal).mp hne
  have heq : ell = canonicalHSecond N cap precision tau lower z :=
    Finset.mem_singleton.mp hell
  have hmem := canonical_h_second_mem
    N cap precision tau lower hzOriginal hret
  have hproperties := (mem_h_retained_factors_iff
    N cap precision tau lower hzOriginal
      (canonicalHSecond N cap precision tau lower z)).mp hmem
  simpa only [heq] using
    (show z ∈ originalTagged N ∧
        (canonicalHSecond N cap precision tau lower z).Prime ∧
        canonicalHSecond N cap precision tau lower z ∣
          arithmeticQuotientPrime z ∧
        retainedOriginalSecond N cap precision tau
          (literalLowerStartH N) lower z
          (canonicalHSecond N cap precision tau lower z) from
      ⟨hzOriginal, hproperties.1, hproperties.2.1, hproperties.2.2⟩)

/-- The canonical second candidate still occupies the TRUE h-start
window. This is a condition on the lower h-start, NOT an assertion
about the distinct upper U3/U4 H430 owner or a full/selected gate. -/
theorem h_canonical_pair_literal_window
    (N cap precision : ℕ) (tau : ℝ) (lower : Bool)
    (hzcap : literalLowerStartH N ≤ (cap : ℝ))
    {x : Σ _ : TaggedReceiver, ℕ}
    (hx : x ∈ hCanonicalPairs N cap precision tau lower) :
    (N : ℝ) ^ a ≤ (x.2 : ℝ) ∧
    (x.2 : ℝ) < (arithmeticPrime x.1 : ℝ) ∧
    (arithmeticPrime x.1 : ℝ) < (N : ℝ) ^
      Part5OriginalUpsilon5CausalDictionary.h ∧
    ordinaryRosserPrefixAdmissible lower
      (originalPhysicalQ N precision tau x.1)
      [x.2, arithmeticPrime x.1] := by
  obtain ⟨hz, hprime, hdiv, hret⟩ :=
    h_canonical_pair_valid N cap precision tau lower hx
  have hwindow := retained_original_second_window_and_policy
    N cap precision tau (literalLowerStartH N) lower
    hz hprime hdiv hret
  have hstage := ((retained_original_second_iff
    N cap precision tau (literalLowerStartH N) lower
    hz hprime hdiv).mp hret).1
  have hbelow : x.1 ∈ hStartBelow N :=
    h_start_stage_subset_below
      N cap precision tau lower hzcap
      (Finset.mem_filter.mpr ⟨hz, hstage⟩)
  exact ⟨hwindow.1, hwindow.2.1,
    (Finset.mem_filter.mp hbelow).2, hwindow.2.2⟩

end
end ImbalancedChen.Part5OriginalH430CanonicalHSecondFactor
