import ImbalancedChen.Part5OriginalH430StageZeroMassFibreGap
import ImbalancedChen.Part5OriginalH430PostRootRemainingExact

/-!
P5.6 / h34: the ORIGINAL selected U3/U4 quotient's first possible
post-root historical prime-factor window.

The quotient q is an INTEGER, not necessarily a prime. After a true
rank-one first-exit root candidate p, its genuine remaining carrier
only contains primes strictly below p. An original selected quotient is
rough at N^a, so any factor of q that can be offered as the next
candidate must lie in the half-open window [N^a,p).

These are genuine rank-two ENUMERATOR candidates, not admitted
Rosser branches, full/selected/inherited owners, or paid q receipts.
Different tagged (p,q) receipts are not identified and no historical
candidate is replicated to pay several q receipts.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalSecondFactorWindow

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430StageZeroMassFibreGap
open Part5OriginalH430QuotientBadPhysicalCarrier
open Part5OriginalH430HistoricalCandidateOrder

/-- The original sieve protects q at the ORIGINAL N^a threshold,
not at the root-dependent frozen max-two threshold. -/
theorem original_quotient_is_rough (N : ℕ)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N) :
    ChenPrimeRough ((N : ℝ) ^ a) (arithmeticQuotientPrime z) := by
  cases z with
  | inl x =>
      rcases x with ⟨p, q⟩
      have hpq : (⟨p, q⟩ : TaggedPair) ∈ originalPairs N .U3 := by
        simpa [originalTagged] using hz
      have hq : q ∈ originalReceiver N p := (Finset.mem_sigma.mp hpq).2
      change q ∈ (chenQuotientPrimeSource N p).filter
        (ChenPrimeRough ((N : ℝ) ^ a)) at hq
      exact (Finset.mem_filter.mp hq).2
  | inr x =>
      rcases x with ⟨p, q⟩
      have hpq : (⟨p, q⟩ : TaggedPair) ∈ originalPairs N .U4 := by
        simpa [originalTagged] using hz
      have hq : q ∈ originalReceiver N p := (Finset.mem_sigma.mp hpq).2
      change q ∈ (chenQuotientPrimeSource N p).filter
        (ChenPrimeRough ((N : ℝ) ^ a)) at hq
      exact (Finset.mem_filter.mp hq).2

/-- A prime divisor of a genuine original q is never BELOW N^a.
This is a theorem about the original selected source, not an
additional roughness premise on a generated request. -/
theorem original_quotient_factor_lower
    (N : ℕ) {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z) :
    (N : ℝ) ^ a ≤ (ell : ℝ) :=
  original_quotient_is_rough N hz ell hell hdiv

/-- Fix a literal stage-zero candidate c with prefix [p].
For a prime divisor ell of this ORIGINAL q, membership in the true
post-root remaining carrier is EQUIVALENT to ell < p. The real cap,
target exclusion, original quotient q, and enumerator are all used. -/
theorem original_factor_in_rank_one_suffix_iff
    (N cap : ℕ) (z0 : ℝ)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z)
    (c : FirstExitDepthState ℕ)
    (hc : c ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hp : c.selectedPrefix = [arithmeticPrime z]) :
    ell ∈ c.remaining ↔ ell < arithmeticPrime z := by
  have hrem := stage_zero_candidate_exact_suffix
    N cap (arithmeticPrime z) z0 c hc hp
  obtain ⟨before, r, after, hlist, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] (roughPrimeUniverse N cap 0 z0) true 1 c).mp hc
  have hrp : r = arithmeticPrime z := by
    rw [hstate] at hp
    exact (List.cons.inj hp).1
  subst r
  have hrootMem : arithmeticPrime z ∈ roughPrimeUniverse N cap 0 z0 := by
    rw [hlist]
    simp
  have hrootCap : arithmeticPrime z < cap :=
    ((mem_roughPrimeUniverse).mp hrootMem).1
  have hraw : z ∈ rawTagged N :=
    original_tagged_subset_raw_unconditional N hz
  have hnotN : ¬ ell ∣ N :=
    raw_quotient_factor_not_target hraw hell hdiv
  constructor
  · intro he
    rw [hrem] at he
    exact_mod_cast (mem_roughPrimeUniverse_upper he)
  · intro hlt
    rw [hrem]
    have hltReal : (ell : ℝ) < (arithmeticPrime z : ℝ) := by
      exact_mod_cast hlt
    exact (mem_roughPrimeUniverse).mpr
      ⟨lt_trans hlt hrootCap, hell, hnotN, Nat.cast_nonneg _, hltReal⟩

/-- The second-rank enumerator offers exactly the eligible prime
factors below p. This does NOT pass the second Rosser test or create
an owner in the original selected-count consumer. -/
theorem original_factor_next_candidate_iff
    (N cap : ℕ) (z0 : ℝ)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z)
    (c : FirstExitDepthState ℕ)
    (hc : c ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hp : c.selectedPrefix = [arithmeticPrime z]) :
    (∃ d, d ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      c.selectedPrefix c.positive c.mass c.remaining ∧
      d.selectedPrefix = ell :: c.selectedPrefix) ↔
        ell < arithmeticPrime z := by
  exact (actual_next_candidate_iff
    (fun r : ℕ => 1 / ((r : ℝ) - 1)) c ell).symm.trans
    (original_factor_in_rank_one_suffix_iff
      N cap z0 hz hell hdiv c hc hp)

/-- Real candidate gate at the original physical per-(tag,p) Q.
Neither ell nor q is declared to be a newly selected history owner. -/
def possibleOriginalSecond
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ) : Prop :=
  ∃ c d : FirstExitDepthState ℕ,
    c ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
    c.selectedPrefix = [arithmeticPrime z] ∧
    ordinaryRosserRetainedPolicy lower
      (originalPhysicalQ N precision tau z)
      c.positive c.selectedPrefix = true ∧
    d ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      c.selectedPrefix c.positive c.mass c.remaining ∧
    d.selectedPrefix = ell :: c.selectedPrefix

/-- The conditional two-step candidate is precisely a REAL admitted
rank-one root plus a factor strictly below that root. The q factor
premises are sourced from the original arithmetic receipt. -/
theorem possible_original_second_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z) :
    possibleOriginalSecond N cap precision tau z0 lower z ell ↔
      selectedOriginalRootStage N cap precision tau z0 lower z ∧
      ell < arithmeticPrime z := by
  constructor
  · rintro ⟨c, d, hc, hp, hpolicy, hd, hprefix⟩
    have hlt := (original_factor_next_candidate_iff
      N cap z0 hz hell hdiv c hc hp).mp ⟨d, hd, hprefix⟩
    exact ⟨⟨c, hc, hp, hpolicy⟩, hlt⟩
  · rintro ⟨⟨c, hc, hp, hpolicy⟩, hlt⟩
    obtain ⟨d, hd, hprefix⟩ :=
      (original_factor_next_candidate_iff
        N cap z0 hz hell hdiv c hc hp).mpr hlt
    exact ⟨c, d, hc, hp, hpolicy, hd, hprefix⟩

/-- A TRUE possible second selection has the original rank-two
positive parity and *product* weight, not a new q-receipt unit mass. -/
theorem second_candidate_true_mass_sign
    (N cap : ℕ) (z0 : ℝ)
    (p ell : ℕ) (c d : FirstExitDepthState ℕ)
    (hc : c ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hp : c.selectedPrefix = [p])
    (hd : d ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      c.selectedPrefix c.positive c.mass c.remaining)
    (hdprefix : d.selectedPrefix = ell :: c.selectedPrefix) :
    d.positive = true ∧
    d.mass = historicalFirstRootMass p * (1 / ((ell : ℝ) - 1)) := by
  obtain ⟨before, r, after, hlist, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      c.selectedPrefix c.remaining c.positive c.mass d).mp hd
  rw [hstate] at hdprefix
  have hr : r = ell := (List.cons.inj hdprefix).1
  subst r
  obtain ⟨hsgn, hmass⟩ :=
    stage_zero_candidate_mass_sign N cap p z0 c hc hp
  rw [hstate]
  simp [hsgn, hmass]

/-- The half-open physical factor window is a NECESSARY condition
for a q-labelled second-rank candidate. In particular the original
sieve never supplies an ell below N^a to this history. -/
theorem possible_second_factor_window
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z)
    (hsecond : possibleOriginalSecond
      N cap precision tau z0 lower z ell) :
    (N : ℝ) ^ a ≤ (ell : ℝ) ∧
      (ell : ℝ) < (arithmeticPrime z : ℝ) := by
  have hlt := ((possible_original_second_iff
    N cap precision tau z0 lower hz hell hdiv).mp hsecond).2
  exact ⟨original_quotient_factor_lower N hz hell hdiv, by exact_mod_cast hlt⟩

/-- This property is per original tagged q, not per root mark. -/
def hasPostRootPrimeFactor (z : TaggedReceiver) : Prop :=
  ∃ ell : ℕ, ell.Prime ∧
    ell ∣ arithmeticQuotientPrime z ∧ ell < arithmeticPrime z

/-- Exact signed partition of admitted original (tag,p,q) receipts
into q values with/without a possible post-root prime factor. The
second sum is UNPAID; the first is only candidate-eligible, not paid. -/
theorem stage_second_candidate_eligibility_signed_ledger
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower), w z) =
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if hasPostRootPrimeFactor z then w z else 0) +
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if hasPostRootPrimeFactor z then 0 else w z) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : hasPostRootPrimeFactor z <;> simp [h]

end
end ImbalancedChen.Part5OriginalH430OriginalSecondFactorWindow
