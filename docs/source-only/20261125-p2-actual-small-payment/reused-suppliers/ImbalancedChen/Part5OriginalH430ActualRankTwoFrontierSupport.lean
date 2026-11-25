import ImbalancedChen.Part5OriginalH430ActualSecondRosserRetention
import ImbalancedChen.FirstExitFrontierInvariants
import ImbalancedChen.FirstExitCandidateGeometry

/-!
P5.6 / h34: lift actual two-step ordinary-Rosser-retained ORIGINAL
q prime factors into the genuine recursive firstExitDepthFrontier 2.
The prefix, physical per-tag/root Q, alternating sign, true mass
and original q-factor window are retained.

ONE-WAY SUPPORT ONLY: not a full/selected/inherited owner, not an
injective q-to-history map, not a mass payment, not an h34 closure.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRankTwoFrontierSupport

noncomputable section
open scoped Classical
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430StageZeroMassFibreGap
open Part5OriginalH430OriginalSecondFactorWindow
open Part5OriginalH430ActualSecondRosserRetention

/-- An unprocessed label can always be skipped when the rank is not
yet reached, whether or not its selection would have passed policy. -/
private theorem skip_preserves_frontier
    {α : Type*} (k : ℕ) (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (r : α) (rs : List α) (state : FirstExitDepthState α)
    (hpre : pre.length < k)
    (hs : state ∈ firstExitDepthFrontier k policy h pre positive mass rs) :
    state ∈ firstExitDepthFrontier k policy h pre positive mass (r :: rs) := by
  have hk : ¬ k ≤ pre.length := Nat.not_le_of_gt hpre
  rw [firstExitDepthFrontier, if_neg hk]
  by_cases hr : policy (!positive) (r :: pre) = true
  · rw [if_pos hr, List.mem_append]
    exact Or.inl hs
  · simpa only [if_neg hr, List.append_nil] using hs

/-- One selected *literal* next candidate whose real policy passes
lifts every retained continuation of its untouched suffix to the
original recursion. Skipped labels are handled by the skip branch. -/
private theorem retained_next_lifts_to_frontier
    {α : Type*} (k : ℕ) (policy : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (candidate state : FirstExitDepthState α)
    (hpre : pre.length < k)
    (hc : candidate ∈ firstExitNextSelectionCandidates
      h pre positive mass remaining)
    (hpolicy : policy candidate.positive candidate.selectedPrefix = true)
    (hcont : state ∈ firstExitDepthFrontier k policy h
      candidate.selectedPrefix candidate.positive candidate.mass
      candidate.remaining) :
    state ∈ firstExitDepthFrontier k policy h pre positive mass remaining := by
  obtain ⟨before, q, after, hremaining, hcstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      h pre remaining positive mass candidate).mp hc
  subst candidate
  subst remaining
  change policy (!positive) (q :: pre) = true at hpolicy
  change state ∈ firstExitDepthFrontier k policy h
    (q :: pre) (!positive) (mass * h q) after at hcont
  have hk : ¬ k ≤ pre.length := Nat.not_le_of_gt hpre
  have hselected : state ∈ firstExitDepthFrontier k policy h
      pre positive mass (q :: after) := by
    rw [firstExitDepthFrontier, if_neg hk, if_pos hpolicy, List.mem_append]
    exact Or.inr hcont
  induction before with
  | nil =>
      simpa only [List.nil_append] using hselected
  | cons r before ih =>
      simpa only [List.cons_append] using
        (skip_preserves_frontier k policy h pre positive mass
          r (before ++ q :: after) state hpre ih)

/-- The actual second Rosser-retained original quotient factor reaches
a REAL rank-two recursive frontier at its root-specific physical Q.
The returned state has precisely its true positive sign and product
historical mass, not an independently paid q receipt. -/
theorem retained_original_second_in_actual_rank_two_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ)
    (hret : retainedOriginalSecond
      N cap precision tau z0 lower z ell) :
    ∃ d : FirstExitDepthState ℕ,
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [ell, arithmeticPrime z] ∧
      d.positive = true ∧
      d.mass = historicalFirstRootMass (arithmeticPrime z) *
        (1 / ((ell : ℝ) - 1)) := by
  let policy : Bool → List ℕ → Bool :=
    ordinaryRosserRetainedPolicy lower (originalPhysicalQ N precision tau z)
  let weight : ℕ → ℝ := fun r => 1 / ((r : ℝ) - 1)
  obtain ⟨c, d, hc, hp, hroot, hd, hdpre, hsecond⟩ := hret
  have hlen : 2 ≤ d.selectedPrefix.length := by
    rw [hdpre, hp]
    decide
  have hstop : d ∈ firstExitDepthFrontier 2 policy weight
      d.selectedPrefix d.positive d.mass d.remaining := by
    rw [firstExitDepthFrontier_of_rank_le_length 2 policy weight
      d.selectedPrefix d.remaining d.positive d.mass hlen]
    cases d
    simp
  have hrootlen : c.selectedPrefix.length < 2 := by
    simpa only [hp, List.length_cons, List.length_nil] using
      (show 1 < 2 from by decide)
  have hafterRoot : d ∈ firstExitDepthFrontier 2 policy weight
      c.selectedPrefix c.positive c.mass c.remaining := by
    exact retained_next_lifts_to_frontier 2 policy weight
      c.selectedPrefix c.positive c.mass c.remaining d d
      hrootlen hd hsecond hstop
  have hfrontier : d ∈ firstExitDepthFrontier 2 policy weight
      [] true 1 (roughPrimeUniverse N cap 0 z0) := by
    exact retained_next_lifts_to_frontier 2 policy weight
      [] true 1 (roughPrimeUniverse N cap 0 z0) c d
      (by decide) hc hroot hafterRoot
  obtain ⟨hsign, hmass⟩ := second_candidate_true_mass_sign
    N cap z0 (arithmeticPrime z) ell c d hc hp hd hdpre
  refine ⟨d, hfrontier, ?_, hsign, hmass⟩
  simpa only [hp] using hdpre

/-- A tagged ORIGINAL (p,q) receipt with a retained q prime factor
has rank-two frontier support. This keeps the genuine roughness window,
the original q divisibility, per-root Q, and one actual history state.
Several q/tag receipts may share the same frontier state. -/
theorem original_retained_receipt_rank_two_support
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    (hret : hasRetainedOriginalSecond
      N cap precision tau z0 lower z) :
    ∃ ell : ℕ, ∃ d : FirstExitDepthState ℕ,
      ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
      (N : ℝ) ^ Part5OriginalUpsilon5CausalDictionary.a ≤ (ell : ℝ) ∧
      (ell : ℝ) < (arithmeticPrime z : ℝ) ∧
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [ell, arithmeticPrime z] ∧
      d.positive = true ∧
      d.mass = historicalFirstRootMass (arithmeticPrime z) *
        (1 / ((ell : ℝ) - 1)) := by
  obtain ⟨ell, hell, hdiv, hsecond⟩ := hret
  obtain ⟨hlower, hupper, _⟩ :=
    retained_original_second_window_and_policy
      N cap precision tau z0 lower hz hell hdiv hsecond
  obtain ⟨d, hd, hprefix, hsign, hmass⟩ :=
    retained_original_second_in_actual_rank_two_frontier
      N cap precision tau z0 lower z ell hsecond
  exact ⟨ell, d, hell, hdiv, hlower, hupper, hd, hprefix, hsign, hmass⟩

end
end ImbalancedChen.Part5OriginalH430ActualRankTwoFrontierSupport
