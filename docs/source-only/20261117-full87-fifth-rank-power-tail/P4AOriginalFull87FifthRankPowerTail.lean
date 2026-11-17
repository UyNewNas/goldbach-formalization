import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous ordered-history packet established a genuine sixth-product
power bound for a fifth-exclusive event, but retained an artificial
explicit length-five hypothesis. Here this hypothesis is DISCHARGED
from the original fifthSixthWithoutBoth list producer and the original
shared rank-four source.

For an actual full modulus a*b6 at a surviving fifth-exclusive
sixth-positive candidate, strict X<a*b6 forces
  X^5 < a^5*b5^6.
Conversely a^5*b5^6 <= X^5 excludes that high-q modulus.
This is a literal per-candidate, per-a arithmetic cutoff, not a
vanishing theorem for every fifth event or an analytic tail estimate.
The large region remains in the original signed physical rho.
-/

namespace ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_fifth_exclusive_sixth_modulus_power_bound)

/-- The genuine fifth-exclusive constructors add exactly ONE selected
prime to the incoming history. The fifth-BOTH case emits only sixth
events, which cannot be mistaken for a fifth-exclusive constructor.
No extra source field, set conversion or event deduplication is used. -/
private theorem fifth_exclusive_length_from_original_producer
    {α : Type*} (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre : List α) (positive : Bool)
    (mass : ℝ) (remaining : List α) :
    ∀ fifth : FifthStoppedEvent α,
      FifthSixthStoppedEvent.fifthExclusive fifth ∈
        fifthSixthWithoutBoth R S h T pre positive mass remaining →
      fifth.selectedAfter.length = pre.length + 1 := by
  induction remaining with
  | nil =>
      intro fifth hmem
      simp [fifthSixthWithoutBoth] at hmem
  | cons p ps ih =>
      intro fifth hmem
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · have hsplit : FifthSixthStoppedEvent.fifthExclusive fifth ∈
              (((firstFifthEvents R S h T (p :: pre) (!positive)
                (mass * h p) ps).filter
                (fun inner => decide
                  (inner.kind ≠
                    P4AOriginalFull87FirstFifthStoppedEvents.FifthAdmissionClass.both))).map
                (FifthSixthStoppedEvent.sixthFromBoth (p :: pre))) ++
              fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hmem
          rcases List.mem_append.mp hsplit with hnow | htail
          · obtain ⟨inner, _, heq⟩ := List.mem_map.mp hnow
            cases heq
          · exact ih fifth htail
        · simp [fifthSixthWithoutBoth, hr, hs] at hmem
          rcases hmem with heq | htail
          · cases heq
            simp
          · exact ih fifth htail
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [fifthSixthWithoutBoth, hr, hs] at hmem
          rcases hmem with heq | htail
          · cases heq
            simp
          · exact ih fifth htail
        · have htail : FifthSixthStoppedEvent.fifthExclusive fifth ∈
              fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hmem
          exact ih fifth htail

/-- Original rank-four frontier membership supplies the ACTUAL fifth
event length, with multiplicity and unchanged occurrence source. -/
theorem actual_fifth_exclusive_length_five
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth
        delta n e q om N cap w L X F state) :
    fifth.selectedAfter.length = 5 := by
  have hfour : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hstep := fifth_exclusive_length_from_original_producer
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (P1Pair12RetainedSignedSource.attachedLeafTest
      N cap 1 w L
      (P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X F))
    state.selectedPrefix state.positive state.mass state.remaining
    fifth (by simpa only [actualFifthSixthWithoutBoth] using hfifth)
  omega

/-- The original complete sixth rough product inequality WITHOUT the
previous unproved rank-five parameter. -/
theorem actual_fifth_exclusive_sixth_rough_power
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth
        delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
    ((p :: fifth.selectedAfter).prod) ^ 5 ≤
      fifth.selectedAfter.prod ^ 6 := by
  exact actual_fifth_exclusive_sixth_modulus_power_bound
    delta n e q om N cap w z L X F
    state hstate fifth hfifth
    (actual_fifth_exclusive_length_five
      delta n e q om N cap w z L X F state hstate fifth hfifth)
    p hp

/-- Exact LARGE-FIFTH-PRODUCT necessity for an actual full-modulus
high-q candidate. The Rosser index a is not suppressed from a*b6.
A future signed estimate must retain the region stated here. -/
theorem actual_highq_needs_large_fifth_weight
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth
        delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (a : ℕ)
    (hhigh : X < a * (p :: fifth.selectedAfter).prod) :
    X ^ 5 < a ^ 5 * fifth.selectedAfter.prod ^ 6 := by
  have hrough := actual_fifth_exclusive_sixth_rough_power
    delta n e q om N cap w z L X F
    state hstate fifth hfifth p hp
  calc
    X ^ 5 < (a * (p :: fifth.selectedAfter).prod) ^ 5 := by
      gcongr <;> exact hhigh
    _ = a ^ 5 * ((p :: fifth.selectedAfter).prod) ^ 5 := by
      rw [mul_pow]
    _ ≤ a ^ 5 * fifth.selectedAfter.prod ^ 6 :=
      Nat.mul_le_mul_left _ hrough

/-- Complementary small-product elimination, for each original
(a,p) occurrence, with no assumption that all fifth prefixes are small. -/
theorem actual_small_fifth_weight_excludes_highq
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth
        delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (a : ℕ)
    (hsmall : a ^ 5 * fifth.selectedAfter.prod ^ 6 ≤ X ^ 5) :
    ¬ X < a * (p :: fifth.selectedAfter).prod := by
  intro hhigh
  have hlarge := actual_highq_needs_large_fifth_weight
    delta n e q om N cap w z L X F
    state hstate fifth hfifth p hp a hhigh
  omega

end
end ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
