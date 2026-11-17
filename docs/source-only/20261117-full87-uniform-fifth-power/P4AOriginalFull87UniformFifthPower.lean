import ImbalancedChen.P4AOriginalFull87FifthRankPowerTail
import ImbalancedChen.P4AOriginalFull87SixthOnlyEventInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A quantitative PARENT-level high-q exclusion for ACTUAL fifth-exclusive
occurrences. Earlier power filtering discarded individual Rosser indices
only when a^5*b5^6 <= X^5. Here the *original nonzero plus-beta support*
a < L pays for a uniform cutoff L^5*b5^6 <= X^5, independent of both
the Rosser index a and the sixth candidate prime p.

The conclusion is a nonzero-necessary LARGE FIFTH PARENT REGION:
  sixthPositiveContinuation != 0 -> X^5 < L^5 * b5^6.
It is not a bound on that remaining region, an error/reserve payment,
a uniform physical modulus level, or a new analytic input. In particular
no fifth-only mask is placed on sixthFromBoth.
-/

namespace ImbalancedChen.P4AOriginalFull87UniformFifthPower
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87SixthOnlyEventInvoice (sixthPositiveContinuation)
open P4AOriginalFull87FifthRankPowerTail
  (actual_highq_needs_large_fifth_weight)

/-- If the actual fifth parent satisfies the UNIFORM L-power bound,
then every original positive small-Rosser index at every genuine sixth
candidate has zero strict high-q test. This uses the original active
beta implication (a : R) < L, not a new source or a hypothetical sixth
Rosser gate. Equal endpoints are excluded exactly, not by rounding. -/
theorem actual_fifth_uniform_power_attached_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter)
    (hcut : L ^ 5 * (fifth.selectedAfter.prod : ℝ) ^ 6 ≤ (X : ℝ) ^ 5) :
    attachedLeafTest N cap 1 w L (highQTest X F)
      true (p :: fifth.selectedAfter) = 0 := by
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  change actualSmallRosserPlus N cap w L a *
    highQTest X F (a * (p :: fifth.selectedAfter).prod) = 0
  by_cases hb : actualSmallRosserPlus N cap w L a = 0
  · simp [hb]
  · have hlt : (a : ℝ) < L :=
      (actualSmallRosserPlus_active hb).2.1
    have ha5 : (a : ℝ) ^ 5 ≤ L ^ 5 := by
      gcongr
    have hprod :
        (a : ℝ) ^ 5 * (fifth.selectedAfter.prod : ℝ) ^ 6 ≤
          L ^ 5 * (fifth.selectedAfter.prod : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right ha5
        (pow_nonneg (Nat.cast_nonneg _) _)
    have hnot : ¬ X < a * (p :: fifth.selectedAfter).prod := by
      intro hhigh
      have hpower : X ^ 5 < a ^ 5 * fifth.selectedAfter.prod ^ 6 :=
        actual_highq_needs_large_fifth_weight
          delta n e q om N cap w z L X F
          state hstate fifth hfifth p hp a hhigh
      have hreal :
          (X : ℝ) ^ 5 <
          (a : ℝ) ^ 5 * (fifth.selectedAfter.prod : ℝ) ^ 6 := by
        exact_mod_cast hpower
      exact (not_lt_of_ge (hprod.trans hcut)) hreal
    simp [highQTest, hnot]

/-- All p occurrences on the original remainingAfter List vanish, for
either ORIGINAL policy or any other test R, when the real uniform
fifth-parent condition holds. No bound on p, re-sorting, or occurrence
deduplication is used. -/
theorem actual_fifth_uniform_power_continuation_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R : Bool → List ℕ → Bool)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state)
    (hcut : L ^ 5 * (fifth.selectedAfter.prod : ℝ) ^ 6 ≤ (X : ℝ) ^ 5) :
    sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w L (highQTest X F))
      fifth.selectedAfter fifth.massAfter fifth.remainingAfter = 0 := by
  unfold sixthPositiveContinuation
  have hmap :
      (fifth.remainingAfter.map (fun p =>
        if R true (p :: fifth.selectedAfter) = true then
          signedTreeCoefficient true fifth.massAfter *
            attachedLeafTest N cap 1 w L (highQTest X F)
              true (p :: fifth.selectedAfter)
        else 0)) =
      fifth.remainingAfter.map (fun _ => (0 : ℝ)) := by
    apply List.map_congr_left
    intro p hp
    have hz := actual_fifth_uniform_power_attached_zero
      delta n e q om N cap w z L X F
      state hstate fifth hfifth p hp hcut
    by_cases hR : R true (p :: fifth.selectedAfter) = true
    · simp [hR, hz]
    · simp [hR]
  rw [hmap]
  simp

/-- An actual nonzero fifth-exclusive sixth-positive contribution
strictly forces a quantitatively large FIFTH PARENT, independent of
the literal sixth-prime and Rosser-index occurrences. This is a
necessary region condition, not a numerical upper bound on its mass. -/
theorem actual_fifth_nonzero_continuation_forces_large_parent
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R : Bool → List ℕ → Bool)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X F state)
    (hnz : sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w L (highQTest X F))
      fifth.selectedAfter fifth.massAfter fifth.remainingAfter ≠ 0) :
    (X : ℝ) ^ 5 <
      L ^ 5 * (fifth.selectedAfter.prod : ℝ) ^ 6 := by
  by_contra hnot
  have hcut : L ^ 5 * (fifth.selectedAfter.prod : ℝ) ^ 6 ≤
      (X : ℝ) ^ 5 := le_of_not_gt hnot
  exact hnz (actual_fifth_uniform_power_continuation_zero
    delta n e q om N cap w z L X F R state hstate fifth hfifth hcut)

end
end ImbalancedChen.P4AOriginalFull87UniformFifthPower
