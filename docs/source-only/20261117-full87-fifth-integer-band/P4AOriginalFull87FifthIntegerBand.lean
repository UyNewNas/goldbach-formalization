import ImbalancedChen.P4AOriginalFull87UniformFifthPower
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

NEW quantitative necessary support for the ORIGINAL fifth-exclusive
positive sixth continuation. The predecessor only had the real-valued
condition X^5 < L^5*b5^6, while the manuscript freezes L=N^epsilon,
epsilon<=1/500, X>=N^(3/5). Here we pay those exponent inequalities,
not merely rename the retained finite sum:

  nonzero actual sixth continuation => N^299 < b5^600.

This is the exact integer-power presentation of b5>N^(299/600).
It is a STRICT lower bound on the genuine fifth selected rough product.
The original selected history, remaining prime occurrences, positive
small Rosser indices and both policies are not replaced or masked.
This is NOT a bound on the total signed mass of the surviving band,
NOT a physical N^theta support licence and NOT a numerical H_N saving.
-/

namespace ImbalancedChen.P4AOriginalFull87FifthIntegerBand
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87SixthOnlyEventInvoice (sixthPositiveContinuation)
open P4AOriginalFull87UniformFifthPower
  (actual_fifth_nonzero_continuation_forces_large_parent)
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- Frozen exponent arithmetic, including BOTH original endpoint
conventions. Do not infer the bound without N>1, epsilon<=1/500
and X>=N^(3/5). It records an exact strict integer-power cutoff.
The inequality is independent of the sixth prime because the
ordered fifth-power estimate was already discharged upstream. -/
private theorem strict_integer_band_of_uniform_fifth_power
    (N X b : ℕ) (epsilon : ℝ)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (hlarge : (X : ℝ) ^ 5 <
      ((N : ℝ) ^ epsilon) ^ 5 * (b : ℝ) ^ 6) :
    (N : ℝ) ^ 299 < (b : ℝ) ^ 600 := by
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_of_lt hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hX5 : (N : ℝ) ^ 3 ≤ (X : ℝ) ^ 5 := by
    have hp : ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 5 = (N : ℝ) ^ 3 := by
      calc
        _ = (N : ℝ) ^ ((3 / 5 : ℝ) * (5 : ℝ)) :=
          (Real.rpow_mul_natCast hN0 (3 / 5 : ℝ) 5).symm
        _ = (N : ℝ) ^ (3 : ℝ) := by norm_num
        _ = (N : ℝ) ^ 3 := by norm_num
    rw [← hp]
    gcongr <;> assumption
  have hL500 : ((N : ℝ) ^ epsilon) ^ 500 ≤ (N : ℝ) := by
    calc
      _ = (N : ℝ) ^ (epsilon * (500 : ℝ)) :=
        (Real.rpow_mul_natCast hN0 epsilon 500).symm
      _ ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [heps])
      _ = (N : ℝ) := by simp
  have hlarge100 :
      ((X : ℝ) ^ 5) ^ 100 <
        (((N : ℝ) ^ epsilon) ^ 5 * (b : ℝ) ^ 6) ^ 100 := by
    gcongr <;> assumption
  have hN300 :
      (N : ℝ) ^ 300 <
        ((N : ℝ) ^ epsilon) ^ 500 * (b : ℝ) ^ 600 := by
    calc
      _ = ((N : ℝ) ^ 3) ^ 100 := by ring
      _ ≤ ((X : ℝ) ^ 5) ^ 100 := by gcongr <;> assumption
      _ < (((N : ℝ) ^ epsilon) ^ 5 * (b : ℝ) ^ 6) ^ 100 :=
        hlarge100
      _ = ((N : ℝ) ^ epsilon) ^ 500 * (b : ℝ) ^ 600 := by ring
  have hN300' :
      (N : ℝ) ^ 300 < (N : ℝ) * (b : ℝ) ^ 600 :=
    lt_of_lt_of_le hN300
      (mul_le_mul_of_nonneg_right hL500
        (pow_nonneg (Nat.cast_nonneg b) 600))
  have hpow : (N : ℝ) ^ 300 = (N : ℝ) * (N : ℝ) ^ 299 := by ring
  rw [hpow] at hN300'
  exact (mul_lt_mul_left hNpos).mp hN300'

/-- Original event-level support statement. It uses the SAME fifth
exclusive occurrence from the actual fourth-rank parent, not a
surrogate geometric archive or another accepted fifth branch. The
selected product remains the literal b5 with its original history.

No signed saving, fifth-tail measure, or sixthFromBoth assumption
is imported in this theorem. -/
theorem actual_fifth_exclusive_nonzero_requires_integer_band
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (R : Bool → List ℕ → Bool)
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w
        ((N : ℝ) ^ epsilon) X F state)
    (hnz : sixthPositiveContinuation R
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F))
      fifth.selectedAfter fifth.massAfter fifth.remainingAfter ≠ 0) :
    (N : ℝ) ^ 299 <
      (fifth.selectedAfter.prod : ℝ) ^ 600 := by
  have hlarge :
      (X : ℝ) ^ 5 <
        ((N : ℝ) ^ epsilon) ^ 5 *
          (fifth.selectedAfter.prod : ℝ) ^ 6 :=
    actual_fifth_nonzero_continuation_forces_large_parent
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X F R
      state hstate fifth hfifth hnz
  exact strict_integer_band_of_uniform_fifth_power
    N X fifth.selectedAfter.prod epsilon hN heps hX hlarge

end
end ImbalancedChen.P4AOriginalFull87FifthIntegerBand
