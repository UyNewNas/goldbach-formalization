import ImbalancedChen.P1OriginalHistoricalRoughOwnerPartition
import ImbalancedChen.P4AUpperTaggedFirstPrefixDisagreement

/-!
The original historical rough mask reads the full canonical prime word.
Reuse the existing raw-support dictionary; do not substitute the O compiler's
smoothed coefficient or its small-prime attachment. No affine cover or signed
distribution bound is asserted here.
-/
namespace ImbalancedChen.P1OriginalHistoricalCanonicalTrace
noncomputable section
open Classical
open scoped BigOperators
open P1OriginalHistoricalCoefficientDictionary
  (commonRoughSupport roughMaskDelta attachedMobius)
open P1OriginalHistoricalRoughOwnerPartition (fibre fibre_mask)
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho)
open P1Full87HistoricalMiddleSmoothing (remainingModuli)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)

/-- Both tests are the original complete sequential selections, on the SAME
canonical word of b. No rough-mask or factorization equation is a premise. -/
theorem rough_mask_eq_canonical_trace_difference
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (b : ℕ)
    (hb : b ∈ commonRoughSupport old fresh N cap w z) :
    roughMaskDelta old fresh N cap w z b =
      (if FirstExitValidSelection (oddFirstExitPolicy fresh) [] true
        b.primeFactorsList.reverse then (1 : ℝ) else 0) -
      (if FirstExitValidSelection (oddFirstExitPolicy old) [] true
        b.primeFactorsList.reverse then (1 : ℝ) else 0) := by
  have hu : b ∈ P4AUpperTaggedParityCompiler.«universe» N cap w z := by
    rcases Finset.mem_union.mp hb with hf | ho
    · exact P4AUpperTaggedParityCompiler.rawSupport_subset_universe fresh N cap w z hf
    · exact P4AUpperTaggedParityCompiler.rawSupport_subset_universe old N cap w z ho
  have ho : b ∈ fixedRoughSupport old N cap w z ↔
      FirstExitValidSelection (oddFirstExitPolicy old) [] true b.primeFactorsList.reverse := by
    simpa only [P4AUpperTaggedParityCompiler.rawSupport, hu, true_and] using
      raw_support_iff_canonical_validSelection old N cap w z b
  have hf : b ∈ fixedRoughSupport fresh N cap w z ↔
      FirstExitValidSelection (oddFirstExitPolicy fresh) [] true b.primeFactorsList.reverse := by
    simpa only [P4AUpperTaggedParityCompiler.rawSupport, hu, true_and] using
      raw_support_iff_canonical_validSelection fresh N cap w z b
  simp only [roughMaskDelta, hf, ho]

/-- The original arbitrary complex test, with only the retention masks
rewritten. attachedMobius still chooses beta from original rough Mobius,
and the original remaining filter stays on the COMPLETE a*b. -/
theorem remaining_test_eq_canonical_trace_pair_sum
    (B : ℝ) (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℂ) :
    (∑ q ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z),
      (trueDDeltaRho old fresh N cap w z L q : ℂ) * G q) =
    ∑ a ∈ actualSmallRosserSupport N cap w,
      ∑ b ∈ commonRoughSupport old fresh N cap w z,
        (((if FirstExitValidSelection (oddFirstExitPolicy fresh) [] true
            b.primeFactorsList.reverse then (1 : ℝ) else 0) -
          (if FirstExitValidSelection (oddFirstExitPolicy old) [] true
            b.primeFactorsList.reverse then (1 : ℝ) else 0) : ℝ) : ℂ) *
        (attachedMobius N cap w L a b : ℂ) *
          (if a * b ∈ remainingModuli B N (trueDDeltaSupport old fresh N cap w z)
            then G (a * b) else 0) := by
  rw [P1OriginalHistoricalCoefficientDictionary.remaining_trueDDeltaRho_test_eq_pair_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b hb
  rw [rough_mask_eq_canonical_trace_difference old fresh N cap w z b hb]

/-- The full-word difference is the SAME fixed original owner sign.
It is not used to reselect the original small Rosser member. -/
theorem fibre_canonical_trace_sign
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ) (b : ℕ)
    (hb : b ∈ fibre old fresh N cap w z state) :
    (if FirstExitValidSelection (oddFirstExitPolicy fresh) [] true
        b.primeFactorsList.reverse then (1 : ℝ) else 0) -
      (if FirstExitValidSelection (oddFirstExitPolicy old) [] true
        b.primeFactorsList.reverse then (1 : ℝ) else 0) =
      (if fresh state.selectedPrefix = true then (1 : ℝ) else -1) := by
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
  rw [← rough_mask_eq_canonical_trace_difference old fresh N cap w z b hc]
  exact fibre_mask old fresh N cap w z state b hb

end
end ImbalancedChen.P1OriginalHistoricalCanonicalTrace
