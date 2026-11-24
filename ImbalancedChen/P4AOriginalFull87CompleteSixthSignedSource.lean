import ImbalancedChen.P4AOriginalFull87CompleteSixthDispatch
import ImbalancedChen.P4AOriginalCompleteSixthSignedSource

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

An exact finite signed-source identity for the concrete full87 endpoint
policy. Its predecessor is the COMPLETE sixth policy, not the held eleven
cells. The source is independently defined on the predecessor's actual
rank-eight occurrence frontier. Full modulus tests, incoming signs/mass,
remaining carriers, list multiplicities and arbitrary presieve w survive.
No inequality, prime mean, positive-presieve saving or reserve is inferred.
-/
namespace ImbalancedChen.P4AOriginalFull87CompleteSixthSignedSource
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87CompleteSixthDispatch
open P5OriginalCommonRefinedSource P1Pair12RetainedSignedSource

/-- The actual physical finite sum for the constructed full87 policy. -/
def physical (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ d ∈ actualSmallRoughModuli (policy e q omega (N : ℝ) false) N cap w z,
    actualSmallRoughRho (policy e q omega (N : ℝ) false) N cap w z L d * G d

/-- The actual predecessor, explicitly the complete sixth finite sum. -/
def sixthPhysical (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ d ∈ actualSmallRoughModuli
      (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega (N : ℝ) false)
      N cap w z,
    actualSmallRoughRho
      (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega (N : ℝ) false)
      N cap w z L d * G d

/-- An actual occurrence-frontier source, NOT the desired final physical
estimate defined by subtraction. Both continuation tests retain all of
the predecessor state's sign, mass, prefix and remaining carrier. -/
def full87SourceChange (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier 8
    (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega (N : ℝ))
    (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z)).map (fun state =>
      signedTest (continuation e q omega (N : ℝ))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining -
      signedTest
        (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega (N : ℝ))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining)).sum

/-- Exact new-minus-actual-predecessor identity, for every full-q test G.
No owner/support/current-parent-bound premise is required for this finite
identity; such premises are still needed for later analytic estimates. -/
theorem physical_full87_sub_complete_sixth_eq_source
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical e q omega N cap w z L G - sixthPhysical e q omega N cap w z L G =
      full87SourceChange e q omega N cap w z L G := by
  unfold physical sixthPhysical
  have hnew := physical_test_eq_signedTest (policy e q omega (N : ℝ))
    (policy_even e q omega (N : ℝ)) N cap 1 w z L G
  have hold := physical_test_eq_signedTest
    (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega (N : ℝ))
    (P4AOriginalCompleteSixthChronology.current_policy_even e q omega (N : ℝ))
    N cap 1 w z L G
  simp only [one_mul] at hnew hold
  rw [hnew, hold, policy_eq_splice]
  exact signedTest_splice_sub_eq_frontier 8 _ _ (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] (roughPrimeUniverse N cap w z) true 1

/-- Telescoping the two ACTUAL chronological changes. The fifth tree is
S09's same original fourth/fifth instance. This does not transport old
held-parent saving numerals to the new tree or introduce a second reserve. -/
theorem physical_full87_sub_fifth_eq_sources
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical e q omega N cap w z L G -
      source (P4AOriginalCompleteSixthChronology.data e q omega) .fifth N cap w z L G =
        full87SourceChange e q omega N cap w z L G +
          P4AOriginalCompleteSixthSignedSource.completeSixthSourceChange
            e q omega N cap w z L G := by
  have h8 := physical_full87_sub_complete_sixth_eq_source e q omega N cap w z L G
  have h6 : sixthPhysical e q omega N cap w z L G -
      source (P4AOriginalCompleteSixthChronology.data e q omega) .fifth N cap w z L G =
        P4AOriginalCompleteSixthSignedSource.completeSixthSourceChange
          e q omega N cap w z L G :=
    P4AOriginalCompleteSixthSignedSource.physical_complete_sixth_sub_fifth_eq_source
      e q omega N cap w z L G
  linarith

end
end ImbalancedChen.P4AOriginalFull87CompleteSixthSignedSource
