import ImbalancedChen.P4AOriginalFull87CompleteSixthBound

/-! SOURCE ONLY / UNCOMPILED. The complete actual sixth endpoint producer
has a source at the actual retained sixth frontier of its ORIGINAL fifth
predecessor. This keeps the complete modulus test, incoming sign/mass and
remaining carrier; it is not a source defined by subtracting the target.
No raw or positive-presieve numerical estimate is inferred. -/
namespace ImbalancedChen.P4AOriginalCompleteSixthSignedSource
noncomputable section
open scoped Classical BigOperators
open P4AOriginalCompleteSixthChronology
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSource
open P1Pair12RetainedSignedSource

def completeSixthSourceChange (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier 6 (policy5 (data e q omega) (N : ℝ))
    (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z)).map (fun state =>
      signedTest
        (frozenParityRosserPolicy false 6
          (fun pre => (N : ℝ) ^ currentSixthExponent e q omega (N : ℝ) pre))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining -
      signedTest (policy5 (data e q omega) (N : ℝ))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining)).sum

/-- New complete-sixth minus the actual post-fifth tree, never minus an
obsolete fourth-only or unmodified third tree. Both presieves are allowed. -/
theorem physical_complete_sixth_sub_fifth_eq_source
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ actualSmallRoughModuli (currentSixthPolicy e q omega (N : ℝ) false) N cap w z,
      actualSmallRoughRho (currentSixthPolicy e q omega (N : ℝ) false) N cap w z L d * G d) -
      source (data e q omega) .fifth N cap w z L G =
        completeSixthSourceChange e q omega N cap w z L G := by
  have hp := physical_test_eq_signedTest (currentSixthPolicy e q omega (N : ℝ))
    (current_policy_even e q omega (N : ℝ)) N cap 1 w z L G
  simp only [one_mul] at hp
  rw [hp, source_eq_actual_root]
  change signedTest (firstExitDepthSplicePolicy 6 (policy5 (data e q omega) (N : ℝ))
      (frozenParityRosserPolicy false 6
        (fun pre => (N : ℝ)^currentSixthExponent e q omega (N : ℝ) pre)))
      (fun _ => 1) (attachedLeafTest N cap 1 w L G) [] true 1
      (roughPrimeUniverse N cap w z) -
    signedTest (policy5 (data e q omega) (N : ℝ))
      (fun _ => 1) (attachedLeafTest N cap 1 w L G) [] true 1
      (roughPrimeUniverse N cap w z) = _
  exact signedTest_splice_sub_eq_frontier 6 _ _ (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] (roughPrimeUniverse N cap w z) true 1

end
end ImbalancedChen.P4AOriginalCompleteSixthSignedSource
