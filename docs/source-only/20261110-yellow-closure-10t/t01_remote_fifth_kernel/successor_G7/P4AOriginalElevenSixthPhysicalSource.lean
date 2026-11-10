import ImbalancedChen.P4AOriginalElevenSixthStage
import ImbalancedChen.P5OriginalCommonRefinedSource

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual G4→G7 sixth stage is a difference of physical sieve sources
on the SAME fifth-policy frontier. Incoming signs, masses, remaining
carriers, complete-modulus tests and attached leaf weights are retained.
This equality does not presume compact occurrence admission or a positive
numerical saving; those must be proved on the original G7 physical cells.
-/
namespace ImbalancedChen.P4AOriginalElevenSixthPhysicalSource
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87DataPolicy (fifthPolicy)

def physical (R : Bool → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
    actualSmallRoughRho (R false) N cap w z L d * G d

def change (n : ℕ) (d : OriginalData) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier 6 (fifthPolicy n d (N:ℝ)) (fun _ => 1) [] true 1
    (roughPrimeUniverse N cap w z)).map (fun state =>
      signedTest (frozenParityRosserPolicy false 6
        (fun pre => (N:ℝ)^P4AOriginalElevenSixthStage.level n d (N:ℝ) pre))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining -
      signedTest (frozenParityRosserPolicy false 6
        (fun pre => (N:ℝ)^P4AOriginalSavedSixthStage.level n d (N:ℝ) pre))
        (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining)).sum

theorem physical_sub_eq_signed_source (n : ℕ) (d : OriginalData) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    physical (P4AOriginalElevenSixthStage.policy n d (N:ℝ)) N cap w z L G -
      physical (P4AOriginalSavedSixthStage.policy n d (N:ℝ)) N cap w z L G =
        change n d N cap w z L G := by
  have hnew := physical_test_eq_signedTest (P4AOriginalElevenSixthStage.policy n d (N:ℝ))
    (P4AOriginalElevenSixthStage.even n d (N:ℝ)) N cap 1 w z L G
  have hold := physical_test_eq_signedTest (P4AOriginalSavedSixthStage.policy n d (N:ℝ))
    (P4AOriginalSavedSixthStage.even n d (N:ℝ)) N cap 1 w z L G
  simp only [one_mul] at hnew hold
  unfold physical
  rw [hnew,hold]
  unfold P4AOriginalElevenSixthStage.policy P4AOriginalSavedSixthStage.policy
  rw [signedTest_splice_eq_stopped_add_frontier,signedTest_splice_eq_stopped_add_frontier,
    add_sub_add_left_eq_sub]
  unfold change
  generalize firstExitDepthFrontier 6 (fifthPolicy n d (N:ℝ)) (fun _ => (1:ℝ)) [] true 1
    (roughPrimeUniverse N cap w z) = states
  induction states with
  | nil => simp
  | cons state states ih => simp only [List.map_cons,List.sum_cons]; linarith only [ih]

/-- This specializes the physical identity to the actual old+new fifth
union. The early activation parameter a is retained separately from the
late roughness cutoff z and attached-test endpoint L. -/
theorem original_union_physical_sub_eq_signed_source (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (P4AOriginalElevenSixthStage.policy n (P4AOriginalNewFifthUnion.data e q a) (N:ℝ))
      N cap w z L G -
    physical (P4AOriginalSavedSixthStage.policy n (P4AOriginalNewFifthUnion.data e q a) (N:ℝ))
      N cap w z L G =
    change n (P4AOriginalNewFifthUnion.data e q a) N cap w z L G :=
  physical_sub_eq_signed_source n (P4AOriginalNewFifthUnion.data e q a) N cap w z L G

end
end ImbalancedChen.P4AOriginalElevenSixthPhysicalSource
