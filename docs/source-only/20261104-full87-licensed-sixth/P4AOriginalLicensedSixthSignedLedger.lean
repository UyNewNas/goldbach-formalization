import ImbalancedChen.P4AOriginalFull87LicensedSixthRealization
import ImbalancedChen.P4AOriginalFull87CompleteSixthSignedSource

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Exact finite physical accounting for the NEW licensed-filter tree.
The sixth source uses the unchanged finite fifth occurrence frontier.
The eighth source uses the NEW sixth occurrence frontier, not the old one.
Full-q beta attachment, signs, incoming mass and list multiplicity remain.
This is an equality only: neither a numerical saving nor a reserve is paid.
-/
namespace ImbalancedChen.P4AOriginalLicensedSixthSignedLedger
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource P5OriginalCommonRefinedSource
open P4AOriginalFull87LicensedSixthPolicy

/-- An actual finite physical sum, with the same arbitrary full-q test. -/
def physical (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
    actualSmallRoughRho (P false) N cap w z L d * G d

/-- Independently defined occurrence-frontier source. The continuation is
compared with its actual predecessor on each SAME state and remaining list. -/
def frontierChange (k : ℕ) (P C : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier k P (fun _ => 1) [] true 1
    (roughPrimeUniverse N cap w z)).map (fun state =>
      signedTest C (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining -
      signedTest P (fun _ => 1) (attachedLeafTest N cap 1 w L G)
        state.selectedPrefix state.positive state.mass state.remaining)).sum

theorem physical_splice_sub_eq_frontier (k : ℕ)
    (P C : Bool → List ℕ → Bool)
    (hP : ∀ pre, P true pre = true)
    (hC : ∀ pre, C true pre = true)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (firstExitDepthSplicePolicy k P C) N cap w z L G -
      physical P N cap w z L G = frontierChange k P C N cap w z L G := by
  have hnew := physical_test_eq_signedTest (firstExitDepthSplicePolicy k P C)
    (UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained k P C hP hC)
    N cap 1 w z L G
  have hold := physical_test_eq_signedTest P hP N cap 1 w z L G
  simp only [one_mul] at hnew hold
  unfold physical
  rw [hnew,hold]
  exact signedTest_splice_sub_eq_frontier k P C (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] (roughPrimeUniverse N cap w z) true 1

/-- The cap filter's actual sixth increment; no raw/current gain is
substituted, and no absolute-value monotonicity is inferred. -/
def sixthChange (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  frontierChange 6 (P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q om (N : ℝ))
    (frozenParityRosserPolicy false 6
      (fun pre => (N : ℝ) ^ level6Exponent n e q om (N : ℝ) pre)) N cap w z L G

/-- The eighth source must be rebuilt on the new predecessor frontier. -/
def eighthChange (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  frontierChange 8 (sixthPolicy n e q om (N : ℝ))
    (eighthContinuation delta n e q om (N : ℝ)) N cap w z L G

theorem sixth_physical_change (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L G -
      physical (P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q om (N : ℝ))
        N cap w z L G = sixthChange n e q om N cap w z L G :=
  physical_splice_sub_eq_frontier 6 _ _
    (P4AOriginalFull87FiniteParentPolicy.fifth_even n e q om (N : ℝ))
    (fun pre => frozenParityRosserPolicy_upper_even 6 _ pre) N cap w z L G

theorem eighth_physical_change (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (policy delta n e q om (N : ℝ)) N cap w z L G -
      physical (sixthPolicy n e q om (N : ℝ)) N cap w z L G =
        eighthChange delta n e q om N cap w z L G := by
  apply physical_splice_sub_eq_frontier 8 _ _ (sixth_even n e q om (N : ℝ))
  intro pre
  unfold eighthContinuation
  cases P4AOriginalFull87FiniteEighthPolicy.selectedCap delta n (N : ℝ) pre
  · exact sixth_even n e q om (N : ℝ) pre
  · simp [ordinaryParityRosserPolicy,oddFirstExitPolicy]

/-- Exact two-stage ledger. In particular, changing the sixth cap does
not entitle one to reuse an archived eighth gain on the old frontier. -/
theorem full_physical_sub_fifth (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (policy delta n e q om (N : ℝ)) N cap w z L G -
      physical (P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q om (N : ℝ))
        N cap w z L G =
      eighthChange delta n e q om N cap w z L G + sixthChange n e q om N cap w z L G := by
  have h6 := sixth_physical_change n e q om N cap w z L G
  have h8 := eighth_physical_change delta n e q om N cap w z L G
  linarith

end
end ImbalancedChen.P4AOriginalLicensedSixthSignedLedger
