import ImbalancedChen.P2Saving16SignedCorrectionFamilies
import ImbalancedChen.P1Pair12RetainedSignedSource
import ImbalancedChen.FirstExitFrontierInvariants

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Expose the literal rank-four retained frontier of the very policy read by
the compiler, with the sign-sensitive beta attachment and the original
full-modulus test. This is not a geometric-corner identification. -/
namespace ImbalancedChen.P2Saving16ActualFourthFrontier
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2Saving16ActualCompilerDifference P2Saving16WeightedCompilerLedger
open P2Saving16SignedCorrectionFamilies P1Pair12RetainedSignedSource
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)

def stoppedBeforeFour (ret : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  stoppedTest 4 (oddFirstExitPolicy ret) (fun _ => 1)
    (attachedLeafTest N cap 1 w L G) [] true 1 (roughPrimeUniverse N cap w z)

/-- The list and every state retain their incoming sign, mass, prefix and
remaining prime carrier. No state is converted to an unweighted set. -/
def fourthFrontierSource (ret : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier 4 (oddFirstExitPolicy ret) (fun _ : ℕ => 1)
      [] true 1 (roughPrimeUniverse N cap w z)).map
    (fun s => signedTest (oddFirstExitPolicy ret) (fun _ => 1)
      (attachedLeafTest N cap 1 w L G)
      s.selectedPrefix s.positive s.mass s.remaining)).sum

/-- Every actual rank-four occurrence has four selected primes, the
original positive incoming sign, unit local mass, and its selected word
is a sublist of the original carrier in the original order. -/
theorem fourth_frontier_incoming_sign (ret : List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 4 (oddFirstExitPolicy ret) (fun _ : ℕ => 1)
      [] true 1 (roughPrimeUniverse N cap w z)) :
    s.selectedPrefix.length = 4 ∧ s.mass = 1 ∧
    signedTreeCoefficient s.positive s.mass = 1 ∧
    s.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z := by
  have hl := firstExitDepthFrontier_selected_length 4 (oddFirstExitPolicy ret)
    (fun _ : ℕ => (1 : ℝ)) [] (roughPrimeUniverse N cap w z) true 1 (by simp) s hs
  have hm : s.mass = 1 := by
    simpa using mem_firstExitDepthFrontier_mass_eq_selected_prod 4
      (oddFirstExitPolicy ret) (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z) s hs
  have hp := mem_firstExitDepthFrontier_positive_eq_evenListLength 4
    (oddFirstExitPolicy ret) (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z) s hs
  refine ⟨hl, hm, ?_, mem_firstExitDepthFrontier_selected_reverse_sublist 4
    (oddFirstExitPolicy ret) (fun _ : ℕ => (1 : ℝ)) (roughPrimeUniverse N cap w z) s hs⟩
  rw [hp, hm, signedTreeCoefficient_evenListLength_eq_negOnePow, hl]
  norm_num

/-- The full-Q raw attached coefficient is exactly the original retained
signed tree, with the same small beta pair and full-modulus G. -/
theorem raw_on_compiler_support_eq_signed_tree (ret : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ m ∈ support N cap w z, actualSmallRoughRho ret N cap w z L m * G m) =
      signedTest (oddFirstExitPolicy ret) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G) [] true 1 (roughPrimeUniverse N cap w z) := by
  have henlarge := sum_smallRoughRho_mul_eq_of_rough_enlargement
    (actualSmallRosserSupport N cap w) (rawSupport_subset_universe ret N cap w z)
    (raw ret N cap w z) (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)
    (fun d _ hnot => by rw [raw_value, if_neg hnot]) G
  change (∑ m ∈ support N cap w z,
    smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
      (raw ret N cap w z) (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) m * G m) =
    (∑ m ∈ actualSmallRoughModuli ret N cap w z,
      actualSmallRoughRho ret N cap w z L m * G m) at henlarge
  rw [raw_attachment_eq_actual ret N cap w z L] at henlarge
  have htree := physical_test_eq_signedTest (oddFirstExitPolicy ret)
    (oddFirstExitPolicy_even ret) N cap 1 w z L G
  have htree' :
      (∑ m ∈ actualSmallRoughModuli ret N cap w z,
        actualSmallRoughRho ret N cap w z L m * G m) =
      signedTest (oddFirstExitPolicy ret) (fun _ => 1)
        (attachedLeafTest N cap 1 w L G) [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only [oddFirstExitPolicy, Bool.false_or, one_mul] using htree
  exact henlarge.trans htree'

/-- Split the actual retained signed tree at rank four. All continuations
retain the complete terminal beta-weighted test. -/
theorem signed_tree_eq_stopped_add_fourth_frontier (ret : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    signedTest (oddFirstExitPolicy ret) (fun _ => 1)
      (attachedLeafTest N cap 1 w L G) [] true 1 (roughPrimeUniverse N cap w z) =
        stoppedBeforeFour ret N cap w z L G + fourthFrontierSource ret N cap w z L G := by
  have h := signedTest_splice_eq_stopped_add_frontier 4
    (oddFirstExitPolicy ret) (oddFirstExitPolicy ret) (fun _ : ℕ => 1)
    (attachedLeafTest N cap 1 w L G) [] (roughPrimeUniverse N cap w z) true 1
  rw [firstExitDepthSplicePolicy_self] at h
  exact h

/-- Exact compiler coefficient on its own support: the stopped raw part,
the actual signed fourth frontier, and both original rounding families.
This is an identity, not a difference of independently estimated bounds. -/
theorem compiler_on_actual_fourth_frontier (ret : List ℕ → Bool)
    (tag : ℕ → List Bool) (N cap : ℕ) (w z tau L : ℝ) (G : ℕ → ℝ) :
    (∑ m ∈ support N cap w z, rho ret tag N cap w z tau L m * G m) =
      stoppedBeforeFour ret N cap w z L G + fourthFrontierSource ret N cap w z L G +
        (positiveOuterSum ret tag N cap w z tau L G +
          negativeInnerSum ret tag N cap w z tau L G) := by
  have hc := actual_weighted_correction_sum ret tag N cap w z tau L G
  rw [correctionSum_eq_two_families] at hc
  simp only [sub_mul, Finset.sum_sub_distrib] at hc
  have hr := raw_on_compiler_support_eq_signed_tree ret N cap w z L G
  have hf := signed_tree_eq_stopped_add_fourth_frontier ret N cap w z L G
  linarith only [hc, hr, hf]

/-- Specialization to the existing ordered-eighth coefficient, literal Q,
one beta and the exact policy read by the signed compiler. -/
theorem r17_compiler_on_actual_fourth_frontier
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ) (N : ℕ) (G : ℕ → ℝ) :
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let L := (N : ℝ)^(nu*beta)
    let Q := moduli N w
    let f := keep r n e q a omega N
    (∑ m ∈ Q, coefficient r n e q a omega N tau L m * G m) =
      stoppedBeforeFour f N N w z L G + fourthFrontierSource f N N w z L G +
        (positiveOuterSum f (fun _ => []) N N w z tau L G +
          negativeInnerSum f (fun _ => []) N N w z tau L G) := by
  exact compiler_on_actual_fourth_frontier
    (keep r n e q a (nu * beta^2) N) (fun _ => []) N N
    ((N : ℝ)^(nu * beta^2)) (cutoff N) tau ((N : ℝ)^(nu*beta)) G

end
end ImbalancedChen.P2Saving16ActualFourthFrontier
