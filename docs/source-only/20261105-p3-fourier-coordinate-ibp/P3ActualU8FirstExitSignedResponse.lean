import ImbalancedChen.P3ActualU8FirstExitSupportDelta
import ImbalancedChen.P1OriginalHistoricalPhysicalCoefficient
import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Exact signed response of the ORIGINAL U8 labelled rank-three discrepancy
to differences between genuine first-exit retained supports.  The earlier
cardinality estimate discarded the Mobius sign and the entire small Rosser
response.  This source instead retains a signed sum over the two *oriented*
support differences, AFTER the complete physical modulus sum.  It assumes
neither cancellation nor a bound on these oriented sums.

The two compared policies use the same finite roughPrimeUniverse, the
same physical small/rough product carrier, the same sign-sensitive real
Rosser beta weights, the same actual complete U8 products and exact
coprime masses.  The other policy is NOT identified with the final global
causal compiler.  Smooth PP admissibility and all external (M) estimates
remain unproved.
-/

namespace ImbalancedChen.P3ActualU8FirstExitSignedResponse

noncomputable section
open scoped BigOperators
open Classical

/-- The response of a rough modulus to the original complete physical
modulus test.  The sign is the *fixed* Mobius sign of the rough modulus,
not a new choice depending on the test function or original prime label. -/
def signedRoughResponse (small : Finset ℕ)
    (betaMinus betaPlus F : ℕ → ℝ) (b : ℕ) : ℝ :=
  ∑ a ∈ small,
    signAttachedCoefficient (ArithmeticFunction.moebius b : ℝ)
      (betaMinus a) (betaPlus a) * F (a * b)

/-- Exact pair-to-physical finite Fubini for a real first-exit coefficient.
This is a SIGNED identity, including at an empty retained support.
The sole uses of the physical cutoff are the existing unique-factorization
hypotheses; there is no assertion about upper-sieve admissibility. -/
theorem firstExit_physical_signed_response
    (w : ℝ) (small rough : Finset ℕ)
    (hsmall : ∀ a ∈ small, SmallPrimeSupportedAt w a)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (carrier : List ℕ) (policy : Bool → List ℕ → Bool)
    (betaMinus betaPlus F : ℕ → ℝ) :
    (∑ q ∈ smallRoughModuli small rough,
      smallRoughRho small rough
        (fun b => (firstExitRetainedCoefficient policy carrier b : ℝ))
        betaMinus betaPlus q * F q) =
      ∑ b ∈ rough,
        if b ∈ firstExitRetainedModuli policy carrier then
          signedRoughResponse small betaMinus betaPlus F b else 0 := by
  rw [sum_smallRoughRho_mul hsmall hrough
    (fun b => (firstExitRetainedCoefficient policy carrier b : ℝ))
    betaMinus betaPlus F]
  simp only [smallRoughPairs, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : b ∈ firstExitRetainedModuli policy carrier
  · simp [signedRoughResponse, smallRoughPairCoefficient,
      firstExitRetainedCoefficient, h]
  · simp [signedRoughResponse, smallRoughPairCoefficient,
      firstExitRetainedCoefficient, signAttachedCoefficient, h]

/-- The exact *oriented* symmetric-difference formula.  Each nonzero
rough modulus has a fixed Mobius sign for BOTH policies.  Unlike an L1
or cardinality bound, this identity still allows the cancellation that
may be essential when the physical small level grows like N^epsilon. -/
theorem firstExit_physical_signed_support_difference
    (w : ℝ) (small rough : Finset ℕ)
    (hsmall : ∀ a ∈ small, SmallPrimeSupportedAt w a)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (carrier : List ℕ)
    (policy₁ policy₀ : Bool → List ℕ → Bool)
    (betaMinus betaPlus F : ℕ → ℝ) :
    let S₁ := firstExitRetainedModuli policy₁ carrier
    let S₀ := firstExitRetainedModuli policy₀ carrier
    (∑ q ∈ smallRoughModuli small rough,
      smallRoughRho small rough
        (fun b => (firstExitRetainedCoefficient policy₁ carrier b : ℝ))
        betaMinus betaPlus q * F q) -
    (∑ q ∈ smallRoughModuli small rough,
      smallRoughRho small rough
        (fun b => (firstExitRetainedCoefficient policy₀ carrier b : ℝ))
        betaMinus betaPlus q * F q) =
      (∑ b ∈ rough.filter (fun b => b ∈ S₁ ∧ b ∉ S₀),
        signedRoughResponse small betaMinus betaPlus F b) -
      (∑ b ∈ rough.filter (fun b => b ∈ S₀ ∧ b ∉ S₁),
        signedRoughResponse small betaMinus betaPlus F b) := by
  dsimp only
  rw [firstExit_physical_signed_response w small rough hsmall hrough
        carrier policy₁ betaMinus betaPlus F,
      firstExit_physical_signed_response w small rough hsmall hrough
        carrier policy₀ betaMinus betaPlus F]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h₁ : b ∈ firstExitRetainedModuli policy₁ carrier <;>
    by_cases h₀ : b ∈ firstExitRetainedModuli policy₀ carrier <;>
    simp [h₁, h₀]

/-- True original U8 sharp-K signed progression discrepancy per physical
modulus, with every ordered prime triple and its exact coprime mean. -/
def actualU8SignedKernel (N q : ℕ) : ℝ :=
  p5z_labelledCongruenceMass
    (P5U8SharpKSource.arithmeticTriples N)
    P5U8SharpKSource.product (fun _ => (1 : ℝ)) N q -
  p5z_labelledCoprimeMass
    (P5U8SharpKSource.arithmeticTriples N)
    P5U8SharpKSource.product (fun _ => (1 : ℝ)) q /
      (Nat.totient q : ℝ)

/-- EXACT original fifth-policy U8 signed PP perturbation, not a
hypothetical sparse-fibre relative estimate.  No absolute values are
inserted before either the physical modulus or the rough-support sum.
The result exposes the real arithmetic cancellation still to be paid. -/
theorem original_fifth_u8_signed_support_difference
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Fin 4 → Fin (m + 1)))
    (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (other : Bool → List ℕ → Bool) :
    let fifth := P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ)
    let carrier := roughPrimeUniverse N cap w z
    let small := actualSmallRosserSupport N cap w
    let Q := smallRoughModuli small rough
    let rhoOther := smallRoughRho small rough
      (fun b => (firstExitRetainedCoefficient other carrier b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    let rhoFifth := smallRoughRho small rough
      (fun b => (firstExitRetainedCoefficient fifth carrier b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    let Sother := firstExitRetainedModuli other carrier
    let Sfifth := firstExitRetainedModuli fifth carrier
    Part3.primeProductSignedError 3 N N Q rhoOther
        (P5U8SharpKSource.physicalWeight N) -
      Part3.primeProductSignedError 3 N N Q rhoFifth
        (P5U8SharpKSource.physicalWeight N) =
      (∑ b ∈ rough.filter (fun b => b ∈ Sother ∧ b ∉ Sfifth),
        signedRoughResponse small
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L)
          (actualU8SignedKernel N) b) -
      (∑ b ∈ rough.filter (fun b => b ∈ Sfifth ∧ b ∉ Sother),
        signedRoughResponse small
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L)
          (actualU8SignedKernel N) b) := by
  dsimp only
  rw [← P5U8SharpKSource.distribution_eq_physicalPP,
      ← P5U8SharpKSource.distribution_eq_physicalPP]
  change
    (∑ q ∈ smallRoughModuli (actualSmallRosserSupport N cap w) rough,
      smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fun b => (firstExitRetainedCoefficient other
          (roughPrimeUniverse N cap w z) b : ℝ))
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) q *
          actualU8SignedKernel N q) -
    (∑ q ∈ smallRoughModuli (actualSmallRosserSupport N cap w) rough,
      smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fun b => (firstExitRetainedCoefficient
          (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
            e chi m omega J4 cap4 J5 cap5 (N : ℝ))
          (roughPrimeUniverse N cap w z) b : ℝ))
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) q *
          actualU8SignedKernel N q) = _
  exact firstExit_physical_signed_support_difference w
    (actualSmallRosserSupport N cap w) rough
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    hrough (roughPrimeUniverse N cap w z) other
    (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ))
    (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)
    (actualU8SignedKernel N)

end
end ImbalancedChen.P3ActualU8FirstExitSignedResponse
