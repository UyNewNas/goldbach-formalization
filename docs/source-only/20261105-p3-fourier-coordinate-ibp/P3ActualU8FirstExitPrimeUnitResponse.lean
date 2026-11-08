import ImbalancedChen.P3ActualU8FirstExitSignedResponse
import ImbalancedChen.P3ActualU8UnitQuotientOffshift
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Actual original U8 sharp-K source has BOTH labelled prime-quotient triples
(with the inclusive terminal p₂=q wall) and the separately recorded
quotient-one PAIRS. The previous signed first-exit response covered only
the triples. This file combines both sources with the IDENTICAL physical
Q and signed small/rough rho, before any absolute value is taken.

The source-specific unit pair distribution is included as an exact
signed-discrepancy identity, NOT as a new assumption that it meets the
admissible smooth PP class. The unit source can instead be paid by the
existing independent direct-count power saving. No global final causal
compiler is identified with the comparison first-exit policy.
-/ 

namespace ImbalancedChen.P3ActualU8FirstExitPrimeUnitResponse

noncomputable section
open scoped BigOperators
open Classical
open P3ActualU8FirstExitSignedResponse
open P3ActualU8UnitQuotientOffshift

/-- Original quotient-ONE pairs, with their own labelled multiplicity,
complete physical pair product and exact coprime mean. -/
def actualU8UnitSignedKernel (N q : ℕ) : ℝ :=
  p5z_labelledCongruenceMass
    (currentChenUpsilon8UnitFibres N)
    unitPairProduct (fun _ => (1 : ℝ)) N q -
  p5z_labelledCoprimeMass
    (currentChenUpsilon8UnitFibres N)
    unitPairProduct (fun _ => (1 : ℝ)) q /
      (Nat.totient q : ℝ)

/-- Sum of the two ACTUAL different U8 source kernels.
This is not a single artificial rank-three source: the unit pairs
retain their physical rank two and their original labels. -/
def actualU8PrimeUnitSignedKernel (N q : ℕ) : ℝ :=
  actualU8SignedKernel N q + actualU8UnitSignedKernel N q

/-- Actual full labelled U8 arithmetic distribution, with one physical
rho. The original triples and quotient-one pairs remain separate sums
on the left, but combine into one signed modulus sum on the right. -/
theorem actual_u8_prime_unit_same_rho_signed_kernel
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N Q rho
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N Q rho =
      ∑ q ∈ Q, rho q * actualU8PrimeUnitSignedKernel N q := by
  rw [← P5U8SharpKSource.distribution_eq_physicalPP]
  change (∑ q ∈ Q, rho q * actualU8SignedKernel N q) +
      (∑ q ∈ Q, rho q * actualU8UnitSignedKernel N q) =
      ∑ q ∈ Q, rho q * actualU8PrimeUnitSignedKernel N q
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  unfold actualU8PrimeUnitSignedKernel
  ring

/-- The signed rough-modulus response decomposes into the original
rank-three and quotient-one pair responses. No triangle inequality,
pointwise fibre relative bound or arithmetic cancellation is assumed. -/
theorem prime_unit_signedRoughResponse_split
    (small : Finset ℕ) (betaMinus betaPlus : ℕ → ℝ)
    (N b : ℕ) :
    signedRoughResponse small betaMinus betaPlus
        (actualU8PrimeUnitSignedKernel N) b =
      signedRoughResponse small betaMinus betaPlus
        (actualU8SignedKernel N) b +
      signedRoughResponse small betaMinus betaPlus
        (actualU8UnitSignedKernel N) b := by
  unfold signedRoughResponse actualU8PrimeUnitSignedKernel
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

/-- The literal original fifth-capped first-exit policy versus any
second first-exit policy on the SAME roughPrimeUniverse. This is the
FULL U8 prime-plus-unit signed PP response, preserving each actual
rank, repeated terminal-prime label, small Rosser sign switch,
original physical product and exact primitive-coprime mean.

It makes no assertion that the other policy is the full global causal
compiler, nor that either signed oriented support sum is small. -/
theorem original_fifth_u8_prime_unit_signed_support_difference
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
    (Part3.primeProductSignedError 3 N N Q rhoOther
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N Q rhoOther) -
    (Part3.primeProductSignedError 3 N N Q rhoFifth
        (P5U8SharpKSource.physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N Q rhoFifth) =
      (∑ b ∈ rough.filter (fun b => b ∈ Sother ∧ b ∉ Sfifth),
        signedRoughResponse small
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L)
          (actualU8PrimeUnitSignedKernel N) b) -
      (∑ b ∈ rough.filter (fun b => b ∈ Sfifth ∧ b ∉ Sother),
        signedRoughResponse small
          (actualSmallRosserMinus N cap w L)
          (actualSmallRosserPlus N cap w L)
          (actualU8PrimeUnitSignedKernel N) b) := by
  dsimp only
  rw [actual_u8_prime_unit_same_rho_signed_kernel,
      actual_u8_prime_unit_same_rho_signed_kernel]
  change
    (∑ q ∈ smallRoughModuli (actualSmallRosserSupport N cap w) rough,
      smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fun b => (firstExitRetainedCoefficient other
          (roughPrimeUniverse N cap w z) b : ℝ))
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) q *
          actualU8PrimeUnitSignedKernel N q) -
    (∑ q ∈ smallRoughModuli (actualSmallRosserSupport N cap w) rough,
      smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fun b => (firstExitRetainedCoefficient
          (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
            e chi m omega J4 cap4 J5 cap5 (N : ℝ))
          (roughPrimeUniverse N cap w z) b : ℝ))
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) q *
          actualU8PrimeUnitSignedKernel N q) = _
  exact firstExit_physical_signed_support_difference w
    (actualSmallRosserSupport N cap w) rough
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    hrough (roughPrimeUniverse N cap w z) other
    (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ))
    (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)
    (actualU8PrimeUnitSignedKernel N)

end
end ImbalancedChen.P3ActualU8FirstExitPrimeUnitResponse
