import ImbalancedChen.P2Saving16NegativeFiniteCore
import ImbalancedChen.P4AFull87UnionCompilerPayment
import ImbalancedChen.ActualPrimeFineWordMultiplicity

/-! The paid ALL/ANY value is a scalar for a whole label-and-tag fibre.
This statement does not assume that a rectangular fine-label fibre has
a single tag. The original factorial still applies with its actual,
permutation-invariant tagged weight inside the tuple sum. -/
namespace ImbalancedChen.P4AFull87TaggedAtomValue
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler

theorem fibre_scalar (ret : List ℕ → Bool) (tag : ℕ → List Bool) (N cap : ℕ)
    (w z tau : ℝ) {d e : ℕ} (hd : d ∈ «universe» N cap w z)
    (he : e ∈ «universe» N cap w z) (hj : label tag N tau d=label tag N tau e) :
    occupied ret tag N cap w z tau d=occupied ret tag N cap w z tau e := by
  simp [occupied,hd,he,hj]

/-- Both global rank signs and both occupied-fibre choices are kept.
The full rough squarefree test, target exclusion and rough endpoints
are inherited through the literal coefficient, also off the carrier. -/
theorem original_factorial (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    {N : ℕ} (hN : 1≤N) (cap : ℕ) (w z : ℝ) {tau : ℝ} (ht : 0≤tau)
    (J : List ℕ) (hJ : J.Pairwise (· ≥ ·)) (E : ℕ → ℝ) :
    (1 / (actualPrimeFineWordMultiplicity J:ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J,
          coefficient ret tag N cap w z tau ps.prod * E ps.prod) =
      ∑ d ∈ ((actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J).filter
        List.SortedGT).image List.prod, coefficient ret tag N cap w z tau d * E d := by
  have h := actualPrimeFineWord_original_scalar hN ht J hJ 1 1
    (fun d => occupied ret tag N cap w z tau d * E d)
  simpa only [literal_value,one_mul,mul_assoc] using h

/-- Value of the actual signed, beta-attached coefficient at every
physical integer, before taking a norm or restricting the support. -/
theorem actual_union_rho (delta : ℝ) (hd : 0<delta) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z tau L : ℝ) (m : ℕ) :
    let D := P4AOriginalNewFifthUnion.data e q om
    let ret := P4AFull87UnionCompilerPayment.keep delta n D N
    let tag := P4AFull87DataCompilerReads.tag delta hd n D N
    P4AUpperTaggedBetaAttachment.rho ret tag N cap w z tau L m =
      ∑ x ∈ smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z)
        with x.1*x.2=m,
        signAttachedCoefficient ((ArithmeticFunction.moebius x.2:ℝ)*occupied ret tag N cap w z tau x.2)
          (actualSmallRosserMinus N cap w L x.1) (actualSmallRosserPlus N cap w L x.1) := by
  dsimp only
  simp only [P4AUpperTaggedBetaAttachment.rho,smallRoughRho,smallRoughPairCoefficient,literal_value]

end
end ImbalancedChen.P4AFull87TaggedAtomValue
