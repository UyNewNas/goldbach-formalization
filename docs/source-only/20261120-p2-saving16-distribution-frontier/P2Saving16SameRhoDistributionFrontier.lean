import ImbalancedChen.P2Saving16SameBetaPositiveLicense
import ImbalancedChen.P2Saving16ActualFourthTuples
import ImbalancedChen.P2Saving16NegativeInnerFourthAncestor
import ImbalancedChen.FiniteUpperCarrierCore

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Expose the exact signed real half-product distribution error on the same
compiler Q and rho as the actual ordered-fourth source. No PP estimate or
geometric-corner identification is asserted. -/
namespace ImbalancedChen.P2Saving16SameRhoDistributionFrontier
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2Saving16SignedCorrectionFamilies P2Saving16ActualFourthFrontier
open P2Saving16ActualFourthTuples P2Saving16SameBetaPositiveLicense
open P2Saving16NegativeInnerFourthAncestor P2CanonicalWallFullResidualPayment
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)

/-- Exact signed primitive-residue discrepancy for the actual real
half-product source at its original full modulus. -/
def realHalfProductDiscrepancy (b : ℝ) (N : ℕ) (T : ℝ) (m : ℕ) : ℝ :=
  realHalfProductCongruenceMass b N T m -
    realHalfProductCoprimeMass b N T m / (Nat.totient m : ℝ)

/-- The literal signed error reads the same coefficient and full-modulus
discrepancy; no absolute values or independent coefficients are inserted. -/
theorem actual_error_is_same_Q_discrepancy_sum
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (N : ℕ) (b T : ℝ) :
    let omega := nu*beta^2
    let w := (N : ℝ)^omega
    let L := (N : ℝ)^(nu*beta)
    realPhysicalDistributionError b N T (moduli N w)
      (coefficient r n e q a omega N tau L) =
    ∑ m ∈ moduli N w, coefficient r n e q a omega N tau L m *
      realHalfProductDiscrepancy b N T m := by
  rfl

/-- Exact allocation of the actual PP consumer: before-four terminal
part, the original admitted ordered-fourth signed continuations, and
both existing compiler correction families, all with the same b,N,T. -/
theorem r17_distribution_error_on_actual_fourths
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (N : ℕ) (b T : ℝ) :
    let omega := nu*beta^2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let L := (N : ℝ)^(nu*beta)
    let Q := moduli N w
    let rho := coefficient r n e q a omega N tau L
    let f := keep r n e q a omega N
    let G := realHalfProductDiscrepancy b N T
    realPhysicalDistributionError b N T Q rho =
      stoppedBeforeFour f N N w z L G +
        (∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z),
          fourthTupleTerm f N N w z L G p) +
        (positiveOuterSum f (fun _ => []) N N w z tau L G +
          negativeInnerSum f (fun _ => []) N N w z tau L G) := by
  rw [actual_error_is_same_Q_discrepancy_sum]
  exact r17_compiler_on_actual_ordered_fourths r n e q a nu beta tau N
    (realHalfProductDiscrepancy b N T)

/-- The actual negative-inner word contributes the exact real-source
PP summand on its own full modulus and has the same admitted fourth
ancestor as its actual eighth source. -/
theorem negative_inner_actual_distribution_summand
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta^2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (i : Fin 14) {d s : ℕ}
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) (width r))
    (hs : s ∈ actualSmallRosserSupport N N ((N : ℝ)^(nu * beta^2)))
    (hneg : (ArithmeticFunction.moebius d : ℝ) < 0)
    (hchanged : changed (keep r n e q a (nu * beta^2) N) (fun _ => []) N N
      ((N : ℝ)^(nu * beta^2)) (cutoff N) tau d) (b T : ℝ) :
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let L := (N : ℝ)^(nu*beta)
    let f := keep r n e q a omega N
    let word := rosserAncestor 8 d.primeFactorsList
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    let G := realHalfProductDiscrepancy b N T
    primeHistoryTuple 4 (rosserAncestor 4 word) ∈
      firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z) ∧
    P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    s*d ∈ moduli N w ∧
    coefficient r n e q a omega N tau L (s*d) * G (s*d) =
      (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (s*d) -
        (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (s*d) -
          actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (s*d)) +
        actualSmallRosserMinus N N w L s) * G (s*d) := by
  exact negative_inner_same_actual_fourth_product r n e q a nu beta tau he hcut hh
    N hN i hrank htrim hs hneg hchanged (realHalfProductDiscrepancy b N T)

/-- The original finite count bridge, at the same beta and rho, after
substituting the exact signed error above. The analytic PP bound remains
separate and unproved; no cancellation is discarded. -/
theorem r17_count_with_actual_fourth_distribution_error
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu v beta tau : ℝ)
    (N : ℕ) (hN : 1 < (N : ℝ)) (hnu : 0 < nu)
    (hbeta : 0 < beta) (h8 : beta < 1/8) (hsq : beta^2 < v)
    (hcut : nu*v = (19/96 : ℝ))
    {b T : ℝ} (hb : 0 < b) (hb1 : b < 1) (hT : 0 < T)
    (hgate : (Nat.ceil (cutoff N) : ℝ) ≤ T^(b/(1+b))) :
    let omega := nu*beta^2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let L := (N : ℝ)^(nu*beta)
    let Q := moduli N w
    let rho := coefficient r n e q a omega N tau L
    let f := keep r n e q a omega N
    let G := realHalfProductDiscrepancy b N T
    (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ)*physicalDensitySum Q rho +
      (stoppedBeforeFour f N N w z L G +
        (∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z),
          fourthTupleTerm f N N w z L G p) +
        (positiveOuterSum f (fun _ => []) N N w z tau L G +
          negativeInnerSum f (fun _ => []) N N w z tau L G)) +
      (Nat.ceil z : ℝ)+(T+1) := by
  have hs := original_beta_physical_scales N hN nu v beta hnu hbeta h8 hsq hcut
  have hc := P4AOriginalOrderedThirdActualCoefficient.count
    r n e q a (nu*beta^2) N tau ((N : ℝ)^(nu*beta))
    (hs.1.trans hs.2.1) hs.2.1.le hs.2.2.1.le hs.2.2.2 hb hb1 hT hgate
  rw [r17_distribution_error_on_actual_fourths r n e q a nu beta tau N b T] at hc
  exact hc

end
end ImbalancedChen.P2Saving16SameRhoDistributionFrontier
