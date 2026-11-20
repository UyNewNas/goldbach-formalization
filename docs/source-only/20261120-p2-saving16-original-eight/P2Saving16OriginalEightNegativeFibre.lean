import ImbalancedChen.P2OriginalFourteenRetainedTupleOwnership
import ImbalancedChen.P2Saving16SameRhoDistributionFrontier
import ImbalancedChen.P2LowerCanonicalRetainedTrace

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.

One actual negative-inner modulus may have a tail after its first eight
primes. Its original ordered eight-tuple is transported to the same positive
rough carrier and its literal fourth ancestor is the one used by the signed
compiler. No equality with a geometric corner or analytic PP estimate is
asserted. The original admission is an explicit, separate premise.
-/
namespace ImbalancedChen.P2Saving16OriginalEightNegativeFibre
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies P2Saving16ActualFourthFrontier
open P2Saving16ActualFourthTuples P2Saving16SameRhoDistributionFrontier
open P2Saving16NegativeInnerFourthAncestor P2Saving16FirstRowCompilerFibre
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalFull87CompiledCounting (moduli)

/-- The original processing-order tuple gives the literal eighth ancestor,
including its order. The full modulus is not assumed to end there. -/
theorem original_history_eq_actual_eighth (d : ℕ)
    (hrank : 8 ≤ d.primeFactorsList.length) :
    P2OriginalFourteenRetainedTupleOwnership.history (canonicalPrefix 8 d) =
      rosserAncestor 8 d.primeFactorsList := by
  have hrev : (rosserAncestor 8 d.primeFactorsList).reverse =
      d.primeFactorsList.reverse.take 8 := by
    simp only [rosserAncestor, List.reverse_drop]
    congr 1
    omega
  have h := congrArg List.reverse hrev
  simp only [List.reverse_reverse] at h
  unfold P2OriginalFourteenRetainedTupleOwnership.history
  rw [canonicalPrefix_ofFn hrank]
  exact h.symm

/-- Transfer the original eighth admission from the ordinary carrier to
the positive carrier using the full modulus itself. The historical policy
is unchanged; the same eight ordered entries and their occurrences survive. -/
theorem original_eight_on_positive_carrier
    (data : OriginalData) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hrank : 8 ≤ d.primeFactorsList.length)
    (hp : canonicalPrefix 8 d ∈
      P2OriginalFourteenRetainedTupleOwnership.admitted data N cap z)
    (hd : d ∈ universe N cap w z) :
    canonicalPrefix 8 d ∈ firstExitAdmittedTuples 8 (policy6 data (N : ℝ))
      (roughPrimeUniverse N cap w z) := by
  have hv := (mem_firstExitAdmittedTuples_iff 8 (policy6 data (N : ℝ))
    (roughPrimeUniverse N cap 0 z) (canonicalPrefix 8 d)).mp hp
  have hs := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hd).1
  apply (mem_firstExitAdmittedTuples_iff 8 (policy6 data (N : ℝ))
    (roughPrimeUniverse N cap w z) (canonicalPrefix 8 d)).mpr
  refine ⟨?_, hv.2⟩
  rw [canonicalPrefix_ofFn hrank]
  exact (List.take_sublist 8 d.primeFactorsList.reverse).trans hs

/-- For an original admitted eighth occurrence in one of the fourteen
trimmed cells, a negative-inner changed full modulus carries the same
original ordered history into the signed compiler. The beta-minus term
and discrepancy are evaluated at the full modulus s*d, including any tail.
The full signed error is the existing same-Q decomposition; no new charge
is introduced. -/
theorem original_eight_negative_summand_on_same_error
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta^2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (i : Fin 14) {d s : ℕ}
    (hrank : 8 ≤ d.primeFactorsList.length)
    (hp : canonicalPrefix 8 d ∈ P2OriginalFourteenRetainedTupleOwnership.admitted
      (P4AOriginalFull87UnionHistory.bank e q a) N N (cutoff N))
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
    let word := P2OriginalFourteenRetainedTupleOwnership.history (canonicalPrefix 8 d)
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    let G := realHalfProductDiscrepancy b N T
    canonicalPrefix 8 d ∈ firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
      (roughPrimeUniverse N N w z) ∧
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
  have hraw : d ∈ rawSupport (keep r n e q a (nu * beta^2) N) N N
      ((N : ℝ)^(nu * beta^2)) (cutoff N) :=
    (negative_inner_actual_witness (keep r n e q a (nu * beta^2) N)
      (fun _ => []) N N ((N : ℝ)^(nu * beta^2)) (cutoff N) tau hneg hchanged).1
  have hu := rawSupport_subset_universe (keep r n e q a (nu * beta^2) N)
    N N ((N : ℝ)^(nu * beta^2)) (cutoff N) hraw
  have ha := original_eight_on_positive_carrier
    (P4AOriginalFull87UnionHistory.bank e q a) N N
    ((N : ℝ)^(nu * beta^2)) (cutoff N) hrank hp hu
  have hc := negative_inner_actual_distribution_summand r n e q a nu beta tau
    he hcut hh N hN i hrank htrim hs hneg hchanged b T
  have hword := original_history_eq_actual_eighth d hrank
  exact ⟨ha, by simpa only [hword] using hc⟩

end
end ImbalancedChen.P2Saving16OriginalEightNegativeFibre
