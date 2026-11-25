import ImbalancedChen.P2Saving16NegativeFiniteCore
import ImbalancedChen.P2Saving16CommonTrimNegativeFibre
import ImbalancedChen.P2Saving16SignedCorrectionFamilies
import ImbalancedChen.P2Saving16ActualCompilerDifference

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
The actual negative-inner pair occurrences on one original trimmed cell
are grouped by their ordered eight-prefix, keeping each full product and
its signed beta-minus test. The untouched complement stays in the same
negative-inner sum; no new bound or reserve is asserted. -/
namespace ImbalancedChen.P2Saving16NegativeOriginalFibreSum
noncomputable section
open scoped Classical BigOperators
open Set
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies
open P2Saving16CommonTrimNegativeFibre P2Saving16FirstRowCompilerFibre
open P2Saving16SameRhoDistributionFrontier P2Saving16ActualFourthFrontier P2Saving16ActualFourthTuples
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87CompiledCounting (moduli)

/-- Every grouped key is an original-policy admitted eight-tuple and its
own compiler-policy fourth ancestor. The retained fibre still contains all
separate full moduli that gave this key. -/
theorem tuples_are_scheduled_original_fourths (r : ℕ) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, ∀ (n q : ℕ) (a nu beta tau : ℝ),
        let bank := P4AOriginalFull87UnionHistory.bank e q a
        q0 ≤ q → a ≤ 1 / 100 → nu * beta^2 ≤ a → HistoryOnTrim r e q a →
        ∀ (N : ℕ), 1 < N → ∀ (i : Fin 14) (p : Fin 8 → ℕ),
          let w := (N : ℝ)^(nu*beta^2)
          let z := P4AOriginalFull87RawChronology.cutoff N
          let f := keep r n e q a (nu*beta^2) N
          p ∈ tuples f (fun _ => []) N N w z tau (width r) i →
          p ∈ firstExitAdmittedTuples 8 (policy6 bank (N : ℝ))
            (roughPrimeUniverse N N w z) ∧
          primeHistoryTuple 4 (rosserAncestor 4
            (P2OriginalFourteenRetainedTupleOwnership.history p)) ∈
            firstExitAdmittedTuples 4 (oddFirstExitPolicy f)
              (roughPrimeUniverse N N w z) := by
  obtain ⟨e0, he0, h⟩ := scheduled_negative_inner_one_trim r
  refine ⟨e0, he0, ?_⟩
  intro e he he0e
  obtain ⟨q0, hq0⟩ := h e he he0e
  refine ⟨q0, ?_⟩
  intro n q a nu beta tau
  dsimp only
  intro hq ha hcut hh N hN i p hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
  have hsel := Finset.mem_filter.mp hx
  have hpair : x.1 ∈ actualSmallRosserSupport N N ((N : ℝ)^(nu*beta^2)) ∧
      x.2 ∈ «universe» N N ((N : ℝ)^(nu*beta^2))
        (P4AOriginalFull87RawChronology.cutoff N) := Finset.mem_product.mp hsel.1
  have hrank := hsel.2.1
  have ht := hsel.2.2.1
  have hn := hsel.2.2.2
  have hneg : (ArithmeticFunction.moebius x.2 : ℝ) < 0 := hn.1
  have hc : changed (keep r n e q a (nu*beta^2) N) (fun _ => []) N N
      ((N : ℝ)^(nu*beta^2)) (P4AOriginalFull87RawChronology.cutoff N) tau x.2 := by
    simpa only [changed, if_neg (not_le_of_gt hneg)] using hn.2
  have hs := hq0 n q a nu beta tau hq ha hcut hh N hN i hrank ht hpair.1 hneg hc 0 0
  exact ⟨hs.1, hs.2.1⟩

/-- The existing same-Q, same-rho signed distribution error now exposes
one original-cell negative-inner family by ordered eight-prefix, with the
remaining negative-inner terms preserved once in their exact complement. -/
theorem r17_distribution_error_with_original_eight_fibres
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (N : ℕ) (i : Fin 14) (b T : ℝ) :
    let omega := nu*beta^2
    let w := (N : ℝ)^omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let L := (N : ℝ)^(nu*beta)
    let Q := moduli N w
    let rho := coefficient r n e q a omega N tau L
    let f := keep r n e q a omega N
    let G := realHalfProductDiscrepancy b N T
    realPhysicalDistributionError b N T Q rho =
      stoppedBeforeFour f N N w z L G +
        (∑ p ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy f)
            (roughPrimeUniverse N N w z), fourthTupleTerm f N N w z L G p) +
        (positiveOuterSum f (fun _ => []) N N w z tau L G +
          ((∑ p ∈ tuples f (fun _ => []) N N w z tau (width r) i,
              fibreSum f (fun _ => []) N N w z tau (width r) L i G p) +
            complementSum f (fun _ => []) N N w z tau (width r) L i G)) := by
  have h := r17_distribution_error_on_actual_fourths r n e q a nu beta tau N b T
  rw [negativeInner_exact_split _ _ _ _ _ _ _ (width r) _ i _,
    selectedSum_eq_ordered_eight_fibres] at h
  exact h

end
end ImbalancedChen.P2Saving16NegativeOriginalFibreSum
