import ImbalancedChen.P2Saving16NegativeInnerFourthAncestor
import ImbalancedChen.P2Saving16All96ClosedBox
import ImbalancedChen.P2Saving16SevenOrderRowsCarrier

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
The positive-outer added word and its retained witness remain distinct.
Attach the witness's actual fourth ancestor and all original source rows
while the compiler coefficient and full-q multiplier remain at the added
word. No geometric corner equality or PP estimate is asserted. -/
namespace ImbalancedChen.P2Saving16PositiveOuterFourthWitness
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies
open P2Saving16ThirdRowFourthParent P2Saving16SevenOrderRowsCarrier
open P2Saving16All96ClosedBox P2Saving16NegativeInnerFourthAncestor
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell atlasCell)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalFull87CompiledCounting (moduli)

/-- A positive outer change has a genuinely distinct retained witness on
all the same eight labels, and its own canonical fourth ancestor is
admitted by the exact compiler policy. -/
theorem positive_outer_distinct_admitted_witness
    (ret : List ℕ → Bool) (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hrank : 8 ≤ d.primeFactorsList.length)
    (hpos : 0 ≤ (ArithmeticFunction.moebius d : ℝ))
    (hchanged : changed ret (fun _ => []) N cap w z tau d) :
    ∃ v : ℕ,
      v ≠ d ∧ v ∈ cell (fun _ => []) N cap w z tau d ∧
      v ∈ rawSupport ret N cap w z ∧ 8 ≤ v.primeFactorsList.length ∧
      (∀ j : Fin 8, primeLabel N tau (canonicalPrefix 8 d j) =
        primeLabel N tau (canonicalPrefix 8 v j)) ∧
      primeHistoryTuple 4 (rosserAncestor 4 (rosserAncestor 8 v.primeFactorsList)) ∈
        firstExitAdmittedTuples 4 (oddFirstExitPolicy ret) (roughPrimeUniverse N cap w z) := by
  obtain ⟨hnot, v, hv, hraw⟩ :=
    positive_outer_actual_witness ret (fun _ => []) N cap w z tau hpos hchanged
  have hne : v ≠ d := by
    intro h
    subst v
    exact hnot hraw
  have hvrank : 8 ≤ v.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hv]
    exact hrank
  have hadm := retained_word_admits_canonical_four ret N cap w z hraw
    ((by decide : 4 ≤ 8).trans hvrank)
  refine ⟨v, hne, hv, hraw, hvrank, ?_, ?_⟩
  · intro j
    exact cell_canonicalPrefix_label_eq (fun _ => []) N cap w z tau hv hrank j
  · rw [canonical_four_is_actual_ancestor v hvrank]
    exact hadm

/-- On a single actual trimmed ascending source cell, the retained witness
lies in that same source. The added word keeps its own fourth-parent
comparison and its own full-modulus beta-plus compiler term. -/
theorem positive_outer_same_cell_fourth_witness_and_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta^2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (htau : 0 < tau)
    (hwidth : 12*tau < width r) (i : Fin 14) {d b : ℕ}
    (hd : d ∈ universe N N ((N : ℝ)^(nu * beta^2)) (cutoff N))
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) (width r))
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ)^(nu * beta^2)))
    (hpos : 0 ≤ (ArithmeticFunction.moebius d : ℝ))
    (hchanged : changed (keep r n e q a (nu * beta^2) N) (fun _ => []) N N
      ((N : ℝ)^(nu * beta^2)) (cutoff N) tau d) (G : ℕ → ℝ) :
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let L := (N : ℝ)^(nu*beta)
    let f := keep r n e q a omega N
    let word := rosserAncestor 8 d.primeFactorsList
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    ∃ v : ℕ,
      v ≠ d ∧ v ∈ cell (fun _ => []) N N w z tau d ∧
      v ∈ rawSupport f N N w z ∧
      P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) (firstEightCoordinates N v) ∧
      (∀ j : Fin 8, primeLabel N tau (canonicalPrefix 8 d j) =
        primeLabel N tau (canonicalPrefix 8 v j)) ∧
      primeHistoryTuple 4 (rosserAncestor 4 (rosserAncestor 8 v.primeFactorsList)) ∈
        firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z) ∧
      P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
        P4AOriginalR17EighthParent.parent n e q a omega N word ∧
      b*d ∈ moduli N w ∧
      (∀ s t : ℕ, s ∈ actualSmallRosserSupport N N w → t ∈ universe N N w z →
        s*t = b*d → s = b ∧ t = d) ∧
      coefficient r n e q a omega N tau L (b*d) * G (b*d) =
        (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (b*d) -
          (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (b*d) -
            actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (b*d)) +
          actualSmallRosserPlus N N w L b) * G (b*d) := by
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  let f := keep r n e q a omega N
  obtain ⟨v, hne, hv, hraw, hvrank, hlabels, hadm⟩ :=
    positive_outer_distinct_admitted_witness f N N w z tau hrank hpos hchanged
  have hsource := original_all96_on_fibre i N w tau (width r) htau hwidth hrank htrim hv
  have hQ := actual_product_mem_Q_unique N w hb hd
  have hc := r17_actual_coefficient_at_product r n e q a nu beta tau he hcut hh N hN hb hd
  dsimp only at hc
  simp only [if_pos hchanged, if_pos hpos] at hc
  exact ⟨v, hne, hv, hraw, hsource, hlabels, hadm,
    actual_fourth_le_sixth_parent r n e q a omega he hcut hh N hN i d hrank htrim,
    hQ.1, hQ.2, congrArg (fun x : ℝ => x * G (b*d)) hc⟩

end
end ImbalancedChen.P2Saving16PositiveOuterFourthWitness
