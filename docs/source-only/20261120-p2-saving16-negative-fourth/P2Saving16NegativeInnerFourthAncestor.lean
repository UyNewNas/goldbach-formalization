import ImbalancedChen.P2Saving16ActualFourthTuples
import ImbalancedChen.P2Saving16ThirdRowFourthParent
import ImbalancedChen.P2LowerCanonicalRetainedTrace

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
For a negative inner deletion the word itself is retained. Recover its
actual ordered fourth ancestor and the same full-product beta-minus term.
No identification with a geometric corner or PP estimate is asserted. -/
namespace ImbalancedChen.P2Saving16NegativeInnerFourthAncestor
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P2Saving16ActualCompilerDifference P2Saving16SignedCorrectionFamilies
open P2Saving16ThirdRowFourthParent P2Saving16ActualFourthTuples
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth orderedEighth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalFull87CompiledCounting (moduli)

/-- Every initial segment inherits the actual causal policy tests. -/
private theorem validSelection_take {α : Type*} (R : Bool → List α → Bool)
    (xs : List α) : ∀ (pre : List α) (pos : Bool) (k : ℕ),
    FirstExitValidSelection R pre pos xs → FirstExitValidSelection R pre pos (xs.take k) := by
  intro pre pos k hv
  induction xs generalizing pre pos k with
  | nil => simp [FirstExitValidSelection]
  | cons p ps ih =>
    cases k with
    | zero => simp [FirstExitValidSelection]
    | succ k =>
      change R (!pos) (p :: pre) = true ∧
        FirstExitValidSelection R (p :: pre) (!pos) (ps.take k)
      exact ⟨hv.1, ih (p :: pre) (!pos) k hv.2⟩

/-- Retention of the actual rough word implies admission of its actual
first four ordered prime factors, on the same carrier and same policy. -/
theorem retained_word_admits_canonical_four (ret : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ rawSupport ret N cap w z) (hr : 4 ≤ d.primeFactorsList.length) :
    canonicalPrefix 4 d ∈ firstExitAdmittedTuples 4 (oddFirstExitPolicy ret)
      (roughPrimeUniverse N cap w z) := by
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_oddFirstExitRetainedModuli ret (fun _ => 1) (roughPrimeUniverse N cap w z) d).mp hd
  obtain ⟨chosen, hsub, hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves (oddFirstExitPolicy ret) (fun _ => 1)
      [] (roughPrimeUniverse N cap w z) true 1 leaf hleaf
  have hchosen : chosen.prod = d := by
    simpa only [hselected, List.append_nil, List.prod_reverse] using hprod
  have hcanonical := P2LowerCanonicalRetainedTrace.actual_chosen_eq_canonical
    N cap w z chosen hsub hchosen
  have hsub4 : chosen.take 4 <+ roughPrimeUniverse N cap w z :=
    (List.take_sublist 4 chosen).trans hsub
  have hv4 := validSelection_take (oddFirstExitPolicy ret) chosen [] true 4 hvalid
  apply (mem_firstExitAdmittedTuples_iff 4 (oddFirstExitPolicy ret) _ _).mpr
  constructor
  · simpa only [hcanonical, ← canonicalPrefix_ofFn hr] using hsub4
  · simpa only [hcanonical, ← canonicalPrefix_ofFn hr] using hv4

/-- The canonical four-tuple is the fourth ancestor of the same actual
eighth source word, not an independent fibre representative. -/
theorem canonical_four_is_actual_ancestor (d : ℕ)
    (hrank : 8 ≤ d.primeFactorsList.length) :
    primeHistoryTuple 4 (rosserAncestor 4 (rosserAncestor 8 d.primeFactorsList)) =
      canonicalPrefix 4 d := by
  have hr : 4 ≤ d.primeFactorsList.length := (by decide : 4 ≤ 8).trans hrank
  have hlen : (rosserAncestor 4 d.primeFactorsList).length = 4 := by
    rw [rosserAncestor_length, min_eq_left hr]
  have hrev : (rosserAncestor 4 d.primeFactorsList).reverse =
      d.primeFactorsList.reverse.take 4 := by
    simp only [rosserAncestor, List.reverse_drop]
    congr 1
    omega
  rw [rosserAncestor_nested 4 8 (by decide)]
  apply List.ofFn_injective
  rw [primeHistoryTuple_ofFn hlen, canonicalPrefix_ofFn hr, hrev]

/-- Concrete negative-inner family on one actual trimmed eighth source.
Its own fourth ancestor is admitted and bounded by the same R17 parent;
the compiler reads the beta-minus value at the same full product. -/
theorem negative_inner_same_actual_fourth_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta^2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (i : Fin 14) {d b : ℕ}
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) (width r))
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ)^(nu * beta^2)))
    (hneg : (ArithmeticFunction.moebius d : ℝ) < 0)
    (hchanged : changed (keep r n e q a (nu * beta^2) N) (fun _ => []) N N
      ((N : ℝ)^(nu * beta^2)) (cutoff N) tau d) (G : ℕ → ℝ) :
    let omega := nu * beta^2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let L := (N : ℝ)^(nu*beta)
    let f := keep r n e q a omega N
    let word := rosserAncestor 8 d.primeFactorsList
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    primeHistoryTuple 4 (rosserAncestor 4 word) ∈
      firstExitAdmittedTuples 4 (oddFirstExitPolicy f) (roughPrimeUniverse N N w z) ∧
    P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    b*d ∈ moduli N w ∧
    coefficient r n e q a omega N tau L (b*d) * G (b*d) =
      (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (b*d) -
        (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (b*d) -
          actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (b*d)) +
        actualSmallRosserMinus N N w L b) * G (b*d) := by
  let omega := nu * beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  let f := keep r n e q a omega N
  have hraw : d ∈ rawSupport f N N w z :=
    (negative_inner_actual_witness f (fun _ => []) N N w z tau hneg hchanged).1
  have hu : d ∈ universe N N w z := rawSupport_subset_universe f N N w z hraw
  have hadm := retained_word_admits_canonical_four f N N w z hraw
    ((by decide : 4 ≤ 8).trans hrank)
  have hanc := canonical_four_is_actual_ancestor d hrank
  have hQ : b*d ∈ moduli N w := by
    change b*d ∈ smallRoughModuli (actualSmallRosserSupport N N w) (universe N N w z)
    exact Finset.mem_image.mpr ⟨(b,d), Finset.mem_product.mpr ⟨hb, hu⟩, rfl⟩
  have hc := r17_actual_coefficient_at_product r n e q a nu beta tau he hcut hh N hN hb hu
  dsimp only at hc
  have hn : ¬ 0 ≤ (ArithmeticFunction.moebius d : ℝ) := not_le_of_gt hneg
  simp only [if_pos hchanged, if_neg hn] at hc
  refine ⟨?_, actual_fourth_le_sixth_parent r n e q a omega he hcut hh N hN i d hrank htrim,
    hQ, congrArg (fun v : ℝ => v * G (b*d)) hc⟩
  rw [hanc]
  exact hadm

end
end ImbalancedChen.P2Saving16NegativeInnerFourthAncestor
