import ImbalancedChen.P2Saving16All96ClosedBox

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED. Derive the original action
slacks and physical prefix-square gates on the same closed label box. -/
namespace ImbalancedChen.P2Saving16ActionGatesClosedBox
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P4AFull87CompilerChangedPartition P4AUpperTaggedFrozenAdmissionCatalogue
open P2CanonicalWallFullResidualPayment
open P4AOrderedThirdEighthTrimProgram
open P4AOrderedThirdStaticSixthPrograms (full_eval comp_eval)
open P4AOriginalFull87StrictActionTrim (trim Margin actionSlack)
open P4AOriginalFull87SourceDictionary (Source selected newCap comparison)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (HistoryOnTrim)
open P2OriginalSaving16Full87SourceBinding (sourceCell atlasCell sourceRows_iff_full87_source)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalR17EighthParent (orderedSixth)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P2Saving16FirstRowCompilerFibre P2Saving16SevenOrderRowsCarrier
open P2Saving16All96ClosedBox

/-- Original source membership supplies a positive action cap: the first
prefix-square gate and the original strict order give `0<2*t_1<newCap`. -/
theorem source_newCap_positive (c : P4AOriginalFull87SourceDictionary.Cell)
    (u : Fin 8 → ℝ) (hs : Source c u) : 0 < newCap c u := by
  have hb := P4AOriginalFull87SourceDictionary.source_basic hs
  have hfloor := hb.2.1
  have h01 := hb.2.2.2 (0 : Fin 7)
  have h12 := hb.2.2.2 (1 : Fin 7)
  norm_num at h01 h12
  have h0 : 0 < u 0 := by linarith
  have hgate := (P4AOriginalFull87SourceDictionary.source_full_selected hs).1 (0 : Fin 8)
  norm_num [prefixSquareExpr, Finset.sum_filter, Fin.sum_univ_succ] at hgate
  linarith

/-- Every actual action-slack constructor is strictly positive at an
original source point. Selected complement slots use the original
positive-cap fallback instead of inventing a complement square. -/
theorem source_action_slacks_positive (c : P4AOriginalFull87SourceDictionary.Cell)
    (u : Fin 8 → ℝ) (hs : Source c u) : ∀ m : Margin, 0 < actionSlack c u m := by
  have hp := source_newCap_positive c u hs
  have hi := (P4AOriginalFull87SourceDictionary.source_improvement_terminal hs).1
  have hf := P4AOriginalFull87SourceDictionary.source_full_selected hs
  intro m
  rw [← margin_exact]
  cases m with
  | positive => simpa [marginForm, new_exact] using hp
  | improvement =>
    simpa [marginForm, new_exact, cmp_exact] using (sub_pos.mpr hi)
  | full j =>
    simpa [marginForm, new_exact, full_eval] using (sub_pos.mpr (hf.1 j))
  | complement j =>
    by_cases hj : j ∈ selected c
    · simpa [marginForm, hj, new_exact] using hp
    · simpa [marginForm, hj, new_exact, comp_eval] using (sub_pos.mpr (hf.2 j hj))

/-- Every original closed-box point supplies all action slacks, both
families of square gates and the original selected-tent upper licence. -/
theorem action_gates_on_closed_box (i : Fin 14) (N d : ℕ) (tau delta : ℝ)
    (htau : 0 < tau) (hwidth : 12*tau < delta) (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau d k ≤ u k ∧ u k ≤ slotUpper N tau d k) :
    (∀ m : Margin, 0 < actionSlack (sourceCell i) u m) ∧
    (∀ j : Fin 8, prefixSquareExpr u j < newCap (sourceCell i) u) ∧
    (∀ j : Fin 8, j ∉ selected (sourceCell i) →
      selectedSquareExpr (selected (sourceCell i)) u j < newCap (sourceCell i) u) ∧
    newCap (sourceCell i) u < VariableEnvelope.v (∑ j ∈ selected (sourceCell i), u j) := by
  have hs : Source (sourceCell i) u := (sourceRows_iff_full87_source i u).mp
    (original_all96_closed_box i N d tau delta htau hwidth hrank htrim u hu)
  have hf := P4AOriginalFull87SourceDictionary.source_full_selected hs
  exact ⟨source_action_slacks_positive (sourceCell i) u hs, hf.1, hf.2,
    P4AOriginalFull87SourceDictionary.source_selected_license hs⟩

/-- Exact physical full-prefix and selected-complement square gates at
the same N and cap, under the pointwise prime-factor upper bounds. -/
theorem integer_gates_on_closed_box (i : Fin 14) (N d : ℕ) (hN : 1 < (N : ℝ))
    (tau delta : ℝ) (htau : 0 < tau) (hwidth : 12*tau < delta)
    (hrank : 8 ≤ d.primeFactorsList.length)
    (htrim : firstEightCoordinates N d ∈ trim (sourceCell i) delta)
    (u : Fin 8 → ℝ)
    (hu : ∀ k : Fin 8, slotLower N tau d k ≤ u k ∧ u k ≤ slotUpper N tau d k)
    (p : Fin 8 → ℕ) (hp : ∀ j, (p j : ℝ) ≤ (N : ℝ)^u j) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < (N : ℝ)^newCap (sourceCell i) u) ∧
    (∀ j ∉ selected (sourceCell i), ((∏ k ∈ selected (sourceCell i), p k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selected (sourceCell i)), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < (N : ℝ)^newCap (sourceCell i) u) := by
  have hs : Source (sourceCell i) u := (sourceRows_iff_full87_source i u).mp
    (original_all96_closed_box i N d tau delta htau hwidth hrank htrim u hu)
  exact P4AOriginalFull87SourceDictionary.source_integer_squares hs (N : ℝ) hN p hp

/-- One witness and full product carry all positive action slacks on the
closed box together with the existing same-Q sign-selected beta term. -/
theorem action_slacks_same_Q_signed_product
    (r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta tau : ℝ)
    (he : 0 ≤ e) (hcut : nu * beta ^ 2 ≤ a) (hh : HistoryOnTrim r e q a)
    (N : ℕ) (hN : 1 < (N : ℝ)) (htau : 0 < tau) (hwidth : 12*tau < width r)
    (i : Fin 14) {x y b : ℕ}
    (hx : x ∈ universe N N ((N : ℝ) ^ (nu * beta ^ 2)) (cutoff N))
    (hrank : 8 ≤ x.primeFactorsList.length)
    (htrim : firstEightCoordinates N x ∈ trim (sourceCell i) (width r))
    (hy : y ∈ cell (fun _ => []) N N ((N : ℝ) ^ (nu * beta ^ 2)) (cutoff N) tau x)
    (hb : b ∈ actualSmallRosserSupport N N ((N : ℝ) ^ (nu * beta ^ 2))) (G : ℕ → ℝ) :
    let omega := nu * beta ^ 2
    let w := (N : ℝ) ^ omega
    let z := cutoff N
    let L := (N : ℝ) ^ (nu * beta)
    let f := keep r n e q a omega N
    let word := rosserAncestor 8 x.primeFactorsList
    let bank := P4AOriginalFull87UnionHistory.bank e q a
    (∀ u : Fin 8 → ℝ, (∀ k : Fin 8, slotLower N tau x k ≤ u k ∧ u k ≤ slotUpper N tau x k) →
      ∀ m : Margin, 0 < actionSlack (sourceCell i) u m) ∧
    P2OriginalSaving16FourteenPhysicalAtlas.sourceRows (atlasCell i) (firstEightCoordinates N y) ∧
    b*y ∈ P4AOriginalFull87CompiledCounting.moduli N w ∧
    P4AOriginalFull87DataPolicy.level4Exponent n bank N (rosserAncestor 4 word) ≤
      P4AOriginalR17EighthParent.parent n e q a omega N word ∧
    P4AOriginalOrderedThirdActualCoefficient.coefficient r n e q a omega N tau L (b*y) * G (b*y) =
      (actualSmallRoughRho (orderedSixth n e q a omega N false) N N w z L (b*y) -
        (actualSmallRoughRho (sixthPolicy n e q a N false) N N w z L (b*y) -
         actualSmallRoughRho (policy (width r) n e q a N false) N N w z L (b*y)) +
       (if changed f (fun _ => []) N N w z tau y then
        (if 0 ≤ (ArithmeticFunction.moebius y : ℝ) then actualSmallRosserPlus N N w L b
         else actualSmallRosserMinus N N w L b)
       else 0)) * G (b*y) := by
  have hs := all96_same_Q_signed_product r n e q a nu beta tau he hcut hh
    N hN htau hwidth i hx hrank htrim hy hb G
  refine ⟨?_, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
  intro u hu
  exact (action_gates_on_closed_box i N x tau (width r) htau hwidth hrank htrim u hu).1

end
end ImbalancedChen.P2Saving16ActionGatesClosedBox
