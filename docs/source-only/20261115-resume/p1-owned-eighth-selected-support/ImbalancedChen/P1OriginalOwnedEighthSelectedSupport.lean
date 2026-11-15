import ImbalancedChen.P4AOriginalFull87AllEighthFrontierTerminal
import ImbalancedChen.P4AOriginalFull87OwnedPrimitiveLedger
import ImbalancedChen.P4AFinitePPSelectedPrefixSquares
import ImbalancedChen.Part3ActualCompactAllRankSupport
import ImbalancedChen.FirstExitValidSelection

/-!
SOURCE-ONLY CANDIDATE. NOT ELABORATED OR KERNEL CHECKED.

The same selected eighth cap licenses the COMPLETE before/after terminal
words in the original owned87 saving. The actual sixth parent is read from
the existing tree, and its comparison with this cap is supplied by the
existing common-history theorem. Every later selected prime remains in the
original suffix, with the original target deletion and occurrence list.

This supplies the full and selected-remaining square supports in paragraph 3
of current-eighth-distribution-interface-audit-20261009.tex. It does not
construct an independent whole-box convolution, transfer a compiler error,
identify this coefficient with lower ALL16 or the final upper coefficient,
or prove any signed prime-product estimate.
-/

namespace ImbalancedChen.P1OriginalOwnedEighthSelectedSupport
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87SevenCubeAdmission (pre pre_length pre_ofFn point tuple_pre)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source)
open P4AOriginalFull87FiniteEighthCap (finiteCap finiteCap_licensed)
open P4AOriginalFull87FiniteEighthPolicy (point8_at_eight)
open P4AOriginalFull87LicensedSixthRealization (states FilteredSourceSupply)
open P4AOriginalFull87LicensedSixthPolicy (policy sixthPolicy level6Exponent)
open P4AOriginalFull87EighthKernelIntegration (actualParent actualParent_residual)
open P4AOriginalFull87OwnedPrimitiveLedger (beforeLeaves afterLeaves)
open P4AOriginalFull87InheritedTerminalLevel (ordinary_terminal_admissible)
open P4AOriginalFull87AllEighthFrontierTerminal (actual_rank_eight_state_canonical)

/-- A genuine terminal occurrence on either side of the original saving
has both complete square supports at its OWN selected eighth cap. The
strict tent and physical buffers are fixed by n, before the target N.
No ordinary-admission, selected-square, parent-order or support premise
is added: all of them are produced from the actual state and old supplier.
The enumeration cap remains arbitrary, including cap = 2*N. -/
theorem actual_before_after_selected_support
    (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (H : FilteredSourceSupply s r n e q om)
    (hn : 4 * width n < width r)
    (N cap : ℕ) (w z : ℝ) (hN : 1 < (N : ℝ))
    (c : Cell) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ states (width r) n e q om N cap w z (fun _ => 1) c)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ beforeLeaves n e q om N state ∨
      leaf ∈ afterLeaves n e q om N c state) :
    let M := (finiteCap n c (point8 (N : ℝ) state.selectedPrefix) : ℝ)
    ∃ (p : Fin 8 → ℕ) (tail : List ℕ),
      (∀ i, (p i).Prime) ∧ (∀ i, ¬p i ∣ N) ∧
      pre p = state.selectedPrefix ∧ tail <+ state.remaining ∧
      leaf.selected.reverse = List.ofFn p ++ tail ∧
      actualDwellSupport ((N : ℝ)^M) leaf.selected.reverse ∧
      actualDwellSupport
        (((N : ℝ)^M) /
          ((P4AFinitePPSelectedPrefixSquares.selected (selected c) p).prod : ℝ))
        (P4AFinitePPSelectedPrefixSquares.selected (selected c)ᶜ p ++ tail) ∧
      M + width n < VariableEnvelope.v (∑ i ∈ selected c, actualPrimeTupleLog N p i) ∧
      M + width n < (153 / 256 : ℝ) := by
  let M := (finiteCap n c (point8 (N : ℝ) state.selectedPrefix) : ℝ)
  let P := actualParent n e q om (N : ℝ) state.selectedPrefix
  have hstate' := hstate
  unfold states at hstate'
  obtain ⟨hfront, hfilter⟩ := List.mem_filter.mp hstate'
  have htrim8 : point8 (N : ℝ) state.selectedPrefix ∈ trim c (width r) :=
    (of_decide_eq_true hfilter).2
  obtain ⟨p, hp, hdelete, hcanonical⟩ :=
    actual_rank_eight_state_canonical (width r) n e q om
      N cap w z (fun _ => 1) state hfront
  have hpre : pre p = state.selectedPrefix := by rw [hcanonical]; rfl
  have hcoord : point8 (N : ℝ) state.selectedPrefix = point (N : ℝ) p :=
    (congrArg (point8 (N : ℝ)) hpre.symm).trans
      (point8_at_eight (N : ℝ) (pre p) (pre_length p))
  have hlog : point (N : ℝ) p = actualPrimeTupleLog N p := by
    change actualPrimeTupleLog N (primeHistoryTuple 8 (pre p)) = actualPrimeTupleLog N p
    rw [tuple_pre]
  have htrim : point (N : ℝ) p ∈ trim c (width r) := hcoord ▸ htrim8
  have hsource := trim_subset_source c (width_pos r) htrim
  have hM : (finiteCap n c (point (N : ℝ) p) : ℝ) = M := by
    dsimp only [M]
    rw [hcoord]
  have hlic := finiteCap_licensed n (width_pos r) hn htrim
  have hhistory := (H N hN p hp hdelete c htrim).1
  have hparent := actualParent_residual n e q om (N : ℝ)
    (pre p) (pre_length p) c hsource hhistory
  have hPM : P ≤ M := by
    have hcmp : comparison c (point (N : ℝ) p) ≤
        (finiteCap n c (point (N : ℝ) p) : ℝ) := by
      have hgap := hlic.2.1
      have hw := width_pos r
      linarith
    have h := hparent.2.trans hcmp
    simpa only [hpre, hM, P] using h
  have hpower : (N : ℝ)^P ≤ (N : ℝ)^M :=
    Real.rpow_le_rpow_of_exponent_le hN.le hPM
  have hsix : state ∈ firstExitDepthFrontier 8
      (sixthPolicy n e q om (N : ℝ)) (fun _ => 1) [] true 1
      (roughPrimeUniverse N cap w z) := by
    simpa only [P4AOriginalFull87LicensedSixthPolicy.frontier_eq_new_sixth] using hfront
  have hactual : state ∈ firstExitDepthFrontier 8
      (P4AActualSixthFrozenEighthAdmission.sixthPolicy
        (P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q om (N : ℝ))
        (fun history => (N : ℝ)^level6Exponent n e q om (N : ℝ) history))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only [P4AActualSixthFrozenEighthAdmission.sixthPolicy, sixthPolicy] using hsix
  have hentryP : ordinaryRosserPrefixAdmissible false ((N : ℝ)^P)
      state.selectedPrefix := by
    exact P4AActualSixthFrozenEighthAdmission.actual_rank_eight_admissible
      (P4AOriginalFull87FiniteParentPolicy.fifthPolicy n e q om (N : ℝ))
      (fun history => (N : ℝ)^level6Exponent n e q om (N : ℝ) history)
      N cap w z (fun _ => 1) state hactual
  have hentryM := ordinaryRosserPrefixAdmissible_mono false _ hpower hentryP
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength
    8 (policy (width r) n e q om (N : ℝ)) (fun _ => 1)
    (roughPrimeUniverse N cap w z) state hfront
  have hprefix : state.selectedPrefix.reverse ++ state.remaining <+
      roughPrimeUniverse N cap w z := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist
      8 (policy (width r) n e q om (N : ℝ)) (fun _ => 1)
      [] (roughPrimeUniverse N cap w z) true 1 state hfront
  have hprime : ∀ p ∈ state.remaining, p.Prime := fun p hp =>
    mem_roughPrimeUniverse_prime (hprefix.subset (List.mem_append_right _ hp))
  have horder := (roughPrimeUniverse_pairwise_gt N cap w z).sublist hprefix
  have hsort : (state.remaining.reverse ++ state.selectedPrefix).Pairwise (· < ·) := by
    simpa only [List.reverse_append, List.reverse_reverse, List.pairwise_reverse] using horder
  have hterminal : ordinaryRosserPrefixAdmissible false ((N : ℝ)^M) leaf.selected := by
    rcases hleaf with hbefore | hafter
    · have ht := ordinary_terminal_admissible ((N : ℝ)^P) (fun _ => 1)
        state.selectedPrefix state.remaining state.positive state.mass
        hentryP hsign hprime hsort leaf hbefore
      exact ordinaryRosserPrefixAdmissible_mono false _ hpower ht
    · exact ordinary_terminal_admissible ((N : ℝ)^M) (fun _ => 1)
        state.selectedPrefix state.remaining state.positive state.mass
        hentryM hsign hprime hsort leaf hafter
  have htail : ∃ tail : List ℕ, tail <+ state.remaining ∧
      leaf.selected = tail.reverse ++ state.selectedPrefix := by
    rcases hleaf with hbefore | hafter
    · obtain ⟨tail, hsub, _hvalid, heq⟩ :=
        exists_validSelection_of_mem_firstExitRetainedLeaves
          (ordinaryParityRosserPolicy false ((N : ℝ)^P)) (fun _ => 1)
          state.selectedPrefix state.remaining state.positive state.mass leaf hbefore
      exact ⟨tail, hsub, heq⟩
    · obtain ⟨tail, hsub, _hvalid, heq⟩ :=
        exists_validSelection_of_mem_firstExitRetainedLeaves
          (ordinaryParityRosserPolicy false ((N : ℝ)^M)) (fun _ => 1)
          state.selectedPrefix state.remaining state.positive state.mass leaf hafter
      exact ⟨tail, hsub, heq⟩
  obtain ⟨tail, htail, hselected⟩ := htail
  have hreverse : leaf.selected.reverse = state.selectedPrefix.reverse ++ tail := by
    rw [hselected, List.reverse_append, List.reverse_reverse]
  have hword : leaf.selected.reverse = List.ofFn p ++ tail := by
    rw [hreverse, ← hpre, pre_ofFn, List.reverse_reverse]
  have hsub : leaf.selected.reverse <+ roughPrimeUniverse N cap w z := by
    rw [hreverse]
    exact ((List.Sublist.refl _).append htail).trans hprefix
  have hfull : actualDwellSupport ((N : ℝ)^M) leaf.selected.reverse := by
    apply Part3.ActualCompactAllRankSupport.upper_set_dwell_support _
      (fun p hp => mem_roughPrimeUniverse_prime (hsub.subset hp))
      ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
    simpa only [Bool.false_eq_true, if_false, List.toFinset_reverse] using hterminal.2
  refine ⟨p, tail, hp, hdelete, hpre, htail, hword, hfull, ?_, ?_, ?_⟩
  · have hg : ∀ j ∉ selected c,
        selectedSquareExpr (selected c) (actualPrimeTupleLog N p) j ≤ M := by
      intro j hj
      have h := hlic.2.2.2.1 j hj
      rw [hM, hlog] at h
      have hw := width_pos r
      linarith
    have hfull' : actualDwellSupport ((N : ℝ)^M) (List.ofFn p ++ tail) :=
      hword ▸ hfull
    exact P4AFinitePPSelectedPrefixSquares.complete
      (by exact_mod_cast hN : 1 < N) (selected c) p (fun i => (hp i).pos) tail M hfull' hg
  · simpa only [hM, hlog] using hlic.2.2.2.2.2
  · have hc : M + width n ≤ newCap c (point (N : ℝ) p) := by
      simpa only [hM] using hlic.2.2.2.2.1
    exact hc.trans_lt (source_physical_ceiling hsource)

end
end ImbalancedChen.P1OriginalOwnedEighthSelectedSupport
