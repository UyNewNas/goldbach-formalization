import ImbalancedChen.P4AOriginalFiniteAll22RawLedger
import ImbalancedChen.P4AOriginalR17Full87SavedEndpoint

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The original eighth selector cannot select a genuine source above mu.
This proves equality on EACH high first-exit policy word. T04's genuine
sector identity then transfers the already proved I87 gain to the final
common upper-bank dispatcher without redoing its integrals or prime mean.
-/
namespace ImbalancedChen.P4AOriginalFull87UpperDispatch
noncomputable section
open VariableEnvelope
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackPolicy (Rule high dispatch)
open P4AOriginalFull87RawChronology (rawRoot)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_some_spec)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87HistoryCore (width width_pos)

theorem selectedCap_none_on_high (delta : ℝ) (hd : 0<delta) (n : ℕ) (N : ℝ)
    (h : List ℕ) (hlen : 8≤h.length) (hh : high N h) : selectedCap delta n N h=none := by
  cases hs : selectedCap delta n N h with
  | none => rfl
  | some a =>
      obtain ⟨c,_,ht,_⟩ := selectedCap_some_spec delta n N h a hs
      have hc := P4AOriginalFull87StrictActionTrim.trim_subset_source c hd ht
      have hb := P4AOriginalFull87SourcePrimeTests.source_subset_box c hc
      have hup : point8 N h 0<mu := (mem_logPrimeBox.mp hb 0).2
      have hlen8 : (rosserAncestor 8 h).length=8 := by
        simp only [rosserAncestor,List.length_drop]
        omega
      have hh8 : high N (rosserAncestor 8 h) := by
        simpa only [high,P4AOriginalFiniteFallbackPolicy.point,rosserAncestor_nested 1 8 (by decide)] using hh
      have hcoord := primeHistoryLogCoordinates_ancestor N hlen8 (by decide : 1≤8) (0:Fin 1)
      have hlo : mu<point8 N h 0 := by
        change mu<primeHistoryLogCoordinates N 1 (rosserAncestor 1 (rosserAncestor 8 h)) 0 at hh8
        simpa only [hcoord,point8] using hh8
      exact False.elim ((not_lt_of_ge hup.le) hlo)

theorem eighth_words (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData)
    (omega N : ℝ) (b : Bool) (h : List ℕ) (hh : high N h) :
    P4AOriginalOrderedSixthStages.policy 10 n d omega N b h=
      P4AOriginalOrderedThirdFullPolicy.policy delta n d omega N b h := by
  rw [P4AOriginalOrderedSixthStages.policy_ten]
  unfold P4AOriginalOrderedThirdFullPolicy.policy P4AOriginalOrderedThirdFullPolicy.eight
  by_cases hl : h.length≤8
  · simp only [firstExitDepthSplicePolicy,if_pos hl]
  · have hc := selectedCap_none_on_high delta hd n N h (by omega) hh
    simp only [firstExitDepthSplicePolicy,if_neg hl,hc]

theorem dispatch_eighth (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData)
    (omega : ℝ) (N : ℕ) (U : Rule) (hU : ∀ h,U true h=true) :
    normalize N (rawRoot (dispatch N U (P4AOriginalOrderedSixthStages.policy 10 n d omega N)) N-
      rawRoot (dispatch N U (P4AOriginalOrderedThirdFullPolicy.policy delta n d omega N)) N)=
      normalize N (rawRoot (P4AOriginalOrderedSixthStages.policy 10 n d omega N) N-
        rawRoot (P4AOriginalOrderedThirdFullPolicy.policy delta n d omega N) N) :=
  congrArg (normalize N) (P4AOriginalFiniteFallbackSectorTransport.local_increment N U _ _ hU
    (P4AOriginalOrderedSixthSigned.even 10 n d omega N)
    (P4AOriginalFiniteFallbackJointGain.lower_even delta n d omega N)
    (eighth_words delta hd n d omega N))

/-- The literal low-sector I87 term in the final all22 telescope equals
the ALREADY paid current R17 ordinary difference at the same target. -/
theorem lowerEighth_eq_paid_source (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    P4AOriginalFiniteAll22RawLedger.lowerEighth r n e q a omega N=
      normalize N (rawRoot (P4AOriginalR17EighthParent.orderedSixth n e q a omega N) N-
        rawRoot (P4AOriginalR17EighthParent.orderedEighth r n e q a omega N) N) := by
  let d := P4AOriginalNewFifthUnion.data e q a
  have hU : ∀ h,P4AOrderedThirdArithmeticOccurrence.fresh d omega N true h=true := by
    intro h
    rw [←P4AOriginalFiniteFallbackOccurrence.empty_eq (P4AFallbackCanonicalBanks.bank 0) d omega N]
    exact P4AOriginalFiniteFallbackOccurrence.positive _ _ _ _ _
  unfold P4AOriginalFiniteAll22RawLedger.lowerEighth P4AOriginalFiniteAll22RawLedger.lowEighth
    P4AOriginalFiniteAll22RawLedger.lowStage
  rw [dispatch_eighth (width r) (width_pos r) n d omega N _ hU,
    P4AOriginalOrderedSixthStages.ten_is_original_parent]
  rfl

end
end ImbalancedChen.P4AOriginalFull87UpperDispatch
