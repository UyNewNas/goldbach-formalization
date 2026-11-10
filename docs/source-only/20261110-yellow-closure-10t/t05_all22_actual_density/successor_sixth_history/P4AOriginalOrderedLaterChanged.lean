import ImbalancedChen.P4AOriginalLaterSixthHistoryRows
import ImbalancedChen.P4AOriginalOrderedSixthSigned
import ImbalancedChen.P4AOriginalSixthClosedQuotients

/-! An actual changed word has a winning later-action row. Therefore both
ordinary quotient arguments lie in the same closed cube window. The
entire contribution outside the fixed positive six-prime box is zero. -/
namespace ImbalancedChen.P4AOriginalOrderedLaterChanged
noncomputable section
open Set VariableEnvelope
open scoped Classical BigOperators
open P4AOriginalOrderedSixthStages (level orderedLevel policy finiteAt rawAt laterLicensed)
open P4AOriginalOrderedThirdFullPolicy (Root current accepted after)
open P4AOriginalSixthLaterLiteral (Cell stage)
open P4AOriginalSixthLaterSemantics (Source endpoint comparison)
open P4AOriginalCompleteSixthChronology (laterEligible applyLater)
open P4AOriginalOrderedSixthSigned (admitted tupleResidual admitted_floor)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalSavedSixthHistoricalOwner (pre_log)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P1OriginalVariableFourthContinuation (finiteMax finiteValues)
open P1GuardFrozenFiniteCapAlgebra (rounded)
open Certificates.P2OriginalSixthElevenLogSemantics (S6)
open P4AOriginalSixthClosedQuotients (low high low_pos)

def rowTest (k n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) (c : Cell) : Prop :=
  if R.lower then stage c=k ∧ accepted R d N n h (.later c)
  else laterEligible k (after R d N h k) N c h
def rowValue (n : ℕ) (R : Root) (N : ℝ) (h : List ℕ) (c : Cell) : ℝ :=
  let E := endpoint c (primeHistoryLogCoordinates N 6 h)
  if R.lower then (rounded n E:ℝ) else E

theorem step_form (k n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    level (k+3) n R d N h=finiteMax Finset.univ (rowTest k n R d N h)
      (rowValue n R N h) (level (k+2) n R d N h) := by
  by_cases hr : R.lower <;> simp only [level,rowTest,rowValue,hr,if_true,if_false,
    finiteAt,rawAt,laterLicensed,after,applyLater,P4AOriginalOrderedSixthStages.value,
    P4AOriginalSixthActionBank.endpoint]

theorem test_source {k n : ℕ} {R : Root} {d : OriginalData} {N : ℝ} {h : List ℕ} {c : Cell}
    (hc : rowTest k n R d N h c) :
    stage c=k ∧ Source c (primeHistoryLogCoordinates N 6 h) := by
  by_cases hr : R.lower
  · rw [rowTest,if_pos hr] at hc
    exact ⟨hc.1,hc.2.1.2.2.1⟩
  · rw [rowTest,if_neg hr] at hc
    exact ⟨hc.2.1,hc.2.2.1⟩

theorem value_le_raw {k n : ℕ} {R : Root} {d : OriginalData} {N : ℝ} {h : List ℕ} {c : Cell}
    (hc : rowTest k n R d N h c) : rowValue n R N h c≤endpoint c (primeHistoryLogCoordinates N 6 h) := by
  by_cases hr : R.lower
  · rw [rowValue,if_pos hr]
    let t := primeHistoryLogCoordinates N 6 h
    have hs := (test_source hc).2
    have h0 := (P4AOriginalSixthSquareRows.later_comparison_half c t hs).trans
      (P4AOriginalLaterSixthHistoryRows.source_margins c t hs).2.2.2.1
    have hcap := (P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent c t hs).le.trans (v_le_cap _)
    exact (P1GuardFrozenFiniteCapAlgebra.rounded_error n _ (by linarith) hcap).2.2
  · simp only [rowValue,if_neg hr,le_refl]

theorem changed_owner (k n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ)
    (hc : level (k+2) n R d N h<level (k+3) n R d N h) :
    ∃ c : Cell,stage c=k ∧ Source c (primeHistoryLogCoordinates N 6 h) ∧
      level (k+3) n R d N h≤endpoint c (primeHistoryLogCoordinates N 6 h) := by
  rw [step_form] at hc ⊢
  let E := rowTest k n R d N h
  let V := rowValue n R N h
  let P := level (k+2) n R d N h
  have hm : finiteMax Finset.univ E V P∈finiteValues Finset.univ E V P := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with he|he
  · exact False.elim ((ne_of_gt hc) he)
  · obtain ⟨c,hc',heq⟩ := Finset.mem_image.mp he
    have hh := (Finset.mem_filter.mp hc').2
    exact ⟨c,(test_source hh).1,(test_source hh).2,heq ▸ value_le_raw hh⟩

def window : Set (Fin 6→ℝ) := logPrimeBox (fun _=>low) (fun _=>high)

theorem source_in_window {c : Cell} {t : Fin 6→ℝ} (hs : Source c t) : t∈window := by
  obtain ⟨hx,_,hr,ho⟩ := P4AOriginalSixthSquareRows.later_source_basic c t hs
  apply mem_logPrimeBox.mpr
  intro j
  exact ⟨hr.le.trans (ho.antitone (show j≤(5:Fin 6) from Fin.le_last _)),
    (ho.antitone (Fin.zero_le j)).trans_lt (hx.trans (by norm_num [high]))⟩

theorem outside_zero (k n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (p : Fin 6→ℕ)
    (hh : actualPrimeTupleLog N p∉window) : tupleResidual (k+2) n d omega N cap p=0 := by
  let h := pre p
  let R := current d omega N h
  have hm := P4AOriginalOrderedSixthStages.level_mono n R d N h (show k+2≤k+3 by omega)
  have he : level (k+2) n R d N h=level (k+3) n R d N h := by
    by_contra hn
    obtain ⟨c,_,hc,_⟩ := changed_owner k n R d N h (lt_of_le_of_ne hm hn)
    apply hh
    apply source_in_window (c:=c)
    simpa only [h,pre_log] using hc
  change actualPrimeTupleInitialSaving N cap (level (k+2) n R d N h) (level (k+3) n R d N h) p=0
  simp only [he,actualPrimeTupleInitialSaving,sub_self,zero_mul,zero_div]

theorem whole_admitted_negative (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ k n : ℕ,∀ d : OriginalData,∀ omega : ℝ,
    ∀ cap : ℕ,∀ z : ℝ,∀ p : Fin 6→ℕ,p∈admitted n d omega N cap z →
      -eta<tupleResidual (k+2) n d omega N cap p := by
  obtain ⟨N0,hn0,hh⟩ := P4AOriginalSixthClosedQuotients.difference_lower eta heta
  refine ⟨N0,hn0,?_⟩
  intro N hN hev k n d omega cap z p hpa
  let t := actualPrimeTupleLog N p
  let h := pre p
  let R := current d omega (N:ℝ) h
  let P := level (k+2) n R d N h
  let M := level (k+3) n R d N h
  have hm : P≤M := P4AOriginalOrderedSixthStages.level_mono n R d N h (show k+2≤k+3 by omega)
  change -eta<actualPrimeTupleInitialSaving N cap P M p
  by_cases heq : P=M
  · simp only [heq,actualPrimeTupleInitialSaving,sub_self,zero_mul,zero_div,neg_lt_zero,heta]
  · obtain ⟨c,_,hsrc,hM⟩ := changed_owner k n R d N h (lt_of_le_of_ne hm heq)
    change Source c (primeHistoryLogCoordinates (N:ℝ) 6 (pre p)) at hsrc
    rw [pre_log] at hsrc
    change M≤endpoint c (primeHistoryLogCoordinates (N:ℝ) 6 (pre p)) at hM
    rw [pre_log] at hM
    obtain ⟨hx,hr,hl,ho⟩ := P4AOriginalSixthSquareRows.later_source_basic c t hsrc
    obtain ⟨hp,_,_,hw,_⟩ := admitted_floor (k+2) n d omega N cap z (show 1<N by omega) p hpa
    have hres : t 5≤P-S6 t := by
      have h45 := ho (show (4:Fin 6)<5 by decide)
      change 2*(t 4-t 5)<P-S6 t-t 5 at hw
      linarith
    have hlist := ((mem_firstExitAdmittedTuples_iff 6 _ _ p).mp hpa).1
    have hcap : p 5≤cap := (mem_roughPrimeUniverse.mp (hlist.subset (List.mem_ofFn.mpr ⟨5,rfl⟩))).1
    have hM' := (P4AOriginalLaterSixthHistoryRows.source_margins c t hsrc).2.2.2.2
    exact hh N hN hev p (fun j=>(hp j).pos) P M hl.le (hr.le.trans (by norm_num [high]))
      hres hm ((sub_le_sub_right hM _).trans hM'.le) cap hcap

end
end ImbalancedChen.P4AOriginalOrderedLaterChanged
