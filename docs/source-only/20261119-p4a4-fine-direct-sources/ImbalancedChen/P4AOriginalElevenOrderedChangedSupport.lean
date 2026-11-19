import ImbalancedChen.P4AOriginalOrderedSixthSigned
import ImbalancedChen.P4AOriginalSixthClosedQuotients
import ImbalancedChen.P4AOriginalElevenPrimeOccurrence

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
This is the ACTUAL updated whole-third/R17 fifth frontier, for arbitrary
late omega and every admitted word, including all words outside every
archived trim. A strict change has an actual original G7 winning row.
The existing closed quotient theorem pays a uniformly small negative
error on the ENTIRE changed support. No finite cap monotonicity, compact
owner transfer or assumed boundary-payment licence is used.
-/
namespace ImbalancedChen.P4AOriginalElevenOrderedChangedSupport
noncomputable section
open VariableEnvelope
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (Root accepted eleven)
open P4AOriginalOrderedSixthStages (level orderedLevel)
open P4AOriginalSavedSixthSigned (pre)
open Certificates.P2OriginalSixthElevenLogSemantics (Cell PhysicalCell newCap S6)
open P1OriginalVariableFourthContinuation (finiteMax finiteValues finiteValues_nonempty)

def rowEligible (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) (c : Cell) : Prop :=
  if R.lower then accepted R d N n h (.eleven c) else eleven R d N c h
def rowValue (n : ℕ) (R : Root) (N : ℝ) (h : List ℕ) (c : Cell) : ℝ :=
  if R.lower then (P1GuardFrozenFiniteCapAlgebra.rounded n (newCap c (primeHistoryLogCoordinates N 6 h)):ℝ)
  else newCap c (primeHistoryLogCoordinates N 6 h)

theorem g7_step_form (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    level 2 n R d N h=finiteMax Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
      (rowEligible n R d N h) (rowValue n R N h) (level 1 n R d N h) := by
  by_cases hl : R.lower <;>
    simp only [level,hl,if_true,if_false,P4AOriginalOrderedSixthStages.finiteAt,
      P4AOriginalOrderedSixthStages.rawAt,P4AOriginalOrderedSixthStages.laterLicensed,
      P4AOriginalOrderedSixthStages.savedLicensed,P4AOriginalOrderedSixthStages.savedRaw,
      P4AOriginalOrderedSixthStages.value,P4AOriginalOrderedThirdFullPolicy.after,rowEligible,rowValue,
      P4AOriginalSixthActionBank.endpoint]

theorem row_source {n : ℕ} {R : Root} {d : OriginalData} {N : ℝ} {h : List ℕ} {c : Cell}
    (hc : rowEligible n R d N h c) : PhysicalCell c (primeHistoryLogCoordinates N 6 h) := by
  by_cases hl : R.lower
  · rw [rowEligible,if_pos hl] at hc
    exact hc.1.2.1
  · rw [rowEligible,if_neg hl] at hc
    exact hc.2.1

theorem row_value_le_raw {n : ℕ} {R : Root} {d : OriginalData} {N : ℝ} {h : List ℕ} {c : Cell}
    (hc : rowEligible n R d N h c) : rowValue n R N h c≤newCap c (primeHistoryLogCoordinates N 6 h) := by
  by_cases hl : R.lower
  · rw [rowValue,if_pos hl]
    have hs := row_source hc
    have hp := P4AOriginalSixthActionBank.geometric_lower_license (.eleven c) _ hs none
    change (1/2:ℝ)<newCap c (primeHistoryLogCoordinates N 6 h) at hp
    have hu := (P4AOriginalSixthActionBank.geometric_upper_license (.eleven c) _ hs).trans (v_le_cap _)
    exact (P1GuardFrozenFiniteCapAlgebra.rounded_error n _ (by linarith) hu).2.2
  · rw [rowValue,if_neg hl]

/-- The maximum really attains a G7 row whenever the seed changes. The
row's original PhysicalCell and raw endpoint are derived, not inputs. -/
theorem changed_owner (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ)
    (hchange : level 1 n R d N h<level 2 n R d N h) :
    ∃ c : Cell, PhysicalCell c (primeHistoryLogCoordinates N 6 h) ∧
      level 2 n R d N h≤newCap c (primeHistoryLogCoordinates N 6 h) := by
  rw [g7_step_form] at hchange ⊢
  let rows := Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
  let E := rowEligible n R d N h
  let V := rowValue n R N h
  let P := level 1 n R d N h
  have hm : finiteMax rows E V P∈finiteValues rows E V P :=
    Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact False.elim ((ne_of_gt hchange) hm)
  · obtain ⟨c,hc,heq⟩ := Finset.mem_image.mp hm
    have he := (Finset.mem_filter.mp hc).2
    exact ⟨c,row_source he,heq ▸ row_value_le_raw he⟩

/-- A uniform lower error for ALL admitted words on the corrected tree.
No small-e, supported-owner, compact trim or original-cell hypothesis is
required. Unchanged words have exactly zero residual difference. -/
theorem exists_whole_ordered_G7_negative_error (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ n : ℕ,∀ d : OriginalData,∀ omega : ℝ,
    ∀ cap : ℕ,∀ z : ℝ,∀ p : Fin 6→ℕ,
    p∈P4AOriginalOrderedSixthSigned.admitted n d omega N cap z →
      -eta<P4AOriginalOrderedSixthSigned.tupleResidual 1 n d omega N cap p := by
  obtain ⟨N0,h0,hbound⟩ := P4AOriginalSixthClosedQuotients.difference_lower eta heta
  refine ⟨N0,h0,?_⟩
  intro N hN hev n d omega cap z p hp
  let R := P4AOriginalOrderedThirdFullPolicy.current d omega (N:ℝ) (pre p)
  let P := orderedLevel 1 n d omega (N:ℝ) (pre p)
  let M := orderedLevel 2 n d omega (N:ℝ) (pre p)
  let t := actualPrimeTupleLog N p
  have hPM : P≤M := P4AOriginalOrderedSixthStages.level_mono n R d (N:ℝ) (pre p) (by decide : 1≤2)
  change -eta<actualPrimeTupleInitialSaving N cap P M p
  by_cases heq : P=M
  · rw [heq]
    simp only [actualPrimeTupleInitialSaving,sub_self,zero_mul,zero_div]
    linarith
  · have hchange : P<M := lt_of_le_of_ne hPM heq
    obtain ⟨c,hc,hM⟩ := changed_owner n R d (N:ℝ) (pre p) hchange
    rw [P4AOriginalElevenPrimeOccurrence.pre_log] at hc hM
    have hN1 : 1<N := by omega
    obtain ⟨hprime,ho,hH5,hwedge,hquot⟩ :=
      P4AOriginalOrderedSixthSigned.admitted_floor 1 n d omega N cap z hN1 p hp
    have hres : t 5≤P-S6 t := by linarith [hc.order.1]
    have hupper : t 5≤P4AOriginalSixthClosedQuotients.high := by
      have hh := hc.oldCutoff.le
      change t 5≤1/5
      linarith
    have hlist := ((mem_firstExitAdmittedTuples_iff 6
      (P4AOriginalOrderedSixthStages.orderedFifth n d omega (N:ℝ))
      (roughPrimeUniverse N cap 0 z) p).mp hp).1
    have hcap : p 5≤cap :=
      (mem_roughPrimeUniverse.mp (hlist.subset (List.mem_ofFn.mpr ⟨5,rfl⟩))).1.le
    exact hbound N hN hev p (fun j => (hprime j).pos) P M hc.compactCutoff.le hupper hres hPM
      ((sub_le_sub_right hM _).trans hc.newArgument.le) cap hcap

end
end ImbalancedChen.P4AOriginalElevenOrderedChangedSupport
