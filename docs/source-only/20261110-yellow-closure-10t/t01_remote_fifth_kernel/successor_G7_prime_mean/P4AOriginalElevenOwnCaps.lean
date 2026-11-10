import ImbalancedChen.P4AOriginalElevenPrimeOccurrence

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The original comparison tie walls are genuinely null. Away from them an
original G7 source has a unique actual cell, so its G7 stage is precisely
its own rounded endpoint, on the same protected fifth predecessor. This
is the moving-cap input for the subsequent actual prime mean; no limit
or payment estimate is assumed here.
-/
namespace ImbalancedChen.P4AOriginalElevenOwnCaps
noncomputable section
open Set MeasureTheory VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthMomentRow (Point)
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthPullingUnion (eval affine_zero_volume)
open P2OriginalSixthPhysicalGateRows (old eval_sub)
open P2OriginalSixthCrossCellOwnership (comparisonKind comparison_eq eval_old
  affine_nonzero_of_coefficient distinct_comparison_coefficients same_comparison_disjoint)
open P2OriginalSixthCompactTrim (trim trim_subset_source)
open P4AOriginalElevenActualCommonHistory (bank root ActualHistory)
open P1GuardFrozenFiniteCapAlgebra (rounded)
open P4AOriginalFull87HistoryCore (width)
open Certificates.P2OriginalSixthElevenLogSemantics (PhysicalCell oldCap newCap S6 newResidual)

def comparisonTies : Set Point := ⋃ i : Fin 11, ⋃ j : Fin 11,
  if comparisonKind (sourceCell i)=comparisonKind (sourceCell j) then ∅
  else {t | eval (old (sourceCell i)-old (sourceCell j)) t=0}

theorem comparison_ties_null : volume comparisonTies=0 := by
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases hij : comparisonKind (sourceCell i)=comparisonKind (sourceCell j)
  · simp [hij]
  · simp only [if_neg hij]
    exact affine_zero_volume _ (affine_nonzero_of_coefficient (distinct_comparison_coefficients _ _ hij))

theorem sourceCell_surjective : Function.Surjective sourceCell := by
  intro c
  cases c <;> decide

theorem unique_original_source (i : Fin 11) {t : Point} (hc : PhysicalCell (sourceCell i) t)
    (ht : t∉comparisonTies) (c : Certificates.P2OriginalSixthElevenLogSemantics.Cell)
    (hd : PhysicalCell c t) : c=sourceCell i := by
  obtain ⟨j,rfl⟩ := sourceCell_surjective c
  by_contra hne
  by_cases hk : comparisonKind (sourceCell i)=comparisonKind (sourceCell j)
  · exact Set.disjoint_left.mp (same_comparison_disjoint hk (Ne.symm hne)) hc hd
  · apply ht
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,?_⟩⟩
    simp only [if_neg hk,mem_setOf_eq,eval_sub,eval_old,comparison_eq hc hd,sub_self]

theorem own_cap_eq_rounded (n : ℕ) {e : ℚ} {q : ℕ} {a N : ℝ} {pre : List ℕ} {i : Fin 11}
    (hc : PhysicalCell (sourceCell i) (primeHistoryLogCoordinates N 6 pre))
    (ht : primeHistoryLogCoordinates N 6 pre∉comparisonTies)
    (ha : P4AOriginalFull87DataPolicy.active (bank e q a) N pre)
    (hacc : P4AOriginalFull87DataPolicy.Accepted n (bank e q a) N pre (.eleven (sourceCell i)))
    (hparent : P4AOriginalSavedSixthStage.level n (bank e q a) N pre<
      (rounded n (newCap (sourceCell i) (primeHistoryLogCoordinates N 6 pre)):ℝ)) :
    P4AOriginalElevenSixthStage.level n (bank e q a) N pre=
      (rounded n (newCap (sourceCell i) (primeHistoryLogCoordinates N 6 pre)):ℝ) := by
  apply le_antisymm
  · rw [P4AOriginalElevenSixthStage.level,if_pos ha]
    apply P1OriginalVariableFourthContinuation.finiteMax_le _ _ _ _ _ hparent.le
    intro c _ hrow
    have hs : PhysicalCell c (primeHistoryLogCoordinates N 6 pre) := hrow.1.2.1
    have he := unique_original_source i hc ht c hs
    subst c
    exact le_rfl
  · exact P4AOriginalElevenSixthStage.accepted_lower n (bank e q a) N pre (sourceCell i) ha hacc

/-- The exact moving caps, old residual and unchanged new3r ceiling
are derived on each real original owner. All cells and actual fifth
rows are retained; only the proper comparison ties are excluded. -/
theorem exists_original_G7_own_caps (delta : ℝ) (hdelta : 0<delta) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0≤n → ∃ e0 : ℝ, 0<e0 ∧
    ∀ e : ℚ, 0<e → (e:ℝ)<e0 → ∃ q0 : ℕ, 0<q0 ∧ ∀ q : ℕ, q0≤q →
    ∀ a : ℝ, a≤1/100 → ∀ N : ℝ, 1<N → ∀ pre : List ℕ,
    pre.length=6 → (∀ p∈pre,0<p) → ∀ i : Fin 11,
    primeHistoryLogCoordinates N 6 pre∈trim i delta →
    primeHistoryLogCoordinates N 6 pre∉comparisonTies →
      let t := primeHistoryLogCoordinates N 6 pre
      let P := P4AOriginalSavedSixthStage.level n (bank e q a) N pre
      let M := P4AOriginalElevenSixthStage.level n (bank e q a) N pre
      M=(rounded n (newCap (sourceCell i) t):ℝ) ∧ P≤oldCap (sourceCell i) t ∧
      oldCap (sourceCell i) t+delta/2<M ∧ t 5<P-S6 t ∧ M-S6 t<3*t 5 ∧ M≤newCap (sourceCell i) t := by
  obtain ⟨nH,hH⟩ := P4AOriginalElevenAcceptedCaps.exists_joined_G7_history_and_caps delta hdelta
  obtain ⟨nQ,hQ⟩ := P4AOriginalElevenAcceptedCaps.exists_uniform_rounded_geometry hdelta
  refine ⟨max nH nQ,?_⟩
  intro n hn
  have hnH := (le_max_left nH nQ).trans hn
  have hnQ := (le_max_right nH nQ).trans hn
  obtain ⟨e0,he0,hE⟩ := hH n hnH
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq⟩ := hE e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq a ha N hN pre hlen hp i ht hties
  obtain ⟨hist,hacc,hroot,hparent,hgain⟩ := hq q hqq a ha N hN pre hlen hp i ht
  obtain ⟨_,_,hown,hu⟩ := hQ n hnQ i _ ht
  have hc := trim_subset_source i hdelta ht
  have hactive : P4AOriginalFull87DataPolicy.active (bank e q a) N pre := by
    refine ⟨?_,hist.2.1⟩
    rw [← P4AOriginalElevenActualCommonHistory.firstThree_ancestor N pre hlen]
    exact hc.largest.le
  have hP : P4AOriginalSavedSixthStage.level n (bank e q a) N pre<
      (rounded n (newCap (sourceCell i) (primeHistoryLogCoordinates N 6 pre)):ℝ) := by linarith
  have heq := own_cap_eq_rounded n hc hties hactive hacc hP
  rcases hist with ⟨hstop,hsup,hseed,hfirst,hthird,hfifth,hres,hLE,hER⟩
  refine ⟨heq,hparent,hgain,?_,?_,?_⟩
  · linarith
  · rw [heq]
    have hh := hc.newArgument
    exact (sub_le_sub_right hu _).trans_lt hh
  · rw [heq]
    exact hu

end
end ImbalancedChen.P4AOriginalElevenOwnCaps
