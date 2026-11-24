import ImbalancedChen.P4AOriginalElevenActualCommonHistory

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The existing G7 lower-licence and continuous-gate theorems supply a genuine
uniform positive margin on every original compact trim. The unchanged
biased finite quantizer then passes the actual Accepted guard. No licence,
fixed-parent bound, cap table or numerical saving is assumed by the final
joined schedule theorem. Every real old+new fifth row remains in the bank.
-/
namespace ImbalancedChen.P4AOriginalElevenAcceptedCaps
noncomputable section
open Set Filter VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthCompactTrim (trim trim_compact trim_subset_source strict_margin)
open P4AOriginalElevenActualCommonHistory (bank root ActualHistory)
open P5OriginalCommonRefinedConstructor (OriginalData actualParent5 originalSeed)
open P1GuardFrozenFiniteCapAlgebra (rounded rounded_error protect protect_error)
open P4AOriginalFull87HistoryCore (width width_pos)
open P1QuantizedActionLicense (LowerLicense rounded_licensed)
open Certificates.P2OriginalSixthElevenLogSemantics (PhysicalCell oldCap newCap)

theorem exists_uniform_lower_margin {delta : ℝ} (hdelta : 0<delta) :
    ∃ eta : ℝ, 0<eta ∧ ∀ i : Fin 11, ∀ t∈trim i delta,
      ∀ g : P1QuantizedActionLicense.Gate 6,
      P1QuantizedActionLicense.gate (P4AOriginalSixthActionBank.selected (.eleven (sourceCell i))) t g+eta≤
        newCap (sourceCell i) t := by
  have hf (i : Fin 11) (g : P1QuantizedActionLicense.Gate 6) :
      ∃ eta : ℝ, 0<eta ∧ ∀ t∈trim i delta, eta≤newCap (sourceCell i) t-
        P1QuantizedActionLicense.gate (P4AOriginalSixthActionBank.selected (.eleven (sourceCell i))) t g := by
    apply (trim_compact i delta).exists_forall_le'
    · exact ((P4AOriginalSixthActionBank.endpoint_continuous (.eleven (sourceCell i))).sub
        (P4AOriginalSixthActionBank.gate_continuous (.eleven (sourceCell i)) g)).continuousOn
    · intro t ht
      exact sub_pos.mpr (P4AOriginalSixthActionBank.geometric_lower_license
        (.eleven (sourceCell i)) t (trim_subset_source i hdelta ht) g)
  choose eta heta hfloor using hf
  obtain ⟨a,ha,hmin⟩ := P1QuantizedActionLicense.exists_positive_floor
    (Finset.univ : Finset (Fin 11 × P1QuantizedActionLicense.Gate 6)) (fun _ => True)
    (fun z => eta z.1 z.2) (fun z _ _ => heta z.1 z.2)
  refine ⟨a,ha,?_⟩
  intro i t ht g
  have h1 := hmin (i,g) (Finset.mem_univ _) trivial
  have h2 := hfloor i g t ht
  linarith

theorem exists_uniform_rounded_geometry {delta : ℝ} (hdelta : 0<delta) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0≤n → ∀ i : Fin 11, ∀ t∈trim i delta,
      LowerLicense (P4AOriginalSixthActionBank.selected (.eleven (sourceCell i))) t
        (rounded n (newCap (sourceCell i) t):ℝ) ∧
      (rounded n (newCap (sourceCell i) t):ℝ)+width n≤
        v (∑ j∈P4AOriginalSixthActionBank.selected (.eleven (sourceCell i)),t j) ∧
      oldCap (sourceCell i) t+delta/2<(rounded n (newCap (sourceCell i) t):ℝ) ∧
      (rounded n (newCap (sourceCell i) t):ℝ)≤newCap (sourceCell i) t := by
  obtain ⟨eta,heta,hg⟩ := exists_uniform_lower_margin hdelta
  obtain ⟨n0,hn0⟩ := P1QuantizedActionLicense.exists_resolution (min eta delta) (lt_min heta hdelta)
  refine ⟨n0,?_⟩
  intro n hn i t ht
  have hc := trim_subset_source i hdelta ht
  let a := P4AOriginalSixthActionBank.Action.eleven (sourceCell i)
  have hlow := P4AOriginalSixthActionBank.geometric_lower_license a t hc
  have hu := P4AOriginalSixthActionBank.geometric_upper_license a t hc
  have hcap : newCap (sourceCell i) t≤cap := hu.trans (v_le_cap _)
  have hh := hlow none
  change (1/2:ℝ)<newCap (sourceCell i) t at hh
  have hpos : 0≤newCap (sourceCell i) t := by linarith
  have hneta : 4*width n<eta := by have hx := hn0 n hn; have hm := min_le_left eta delta; linarith [width_pos n]
  have hndelta : 4*width n<delta := by have hx := hn0 n hn; have hm := min_le_right eta delta; linarith [width_pos n]
  have hr := rounded_licensed n (P4AOriginalSixthActionBank.selected a) t
    (newCap (sourceCell i) t) eta heta hcap (hg i t ht) hneta
  have he := rounded_error n (newCap (sourceCell i) t) hpos hcap
  have hgap := strict_margin ht .positiveGap rfl
  change delta≤newCap (sourceCell i) t-oldCap (sourceCell i) t at hgap
  refine ⟨?_,hr.2.trans hu,by linarith [he.1],he.2.2⟩
  intro g
  have h := hr.1 g
  linarith

theorem actual_level5_bounds (n : ℕ) {e : ℚ} {q : ℕ} {a N : ℝ} {pre : List ℕ}
    {i : Fin 11} (hlen : pre.length=6) (hc : PhysicalCell (sourceCell i) (primeHistoryLogCoordinates N 6 pre))
    (hh : ActualHistory e q a N pre i) :
    root (bank e q a) N pre≤P4AOriginalFull87DataPolicy.level5Exponent n (bank e q a) N (rosserAncestor 5 pre) ∧
    P4AOriginalFull87DataPolicy.level5Exponent n (bank e q a) N (rosserAncestor 5 pre)≤
      oldCap (sourceCell i) (primeHistoryLogCoordinates N 6 pre) := by
  let d := bank e q a
  let t := primeHistoryLogCoordinates N 6 pre
  rcases hh with ⟨hstop,hsup,hseed,hfirst,hh3,hh5,hres,hLE,hER⟩
  have hactive : P4AOriginalFull87DataPolicy.active d N pre := by
    refine ⟨?_,hsup⟩
    rw [← P4AOriginalElevenActualCommonHistory.firstThree_ancestor N pre hlen]
    exact hc.largest.le
  have ha5 := (P4AOriginalFull87DataPolicy.active_ancestor d N 5 (by decide) pre).mpr hactive
  have hp0 := hc.coordinates_pos (0:Fin 6)
  have hroot : 0≤root d N pre := by linarith
  have hcap : actualParent5 d N pre≤cap := hER.trans (P2OriginalSixthCrossCellOwnership.oldCap_lt_peak hc).le
  have hp := protect_error n (root d N pre) (actualParent5 d N pre) hroot hLE hcap
  have hform : P4AOriginalFull87DataPolicy.level5Exponent n d N (rosserAncestor 5 pre)=
      protect n (root d N pre) (actualParent5 d N pre) := by
    rw [P4AOriginalFull87DataPolicy.level5Exponent,if_pos ha5,
      P4AOriginalFull87DataPolicy.cap5_eq_protect,
      P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 5 (by decide),← hseed]
    rfl
  rw [hform]
  exact ⟨hp.1,hp.2.2.trans hER⟩

/-- The same trim determines histories first, then the ACTUAL unchanged
guard is discharged at the actual d+ parent. No new row test is invented. -/
theorem exists_joined_G7_history_and_caps (delta : ℝ) (hdelta : 0<delta) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0≤n → ∃ e0 : ℝ, 0<e0 ∧
    ∀ e : ℚ, 0<e → (e:ℝ)<e0 → ∃ q0 : ℕ, 0<q0 ∧ ∀ q : ℕ, q0≤q →
    ∀ a : ℝ, a≤1/100 → ∀ N : ℝ, 1<N →
    ∀ pre : List ℕ, pre.length=6 → (∀ p∈pre,0<p) → ∀ i : Fin 11,
    primeHistoryLogCoordinates N 6 pre∈trim i delta →
      ActualHistory e q a N pre i ∧
      P4AOriginalFull87DataPolicy.Accepted n (bank e q a) N pre (.eleven (sourceCell i)) ∧
      root (bank e q a) N pre≤P4AOriginalSavedSixthStage.level n (bank e q a) N pre ∧
      P4AOriginalSavedSixthStage.level n (bank e q a) N pre≤
        oldCap (sourceCell i) (primeHistoryLogCoordinates N 6 pre) ∧
      oldCap (sourceCell i) (primeHistoryLogCoordinates N 6 pre)+delta/2<
        P4AOriginalElevenSixthStage.level n (bank e q a) N pre := by
  obtain ⟨n0,hn0⟩ := exists_uniform_rounded_geometry hdelta
  obtain ⟨e0,he0,hH⟩ := P4AOriginalElevenActualCommonHistory.exists_original_G7_common_history delta hdelta
  refine ⟨n0,?_⟩
  intro n hn
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hQ⟩ := hH e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha N hN pre hlen hp i ht
  let d := bank e q a
  have hc := trim_subset_source i hdelta ht
  have hh := hQ q hq a ha N hN pre hlen hp i ht
  obtain ⟨hlow,hupper,hgain,_⟩ := hn0 n hn i _ ht
  have hlic : P5OriginalCommonRefinedConstructor.eligibleSixth d N (sourceCell i) pre := by
    rcases hh with ⟨hstop,hsup,hseed,hfirst,hh3,hh5,hres,hLE,hER⟩
    exact ⟨hlen,hc,hh5.trans_le hLE,hER⟩
  have hacc : P4AOriginalFull87DataPolicy.Accepted n d N pre (.eleven (sourceCell i)) :=
    ⟨hlic,hlow,hupper⟩
  have ha' : P4AOriginalFull87DataPolicy.active d N pre := by
    refine ⟨?_,hh.2.1⟩
    rw [← P4AOriginalElevenActualCommonHistory.firstThree_ancestor N pre hlen]
    exact hc.largest.le
  have h5 := actual_level5_bounds n hlen hc hh
  have hpred := P4AOriginalElevenSixthStage.predecessor_on_original_source n d N pre (sourceCell i) hc
  rw [← hpred] at h5
  have hnew := P4AOriginalElevenSixthStage.accepted_lower n d N pre (sourceCell i) ha' hacc
  exact ⟨hh,hacc,h5.1,h5.2,hgain.trans_le hnew⟩

end
end ImbalancedChen.P4AOriginalElevenAcceptedCaps
