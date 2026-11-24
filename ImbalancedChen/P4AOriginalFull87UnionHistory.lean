import ImbalancedChen.P4AOriginalFull87DataPolicy
import ImbalancedChen.P4AOriginalFull87ActualGain
import ImbalancedChen.P4AOriginalNewFifthUnion

/-! Admission and residuals for the original enlarged fifth bank.
Every sixth action checks its predecessor on this bank. The original
third history and the eight-dimensional source and trims are shared. -/
namespace ImbalancedChen.P4AOriginalFull87UnionHistory
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope Set MeasureTheory
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87HistoryCore (width width_pos oldHistory)
open P4AOriginalFull87SevenCubeAdmission (point pre pre_length pre_pairwise source_strictAnti seven_admissible_of_histories)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87FiniteEighthCap (finiteCap finiteCap_licensed finiteCap_upper)
open P4AOriginalFull87DataPolicy (Accepted)
open P5OriginalCommonRefinedConstructor (lambda3 exponent5)
open P1OriginalVariableFourthContinuation (finiteMax_le)
open P1GuardFrozenFiniteCapAlgebra (protect_error)

abbrev bank := P4AOriginalNewFifthUnion.data
abbrev oldBank := P4AOriginalCompleteSixthChronology.data
abbrev level6Exponent (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) := P4AOriginalFull87DataPolicy.level6Exponent n (bank e q om) N
abbrev actualParent (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) := P4AOriginalFull87DataPolicy.actualParent n (bank e q om) N
abbrev fifthPolicy (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) := P4AOriginalFull87DataPolicy.fifthPolicy n (bank e q om) N
abbrev sixthPolicy (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) := P4AOriginalFull87DataPolicy.sixthPolicy n (bank e q om) N
abbrev policy (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) := P4AOriginalFull87DataPolicy.policy delta n (bank e q om) N

theorem source_active {e : ℚ} {q : ℕ} {om N : ℝ} {h : List ℕ} (hlen : h.length = 8)
    {c : Cell} (hs : Source c (primeHistoryLogCoordinates N 8 h)) (hr : RealizedHistory e q om N h c) :
    P4AOriginalFull87DataPolicy.active (bank e q om) N h :=
  P4AOriginalFull87FiniteParentPolicy.source_active e q om N h hlen c hs hr

theorem raw_current_le_comparison (e : ℚ) (q : ℕ) (om N : ℝ) (he : 0 ≤ e)
    (h : List ℕ) (hlen : h.length = 8) (c : Cell) (hs : Source c (primeHistoryLogCoordinates N 8 h))
    (hr : RealizedHistory e q om N h c) :
    P4AOriginalFull87DataPolicy.currentSixthExponent (bank e q om) N (rosserAncestor 6 h) ≤
      comparison c (primeHistoryLogCoordinates N 8 h) := by
  apply P4AOriginalFull87DataPolicy.current_le_of_subset_tents
  · exact P4AOriginalNewFifthUnion.union_fifth_le_original_comparison e q om N he h hlen c hs hr.2.1
  · intro m hm
    have hc : primeHistoryLogCoordinates N 6 (rosserAncestor 6 h) =
        P4AOriginalFull87CompleteSixthBound.firstSix (primeHistoryLogCoordinates N 8 h) := by
      funext i
      exact primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i
    rw [hc]
    exact P4AOriginalFull87CompleteSixthBound.source_sixth_tents c _ hs m hm

/-- The updated fifth producer has the unchanged actual third below it
and the original all-subset comparison above it on its own ancestor. -/
theorem fifth_bounds (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (he : 0 ≤ e)
    (h : List ℕ) (hlen : h.length = 8) (c : Cell) (hs : Source c (primeHistoryLogCoordinates N 8 h))
    (hr : RealizedHistory e q om N h c) :
    lambda3 (oldBank e q om) N (rosserAncestor 4 h) ≤
      P4AOriginalFull87DataPolicy.cap5 n (bank e q om) N (rosserAncestor 5 h) ∧
    P4AOriginalFull87DataPolicy.cap5 n (bank e q om) N (rosserAncestor 5 h) ≤
      comparison c (primeHistoryLogCoordinates N 8 h) := by
  let d := bank e q om
  let L := lambda3 d N (rosserAncestor 4 h)
  let E := exponent5 d N (rosserAncestor 5 h)
  have hL : 0 < L :=
    (P4AOriginalFull87FiniteParentCaps.parent_bounds_of_history n e q om N h hlen c hs hr).1
  have hLE : L ≤ E := by
    change lambda3 d N (rosserAncestor 4 h) ≤ exponent5 d N (rosserAncestor 5 h)
    rw [P5OriginalCommonRefinedPreservation.lambda3_ancestor d N 4 (by decide),
      ← P5OriginalCommonRefinedPreservation.lambda3_ancestor d N 5 (by decide) h]
    exact P5OriginalCommonRefinedPreservation.lambda3_le_exponent5 d N _
  have hER : E ≤ comparison c (primeHistoryLogCoordinates N 8 h) := by
    have hh := P4AOriginalNewFifthUnion.union_fifth_le_original_comparison e q om N he h hlen c hs hr.2.1
    simpa only [P5OriginalCommonRefinedConstructor.actualParent5,rosserAncestor_nested 5 6 (by decide)] using hh
  have hcap := hER.trans ((source_improvement_terminal hs).1.le.trans (source_physical_ceiling hs).le)
  have hprotected := protect_error n L E hL.le hLE hcap
  have hseed := P4AOriginalFull87CompleteSixthBound.actual_third_eq_original d N _ hlen c hs
  rw [P4AOriginalFull87DataPolicy.cap5_eq_protect,
    P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 5 (by decide), ← hseed]
  exact ⟨hprotected.1,hprotected.2.2.trans hER⟩

theorem parent_bounds (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (he : 0 ≤ e)
    (h : List ℕ) (hlen : h.length = 8) (c : Cell) (hs : Source c (primeHistoryLogCoordinates N 8 h))
    (hr : RealizedHistory e q om N h c) :
    lambda3 (oldBank e q om) N (rosserAncestor 4 h) ≤ actualParent n e q om N h ∧
    actualParent n e q om N h ≤ comparison c (primeHistoryLogCoordinates N 8 h) := by
  let d := bank e q om
  have ha := (P4AOriginalFull87DataPolicy.active_ancestor d N 6 (by decide) h).mpr (source_active hlen hs hr)
  have hform : actualParent n e q om N h = P4AOriginalFull87DataPolicy.licensedCap n d N (rosserAncestor 6 h) := by
    simp only [actualParent,P4AOriginalFull87DataPolicy.actualParent,P4AOriginalFull87DataPolicy.level6Exponent,if_pos ha]
  rw [hform]
  have hf := fifth_bounds n e q om N he h hlen c hs hr
  have h56 := P4AOriginalFull87DataPolicy.cap5_le_licensed n d N (rosserAncestor 6 h)
  rw [rosserAncestor_nested 5 6 (by decide)] at h56
  refine ⟨hf.1.trans h56,?_⟩
  unfold P4AOriginalFull87DataPolicy.licensedCap
  apply finiteMax_le
  · simpa only [rosserAncestor_nested 5 6 (by decide)] using hf.2
  · intro a _ hacc
    have ht := P4AOriginalFull87CompleteSixthBound.source_ancestor_tent_le_comparison N h hlen c hs 6
      (by decide) (P4AOriginalSixthActionBank.selected a)
    have hh := hacc.2.2.trans ht
    linarith only [hh,width_pos n]

theorem actualParent_residual (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (he : 0 ≤ e)
    (h : List ℕ) (hlen : h.length = 8) (c : Cell) (hs : Source c (primeHistoryLogCoordinates N 8 h))
    (hr : RealizedHistory e q om N h c) :
    let t := primeHistoryLogCoordinates N 8 h
    t 7 < actualParent n e q om N h - total t ∧ actualParent n e q om N h ≤ comparison c t := by
  have hp := parent_bounds n e q om N he h hlen c hs hr
  have h7 := hr.2.2.1 (3 : Fin 4)
  have ho := (source_basic hs).2.2.2 (6 : Fin 7)
  refine ⟨?_,hp.2⟩
  dsimp [oldHistory,P4AOriginalRemainingEighthSources.history] at h7
  norm_num at ho
  dsimp only [total]
  simp only [Fin.sum_univ_succ]
  linarith only [hp.1,h7,ho]

theorem actual_eighth_kernel_transport (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om N : ℝ) (he : 0 ≤ e) (h : List ℕ) (hlen : h.length = 8)
    (c : Cell) (ht : primeHistoryLogCoordinates N 8 h ∈ trim c (width r))
    (hr : RealizedHistory e q om N h c) :
    let t := primeHistoryLogCoordinates N 8 h
    let P := actualParent n e q om N h
    let M := (finiteCap n c t : ℝ)
    cutoff < t 7 ∧ t 7 < P - total t ∧ P ≤ comparison c t ∧ comparison c t < M ∧
      M - total t < 3 * t 7 ∧ kernel c t ≤ residual (total t) (product t) P M + roundingConstant * width n := by
  dsimp only
  have hs := trim_subset_source c (width_pos r) ht
  have hp := actualParent_residual n e q om N he h hlen c hs hr
  have hl := finiteCap_licensed n (width_pos r) hn ht
  have hRM : comparison c (primeHistoryLogCoordinates N 8 h) < (finiteCap n c (primeHistoryLogCoordinates N 8 h) : ℝ) := by
    linarith only [hl.2.1,width_pos r]
  have hm := residual_parent_mono _ _ _ _ _ (cutoff_pos.trans ((source_coordinate_lower hs 7).trans hp.1))
    (source_product_lower hs).2 hp.2 hRM
  refine ⟨source_coordinate_lower hs 7,hp.1,hp.2,hRM,?_,?_⟩
  · have ht' := (finiteCap_upper n hs).2
    dsimp [total]
    linarith
  · change roundedKernel n c (primeHistoryLogCoordinates N 8 h) ≤ _ at hm
    linarith only [hm,(rounded_kernel_loss r n hn ht).2.2]

/-- The two earlier odd tests use the same third producer. Tests five
and seven use this bank's finite fifth and licensed complete sixth. -/
theorem validSelection (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (he : 0 ≤ e) (hN : 1 < N)
    (p : Fin 8 → ℕ) (hp : ∀ i, (p i).Prime) (c : Cell) (hs : Source c (point N p))
    (hr : RealizedHistory e q om N (pre p) c) :
    FirstExitValidSelection (sixthPolicy n e q om N) [] true (pre p).reverse := by
  have ho := P4AOriginalFull87LicensedSixthPolicy.validSelection_of_history 1 n e q om N he hN p hp c hs hr
  simp only [pre,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,List.singleton_append,
    FirstExitValidSelection,Bool.not_true,Bool.not_false] at ho
  obtain ⟨h1,_,h3,_,_,_,_,_,_⟩ := ho
  let d := bank e q om
  let L := lambda3 d N (rosserAncestor 4 (pre p))
  have hpos : ∀ i, 0 < p i := fun i => (hp i).pos
  have hord := source_strictAnti N hN p hpos c hs
  have h7 := seven_admissible_of_histories N hN p hpos hord L hr.2.2.1
  have hpr : ∀ x ∈ [p 6,p 5,p 4,p 3,p 2,p 1,p 0], x.Prime := by
    intro x hx
    simp only [List.mem_cons,List.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hp _
  have h5 := ordinaryRosserPrefixAdmissible_of_append false (N^L) [p 6,p 5]
    [p 4,p 3,p 2,p 1,p 0] hpr (List.pairwise_cons.mp (pre_pairwise p hord)).2 h7
  have ha := source_active (pre_length p) hs hr
  have ha5 : P4AOriginalFull87DataPolicy.active d N [p 4,p 3,p 2,p 1,p 0] := by
    simpa [pre,rosserAncestor] using (P4AOriginalFull87DataPolicy.active_ancestor d N 5 (by decide) (pre p)).mpr ha
  have hl5 : L ≤ P4AOriginalFull87DataPolicy.level5Exponent n d N [p 4,p 3,p 2,p 1,p 0] := by
    rw [P4AOriginalFull87DataPolicy.level5Exponent,if_pos ha5]
    simpa [L,pre,rosserAncestor] using (fifth_bounds n e q om N he (pre p) (pre_length p) c hs hr).1
  have hl6 : L ≤ level6Exponent n e q om N [p 5,p 4,p 3,p 2,p 1,p 0] := by
    simpa [L,actualParent,P4AOriginalFull87DataPolicy.actualParent,pre,rosserAncestor] using
      (parent_bounds n e q om N he (pre p) (pre_length p) c hs hr).1
  have h5' := ordinaryRosserPrefixAdmissible_mono false _ (Real.rpow_le_rpow_of_exponent_le hN.le hl5) h5
  have h7' := ordinaryRosserPrefixAdmissible_mono false _ (Real.rpow_le_rpow_of_exponent_le hN.le hl6) h7
  have ht5 : sixthPolicy n e q om N false [p 4,p 3,p 2,p 1,p 0] = true := by
    simpa [sixthPolicy,P4AOriginalFull87DataPolicy.sixthPolicy,P4AOriginalFull87DataPolicy.fifthPolicy,
      firstExitDepthSplicePolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,rosserAncestor,
      ordinaryParityRosserPolicy,oddFirstExitPolicy] using h5'
  have ht7 : sixthPolicy n e q om N false [p 6,p 5,p 4,p 3,p 2,p 1,p 0] = true := by
    simpa [sixthPolicy,P4AOriginalFull87DataPolicy.sixthPolicy,firstExitDepthSplicePolicy,
      frozenParityRosserPolicy,ancestorFrozenPolicy,rosserAncestor,ordinaryParityRosserPolicy,oddFirstExitPolicy] using h7'
  simp only [pre,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,List.singleton_append,
    FirstExitValidSelection,Bool.not_true,Bool.not_false]
  exact ⟨h1,P4AOriginalFull87DataPolicy.sixth_even n d N _,h3,P4AOriginalFull87DataPolicy.sixth_even n d N _,
    ht5,P4AOriginalFull87DataPolicy.sixth_even n d N _,ht7,P4AOriginalFull87DataPolicy.sixth_even n d N _,trivial⟩

end
end ImbalancedChen.P4AOriginalFull87UnionHistory
