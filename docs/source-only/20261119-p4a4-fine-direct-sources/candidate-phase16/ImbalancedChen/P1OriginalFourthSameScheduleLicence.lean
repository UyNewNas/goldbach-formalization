import ImbalancedChen.P1OriginalFourthActualQuantizedLicence

/-! SOURCE_ONLY / UNCOMPILED. Same-schedule completion.
The original positive-w/full87 order chooses n BEFORE a/e and q.
One fixed width bound from the ORIGINAL commonMargin works for every
subsequent e<commonE0 delta. The genuine biased-floor upper bound and
the original seed gap eliminate width<=2e from the winner licence.
-/
namespace ImbalancedChen.P1OriginalFourthSameScheduleLicence
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthAllRowsAdmission P1OriginalFourthUniformRowMargins
open P1OriginalFourthCommonHistoricalMesh P1OriginalFourthActualSourceCoverage
open P1OriginalVariableFourthContinuation P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthFullSourceActivation P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthFullActiveIntegral P1OriginalCoarseContinuation
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P1QuantizedActionLicense (LowerLicense)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P1OriginalFourthActualQuantizedLicence
  (bank actualFourth original_row_lower_actual_fourth original_row_gates_actual_fourth)

/-- Select n once, before the later universally quantified small e.
This threshold depends only on the original finite bank's true margin.
-/
theorem exists_quantizer_before_all_small_e :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ delta e : ℝ,
      e < commonE0 delta → 2*e+2*width n < commonMargin := by
  have hd : 0 < commonMargin/8 := div_pos commonMargin_pos (by norm_num)
  obtain ⟨n0,hn0⟩ := Filter.eventually_atTop.mp
    (width_tendsto.eventually (gt_mem_nhds hd))
  refine ⟨n0,?_⟩
  intro n hn delta e he
  have hw := hn0 n hn
  have heM := (commonE0_bounds he).2.1
  linarith [commonMargin_pos]

/-- The original one-step-biased floor is at least one width BELOW E.
The max with zero preserves this when width<=E. No width/e relation.
-/
theorem rounded_add_width_le (n : ℕ) (E : ℝ) (hE0 : 0 ≤ E) (hEc : E ≤ cap)
    (hw : width n ≤ E) : (rounded n E : ℝ)+width n ≤ E := by
  apply (add_le_iff_le_sub).mpr
  rw [rounded,clamp_eq hE0 hEc,Rat.cast_max,Rat.cast_zero]
  exact max_le (by linarith) (P4AOriginalFull87FiniteEighthCap.downCap_error n E).2

private theorem common_third_below_mu
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 4) (hmu : primeHistoryLogCoordinates N 4 pre 0 ≤ mu) :
    P5OriginalCommonRefinedConstructor.lambda3 d N pre =
      P5OriginalCommonRefinedConstructor.originalSeed d N pre := by
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 4) (0 : Fin 2)
  have h3 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 4) (0 : Fin 3)
  have hn2 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard N pre := by
    intro h
    have hh := h.1
    rw [h2] at hh
    exact (not_lt_of_ge hmu) hh
  have hn3 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard N pre := by
    intro h
    have hh := h.1
    rw [h3] at hh
    exact (not_lt_of_ge hmu) hh
  simp only [P5OriginalCommonRefinedConstructor.lambda3,
    P5OriginalCommonRefinedConstructor.fallbackSeed,if_neg hn2,if_neg hn3,max_self]

/-- The original positive active source is ACTUALLY active for the final
data-policy branch: inclusive rough activation, the same selected third
cell, and its unchanged below-mu oldest coordinate are all derived.
-/
theorem original_source_actual_active (e : ℚ) (q : ℕ) (omega : ℝ)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (r : ProducerRow) (hr : r ∈ originalRows4) (ht : actualPrimeTupleLog N p ∈ r.box)
    (label : Label (refinedMesh q))
    (hl : label ∈ activeAdoptedLabels (e : ℝ) ((e : ℝ)/20) (refinedMesh q))
    (hs : actualPrimeTupleLog N p ∈ positiveActiveCell e ((e : ℝ)/20) (refinedMesh q) omega label) :
    P4AOriginalFull87DataPolicy.active (bank e q omega) (N : ℝ) (tupleHistory p) := by
  have ha := (mem_activeAdoptedLabels (e : ℝ) ((e : ℝ)/20) (refinedMesh q) label).mp hl
  have hrough : omega ≤ actualPrimeTupleLog N p 2 := by
    have hh := hs.2.1.2
    simpa only [activationRegion,ha.1,if_true] using hh
  have hsupport : P1ThirdFallbackSupport.supported (e : ℝ) ((e : ℝ)/20) (refinedMesh q)
      omega (N : ℝ) (HistoricalThirdCoarse.P1OriginalFourth.history3 p) := by
    refine ⟨(active_history3_iff N hN omega p hp).mpr hrough,?_⟩
    rw [history3_coordinates]
    exact ⟨HistoricalThirdCoarse.P1OriginalFourth.prefix3 label.1,ha.2,
      mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) hs.2.1.1⟩
  have ho := r.ordered (originalRows4_geometry r hr) _ ht
  change primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 (tupleHistory p)) 0 ≤ mu ∧
    P1ThirdFallbackSupport.supported (e : ℝ) ((e : ℝ)/20) (refinedMesh q)
      omega (N : ℝ) (rosserAncestor 3 (tupleHistory p))
  rw [ancestor3_tupleHistory]
  refine ⟨?_,hsupport⟩
  rw [history3_coordinates]
  exact ho.1.2.2.2

/-- Same-schedule final terminal. No width<=e or width<=2e hypothesis.
For the SAME attained original winner, all actual lower gates hold and
level4Exponent+width is at most its unrounded buffered value. Thus the
same selected-subproduct tent is valid for EVERY later small e.
-/
theorem actual_fourth_original_winner_same_schedule
    (n : ℕ) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (omega : ℝ)
    (heM : 2*(e : ℝ)+2*width n < commonMargin)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (r : ProducerRow) (hr : r ∈ originalRows4) (ht : actualPrimeTupleLog N p ∈ r.box)
    (label : Label (refinedMesh q))
    (hl : label ∈ activeAdoptedLabels (e : ℝ) ((e : ℝ)/20) (refinedMesh q))
    (hs : actualPrimeTupleLog N p ∈ positiveActiveCell e ((e : ℝ)/20) (refinedMesh q) omega label) :
    ∃ w ∈ originalRows4, producerEligible originalAdmission4 w (actualPrimeTupleLog N p) ∧
      P5OriginalCommonRefinedConstructor.exponent4 (bank e q omega) (N : ℝ) (tupleHistory p) =
        w.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
      oldCap (actualPrimeTupleLog N p) < actualFourth n e q omega (N : ℝ) (tupleHistory p) ∧
      LowerLicense w.selected (actualPrimeTupleLog N p) (actualFourth n e q omega (N : ℝ) (tupleHistory p)) ∧
      actualFourth n e q omega (N : ℝ) (tupleHistory p)+width n ≤
        w.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
      actualFourth n e q omega (N : ℝ) (tupleHistory p)+width n ≤
        v (∑ j ∈ w.selected,actualPrimeTupleLog N p j) := by
  let d := bank e q omega
  let t := actualPrimeTupleLog N p
  let pre := tupleHistory p
  let E := P5OriginalCommonRefinedConstructor.exponent4 d (N : ℝ) pre
  let L := P5OriginalCommonRefinedConstructor.originalSeed d (N : ℝ) pre
  have hlen : pre.length = 4 := by simp [pre,tupleHistory]
  have hcoords : primeHistoryLogCoordinates (N : ℝ) 4 pre = t := tupleHistory_log N p
  have ho := r.ordered (originalRows4_geometry r hr) t ht
  have hM : 2*(e : ℝ) < commonMargin := by linarith [width_pos n]
  have hL : L = branchSeed (e : ℝ) ((e : ℝ)/20) (refinedMesh q) label :=
    seedExponent_on_meshBranch (e : ℝ) ((e : ℝ)/20) (refinedMesh q) omega label N hN p hp hs.2.1
  have hA := (mem_activeAdoptedLabels (e : ℝ) ((e : ℝ)/20) (refinedMesh q) label).mp hl
  have hb := HistoricalThirdCoarse.inBox_of_cell
    (mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) hs.2.1.1)
  have hLCap : L ≤ oldCap t := by
    rw [hL,branchSeed,if_pos hA,←cast_thirdCellExponent]
    exact original_third_exponent_le_oldCap e he _ label.1 t hb ho.1
  have hlambda : P5OriginalCommonRefinedConstructor.lambda3 d (N : ℝ) pre = L :=
    common_third_below_mu d (N : ℝ) pre hlen (by rw [hcoords];exact ho.1.2.2.2)
  have hrow : r.bufferedCandidate (e : ℝ) t ≤ E := by
    change r.bufferedCandidate (e : ℝ) t ≤
      P5OriginalCommonRefinedConstructor.exponent4 (bank e q omega) (N : ℝ) pre
    rw [P4AOriginalNewFifthUnion.same_fourth]
    exact original_row_le_complete_fourth e q omega (N : ℝ) pre hlen r hr (by rw [hcoords];exact ht)
  have himprove := (buffered_row_gates r hr (e : ℝ) hM t ht).1
  have hform : E = finiteMax originalRows4 (fun w => producerEligible originalAdmission4 w t)
      (fun w => w.bufferedCandidate (e : ℝ) t) L := by
    dsimp only [E]
    rw [P5OriginalCommonRefinedConstructor.exponent4,if_pos hlen,hcoords,hlambda]
    rfl
  obtain hseed | ⟨w,hw,helig,hwin⟩ := finiteMax_attained originalRows4
    (fun w => producerEligible originalAdmission4 w t) (fun w => w.bufferedCandidate (e : ℝ) t) L
  · rw [←hform] at hseed
    exact False.elim (by linarith)
  · rw [←hform] at hwin
    have hgate := original_row_gates_actual_fourth n e he heM q omega (N : ℝ) pre hlen w hw
      (by rw [hcoords];exact helig.2)
    rw [hcoords] at hgate
    have hLpos : 0 ≤ L := by
      rw [hL]
      have hg := (HistoricalThirdCoarse.P1OriginalFourth.mem_gateRegion _ _ _).mp hs.2.2.1
      linarith [hs.1 0,hg.2.2.1]
    have hseedGap : L+2*width n < E := by
      have hg := (buffered_row_gates r hr ((e : ℝ)+width n) (by linarith) t ht).1
      dsimp only [ProducerRow.bufferedCandidate] at hg hrow
      linarith
    have hEpos : 0 ≤ E := by linarith [width_pos n]
    have hEcap : E ≤ cap := by
      rw [hwin,ProducerRow.bufferedCandidate_eq]
      have hh := v_le_cap (∑ j ∈ w.selected,t j)
      have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
      linarith
    have hrounded := rounded_add_width_le n E hEpos hEcap (by linarith [width_pos n])
    have hprotected : protect n L E+width n ≤ E := by
      apply (add_le_iff_le_sub).mpr
      unfold protect
      exact max_le (by linarith [width_pos n]) (by linarith)
    have hactive := original_source_actual_active e q omega N hN p hp r hr ht label hl hs
    have hu : actualFourth n e q omega (N : ℝ) pre+width n ≤ E := by
      unfold actualFourth P4AOriginalFull87DataPolicy.level4Exponent
      rw [if_pos hactive]
      exact hprotected
    refine ⟨w,hw,helig,hwin,hgate.1,hgate.2,hu.trans_eq hwin,?_⟩
    rw [hwin,ProducerRow.bufferedCandidate_eq] at hu
    have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
    linarith

/-- Original joined order: fix n first; EVERY subsequent sufficiently
small e then has ONE common q-threshold for every original row. N and
the actual tuple occur only after those choices. This is the schedule
needed by the existing positive-w/full87 joined policy.
-/
theorem exists_same_schedule_original_fourth :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ delta : ℝ, 0 < delta →
      ∀ e : ℚ, 0 < e → (e : ℝ) < commonE0 delta →
      ∀ omega : ℝ, omega ≤ 3 / 200 → ∀ mMin qMin : ℕ,
      ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q → mMin ≤ refinedMesh q ∧
      ∀ r ∈ originalRows4, ∀ N : ℕ, 1 < N → ∀ p : Fin 4 → ℕ,
      (∀ i, 0 < p i) → actualPrimeTupleLog N p ∈ trimmedBox r delta →
      ∃ w ∈ originalRows4, producerEligible originalAdmission4 w (actualPrimeTupleLog N p) ∧
        P5OriginalCommonRefinedConstructor.exponent4 (bank e q omega) (N : ℝ) (tupleHistory p) =
          w.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
        oldCap (actualPrimeTupleLog N p) < actualFourth n e q omega (N : ℝ) (tupleHistory p) ∧
        LowerLicense w.selected (actualPrimeTupleLog N p)
          (actualFourth n e q omega (N : ℝ) (tupleHistory p)) ∧
        actualFourth n e q omega (N : ℝ) (tupleHistory p)+width n ≤
          w.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
        actualFourth n e q omega (N : ℝ) (tupleHistory p)+width n ≤
          v (∑ j ∈ w.selected,actualPrimeTupleLog N p j) := by
  obtain ⟨n0,hn0⟩ := exists_quantizer_before_all_small_e
  refine ⟨n0,?_⟩
  intro n hn delta hd e he he0 omega homega mMin qMin
  have heM := hn0 n hn delta (e : ℝ) he0
  obtain ⟨q0,hq0,hq⟩ := exists_common_original_source_cover delta hd e he he0 omega homega mMin qMin
  refine ⟨q0,hq0,?_⟩
  intro q hqq
  refine ⟨(hq q hqq).1,?_⟩
  intro r hr N hN p hp ht
  obtain ⟨label,hl,hs⟩ := (hq q hqq).2 r hr _ ht
  exact actual_fourth_original_winner_same_schedule n e he.le q omega heM N hN p hp r hr
    (trimmedBox_subset r hd.le ht) label hl hs

end
end ImbalancedChen.P1OriginalFourthSameScheduleLicence
