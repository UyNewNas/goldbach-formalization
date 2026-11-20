import ImbalancedChen.P1OriginalFourthPhysicalKernelComparison
import ImbalancedChen.P4AOriginalFull87DataPolicy
import ImbalancedChen.P4AOriginalNewFifthUnion

/-! SOURCE_ONLY / UNCOMPILED. Additive supplement to the six frozen sources.
The final full87 data policy reads level4Exponent, including its protect
branch. The biased floor loses LESS THAN TWO widths, as the original
protect_error states. Every lower gate is transported from actual original
rows. The upper selected-subproduct bound uses the SAME attained winner.
-/
namespace ImbalancedChen.P1OriginalFourthActualQuantizedLicence
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthAllRowsAdmission P1OriginalFourthUniformRowMargins
open P1OriginalFourthActualSourceCoverage
open P1OriginalVariableFourthContinuation
open P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthFullSourceActivation P1OriginalVariableFourthActiveOnly
open P1OriginalVariableFourthFullActiveIntegral
open P1OriginalCoarseContinuation
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P1QuantizedActionLicense (LowerLicense lowerLicense_iff)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)

abbrev bank := P4AOriginalNewFifthUnion.data
abbrev actualFourth (n : ℕ) (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :=
  P4AOriginalFull87DataPolicy.level4Exponent n (bank e q omega) N pre

/-- The final full87 policy still uses the same actual incoming first,
third and even-fourth decisions. Quantization changes the continuation
after that selected ancestor, not the already paid incoming word.
-/
theorem actual_policy_through_four (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (omega N : ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    P4AOriginalFull87DataPolicy.policy delta n (bank e q omega) N positive pre =
      P5OriginalCommonRefinedConstructor.policy4 (bank e q omega) N positive pre := by
  have h6 : pre.length ≤ 6 := hlen.trans (by decide)
  have h8 : pre.length ≤ 8 := hlen.trans (by decide)
  simp only [P4AOriginalFull87DataPolicy.policy,P4AOriginalFull87DataPolicy.sixthPolicy,
    P4AOriginalFull87DataPolicy.fifthPolicy,P5OriginalCommonRefinedConstructor.policy4,
    firstExitDepthSplicePolicy,if_pos hlen,if_pos h6,if_pos h8]

/-- One quantizer threshold can be intersected with every other pre-N
threshold. The exact source bias is 2*width, rather than one width.
-/
theorem exists_common_quantizer (e : ℝ) (he : 0 < e) (hM : 2*e < commonMargin) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      2*e + 2*width n < commonMargin ∧ width n ≤ e := by
  have hd : 0 < min e ((commonMargin-2*e)/4) := by
    exact lt_min he (div_pos (sub_pos.mpr hM) (by norm_num))
  obtain ⟨n0,hn0⟩ := Filter.eventually_atTop.mp
    (width_tendsto.eventually (gt_mem_nhds hd))
  refine ⟨n0,?_⟩
  intro n hn
  have h := hn0 n hn
  have h1 := h.trans_le (min_le_left _ _)
  have h2 := h.trans_le (min_le_right _ _)
  exact ⟨by linarith,h1.le⟩

/-- Every original endpoint enters the ACTUAL final quantized fourth
index. The proof only rounds that known row value, so it does not assume
any global physical range for an arbitrary caller's historical parent.
-/
theorem original_row_lower_actual_fourth (n : ℕ) (e : ℚ) (he : 0 ≤ e)
    (heM : 2*(e : ℝ) < commonMargin) (q : ℕ) (omega N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 4) (r : ProducerRow) (hr : r ∈ originalRows4)
    (ht : primeHistoryLogCoordinates N 4 pre ∈ r.box) :
    r.bufferedCandidate (e : ℝ) (primeHistoryLogCoordinates N 4 pre) - 2*width n <
      actualFourth n e q omega N pre := by
  let t := primeHistoryLogCoordinates N 4 pre
  let R := r.bufferedCandidate (e : ℝ) t
  let E := P5OriginalCommonRefinedConstructor.exponent4 (bank e q omega) N pre
  have hR : R ≤ E := by
    change R ≤ P5OriginalCommonRefinedConstructor.exponent4 (bank e q omega) N pre
    rw [P4AOriginalNewFifthUnion.same_fourth]
    exact original_row_le_complete_fourth e q omega N pre hlen r hr ht
  have hpos : 0 ≤ R := by
    have hhalf := (buffered_row_gates r hr (e : ℝ) heM t ht).2.1
    dsimp only [R]
    linarith
  have hcap : R ≤ cap := by
    have htent : r.candidate t ≤ cap := by
      rw [ProducerRow.candidate_eq]
      exact v_le_cap _
    have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
    dsimp only [R,ProducerRow.bufferedCandidate]
    linarith
  have hrounded := (rounded_error n R hpos hcap).1
  have hmono := rounded_mono n hR
  unfold actualFourth P4AOriginalFull87DataPolicy.level4Exponent
  split_ifs with ha
  · change R-2*width n < protect n _ E
    exact hrounded.trans_le (hmono.trans (le_max_right _ _))
  · change R-2*width n < E
    linarith [width_pos n]

/-- All lower gates of every original eligible row survive in the true
quantized level, including the original old cap. The remaining-selected
test is explicitly relative to that row's own selected mask.
-/
theorem original_row_gates_actual_fourth (n : ℕ) (e : ℚ) (he : 0 ≤ e)
    (heM : 2*(e : ℝ)+2*width n < commonMargin) (q : ℕ) (omega N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 4) (r : ProducerRow) (hr : r ∈ originalRows4)
    (ht : primeHistoryLogCoordinates N 4 pre ∈ r.box) :
    oldCap (primeHistoryLogCoordinates N 4 pre) < actualFourth n e q omega N pre ∧
      LowerLicense r.selected (primeHistoryLogCoordinates N 4 pre) (actualFourth n e q omega N pre) := by
  have hM : 2*(e : ℝ) < commonMargin := by linarith [width_pos n]
  have hlower := original_row_lower_actual_fourth n e he hM q omega N pre hlen r hr ht
  have hg := buffered_row_gates r hr ((e : ℝ)+width n) (by linarith) _ ht
  have heq : r.bufferedCandidate ((e : ℝ)+width n) (primeHistoryLogCoordinates N 4 pre) =
      r.bufferedCandidate (e : ℝ) (primeHistoryLogCoordinates N 4 pre)-2*width n := by
    unfold ProducerRow.bufferedCandidate
    ring
  rw [heq] at hg
  refine ⟨hg.1.trans hlower,(lowerLicense_iff _ _ _).mpr ?_⟩
  exact ⟨hg.2.1.trans hlower,fun j => (hg.2.2.1 j).trans hlower,
    fun j hj => (hg.2.2.2 j hj).trans hlower⟩

private theorem common_third_eq_original_below_mu
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

/-- The actual original source rules out the seed case of the same raw
maximum. A winning original row is extracted, and BOTH its lower gates
and its own selected-tent upper bound hold at the final level4Exponent.
The mask is never borrowed from an unrelated losing row.
-/
theorem actual_fourth_has_original_winner_licence
    (n : ℕ) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (omega : ℝ)
    (heM : 2*(e : ℝ)+2*width n < commonMargin) (hn : width n ≤ 2*(e : ℝ))
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
    common_third_eq_original_below_mu d (N : ℝ) pre hlen (by rw [hcoords];exact ho.1.2.2.2)
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
    have hEpos : 0 ≤ E := by
      have hh := (buffered_row_gates r hr (e : ℝ) hM t ht).2.1
      linarith
    have hEcap : E ≤ cap := by
      rw [hwin,ProducerRow.bufferedCandidate_eq]
      have hh := v_le_cap (∑ j ∈ w.selected,t j)
      have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
      linarith
    have hLE : L ≤ E := by linarith
    have hLpos : 0 ≤ L := by
      rw [hL]
      have hg := (HistoricalThirdCoarse.P1OriginalFourth.mem_gateRegion _ _ _).mp hs.2.2.1
      linarith [hs.1 0,hg.2.2.1]
    have hu : actualFourth n e q omega (N : ℝ) pre ≤ E := by
      unfold actualFourth P4AOriginalFull87DataPolicy.level4Exponent
      split_ifs
      · exact (protect_error n L E hLpos hLE hEcap).2.2
      · exact le_rfl
    refine ⟨w,hw,helig,hwin,hgate.1,hgate.2,?_⟩
    rw [ProducerRow.bufferedCandidate_eq] at hwin
    linarith

end
end ImbalancedChen.P1OriginalFourthActualQuantizedLicence
