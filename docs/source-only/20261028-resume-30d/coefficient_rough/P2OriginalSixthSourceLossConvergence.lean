import ImbalancedChen.P2OriginalSixthSourceCompactCores

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The integrand is the original eight-factor sixth savingKernel.  Its
literal source cutoff t6>53/4608 bounds every denominator away from zero.
Thus no conjectured integrability or target integral is a premise of
the compact-core exhaustion or its boundary/tail convergence.
-/

namespace ImbalancedChen.P2OriginalSixthSourceLossConvergence

noncomputable section
open Classical Set Filter MeasureTheory
open scoped Topology BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P2OriginalSixthSourceCompactCores P2CompactThirdHistorySelection

def denominatorFloor : ℝ := 53 / 4608
def sourceKernelBound : ℝ := 36 / denominatorFloor ^ 8

theorem savingKernel_bound (c : Cell) (t : Physical) (hc : PhysicalCell c t) :
    0 ≤ savingKernel c t ∧ savingKernel c t ≤ sourceKernelBound := by
  have hbox := physicalCell_mem_ambientCube c t hc
  have hu (i : Fin 6) : t i ≤ 1 := (hbox i (Set.mem_univ i)).2
  have hr := hc.residual_guards
  have hfac : ∀ i : Fin 8, denominatorFloor ≤ factors c t i := by
    intro i
    fin_cases i <;> simp only [factors, Matrix.cons_val_zero, Matrix.cons_val_succ]
    all_goals
      dsimp only [denominatorFloor]
      linarith [hc.compactCutoff, hc.order.1, hc.order.2.1, hc.order.2.2.1,
        hc.order.2.2.2.1, hc.order.2.2.2.2, hr.1, hr.2.1, hr.2.2.1]
  have ha : 0 < denominatorFloor := by norm_num [denominatorFloor]
  have hprod := Finset.prod_le_prod
    (s := (Finset.univ : Finset (Fin 8))) (f := fun _ => denominatorFloor)
    (g := factors c t) (fun _ _ => ha.le) (fun i _ => hfac i)
  have hden : denominatorFloor ^ 8 ≤ factorProduct c t := by
    simpa only [factorProduct, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod
  have hden0 : 0 < factorProduct c t := (by positivity : 0 < denominatorFloor^8).trans_le hden
  have hnew : newCap c t ≤ 9 := by
    unfold newCap
    split_ifs
    · dsimp only [ascending33]
      linarith [hu 0, hu 5]
    · dsimp only [clippedCap, S5, eta]
      linarith [hu 0, hu 1, hu 2, hu 3, hu 4, hu 5]
  have hold : 0 ≤ oldCap c t := by
    have hw := hc.raw_envelope.1
    dsimp only [W] at hw
    linarith [hu 2]
  have hnum : 4 * gap c t ≤ 36 := by dsimp only [gap]; linarith
  have hinv := one_div_le_one_div_of_le (by positivity : 0 < denominatorFloor^8) hden
  refine ⟨hc.savingKernel_pos.le, ?_⟩
  calc
    savingKernel c t = (4 * gap c t) / factorProduct c t := rfl
    _ ≤ 36 / factorProduct c t := div_le_div_of_nonneg_right hnum hden0.le
    _ ≤ 36 / denominatorFloor^8 := by
      convert mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 36) using 1 <;> ring

theorem measurable_savingKernel (c : Cell) : Measurable (savingKernel c) := by
  unfold savingKernel gap factorProduct factors oldResidual newResidual
  fun_prop

theorem integrable_source_indicator (c : Cell) :
    Integrable ((sourceRegion c).indicator (savingKernel c)) := by
  have hcube : IsCompact ambientCube := isCompact_univ_pi (fun _ : Fin 6 => isCompact_Icc)
  have hdom : Integrable (ambientCube.indicator (fun _ : Physical => sourceKernelBound)) :=
    (integrable_indicator_iff hcube.measurableSet).mpr
      (integrableOn_const hcube.measure_ne_top)
  apply hdom.mono' ((measurable_savingKernel c).indicator
    (measurableSet_sourceRegion c)).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    by_cases ht : t ∈ sourceRegion c
    · have h := savingKernel_bound c t ht
      rw [indicator_of_mem ht,
        indicator_of_mem (physicalCell_mem_ambientCube c t ht), Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2
    · rw [indicator_of_notMem ht, norm_zero]
      by_cases hcube : t ∈ ambientCube
      · rw [indicator_of_mem hcube]
        dsimp only [sourceKernelBound, denominatorFloor]
        positivity
      · simpa only [indicator_of_notMem hcube] using (le_rfl : (0 : ℝ) ≤ 0)

theorem integrableOn_savingKernel (c : Cell) : IntegrableOn (savingKernel c) (sourceRegion c) :=
  (integrable_indicator_iff (measurableSet_sourceRegion c)).mp (integrable_source_indicator c)

theorem measurableSet_coreSequence (c : Cell) (n : ℕ) : MeasurableSet (coreSequence c n) :=
  (isCompact_compactCore c _).measurableSet

theorem measurableSet_omittedSource (c : Cell) (n : ℕ) : MeasurableSet (omittedSource c n) :=
  (measurableSet_sourceRegion c).diff (measurableSet_coreSequence c n)

def sourceGain (c : Cell) : ℝ := ∫ t in sourceRegion c, savingKernel c t
def compactGain (c : Cell) (n : ℕ) : ℝ := ∫ t in coreSequence c n, savingKernel c t
def omittedGain (c : Cell) (n : ℕ) : ℝ := ∫ t in omittedSource c n, savingKernel c t

/-- This partition is exact even on all raw-mask and cutoff equality
faces.  No zero-volume boundary substitution is used. -/
theorem sourceGain_eq_compact_add_omitted (c : Cell) (n : ℕ) :
    sourceGain c = compactGain c n + omittedGain c n := by
  have hunion : coreSequence c n ∪ omittedSource c n = sourceRegion c := by
    ext t
    constructor
    · rintro (h | h)
      · exact coreSequence_subset_sourceRegion c n h
      · exact h.1
    · intro h
      by_cases ht : t ∈ coreSequence c n
      · exact Or.inl ht
      · exact Or.inr ⟨h, ht⟩
  have hd : Disjoint (coreSequence c n) (omittedSource c n) := by
    apply Set.disjoint_left.mpr
    intro t ht ho
    exact ho.2 ht
  unfold sourceGain compactGain omittedGain
  rw [← hunion]
  exact setIntegral_union hd (measurableSet_omittedSource c n)
    ((integrableOn_savingKernel c).mono_set (coreSequence_subset_sourceRegion c n))
    ((integrableOn_savingKernel c).mono_set Set.diff_subset)

theorem omittedGain_nonneg (c : Cell) (n : ℕ) : 0 ≤ omittedGain c n := by
  unfold omittedGain
  rw [← integral_indicator (measurableSet_omittedSource c n)]
  apply integral_nonneg
  intro t
  by_cases ht : t ∈ omittedSource c n
  · rw [indicator_of_mem ht]
    exact (savingKernel_bound c t ht.1).1
  · simpa only [indicator_of_notMem ht] using (le_rfl : (0 : ℝ) ≤ 0)

/-- All omitted boundary and tail mass tends to zero for the original
kernel itself, with no assumed envelope or integral convergence. -/
theorem tendsto_omittedGain (c : Cell) :
    Tendsto (omittedGain c) atTop (𝓝 0) := by
  have hglobal : Tendsto
      (fun n : ℕ => ∫ t : Physical, (omittedSource c n).indicator (savingKernel c) t)
      atTop (𝓝 (∫ _t : Physical, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun t => ‖(sourceRegion c).indicator (savingKernel c) t‖)
    · exact Eventually.of_forall fun n =>
        ((measurable_savingKernel c).indicator
          (measurableSet_omittedSource c n)).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun t => by
        by_cases ht : t ∈ omittedSource c n
        · rw [indicator_of_mem ht, indicator_of_mem ht.1]
        · rw [indicator_of_notMem ht, norm_zero]
          exact norm_nonneg _
    · exact (integrable_source_indicator c).norm
    · exact Eventually.of_forall fun t => by
        by_cases ht : t ∈ sourceRegion c
        · apply tendsto_const_nhds.congr'
          filter_upwards [eventually_mem_coreSequence c ht] with n hn
          simp [omittedSource, hn]
        · have hz : ∀ n : ℕ, (omittedSource c n).indicator (savingKernel c) t = 0 := by
            intro n
            simp [omittedSource, ht]
          simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have heq : (fun n : ℕ => ∫ t : Physical, (omittedSource c n).indicator (savingKernel c) t) =
      omittedGain c := by
    funext n
    exact integral_indicator (measurableSet_omittedSource c n)
  rw [heq] at hglobal
  simpa only [integral_zero] using hglobal

theorem tendsto_compactGain (c : Cell) : Tendsto (compactGain c) atTop (𝓝 (sourceGain c)) := by
  have heq : compactGain c = fun n : ℕ => sourceGain c - omittedGain c n := by
    funext n
    linarith [sourceGain_eq_compact_add_omitted c n]
  rw [heq]
  simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_omittedGain c)

/-- A source-core truncation with arbitrarily small actual saving loss
already admits the previous uniform finite third policy construction. -/
theorem exists_original_core_small_loss_choice (c : Cell) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ n : ℕ, Nonempty (CompactThirdChoice (coreSequence c n)) ∧
      0 ≤ sourceGain c - compactGain c n ∧
      sourceGain c - compactGain c n < epsilon := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    ((tendsto_omittedGain c).eventually (gt_mem_nhds he))
  refine ⟨n, original_core_thirdChoice c n, ?_, ?_⟩
  · linarith [sourceGain_eq_compact_add_omitted c n, omittedGain_nonneg c n]
  · linarith [sourceGain_eq_compact_add_omitted c n, hn n le_rfl]

end
end ImbalancedChen.P2OriginalSixthSourceLossConvergence
