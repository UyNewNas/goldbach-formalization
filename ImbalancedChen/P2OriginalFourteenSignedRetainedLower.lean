import ImbalancedChen.P2OriginalFourteenRetainedPrimeIntegral
import ImbalancedChen.P2OriginalFourteenRetainedTupleOwnership

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The current-parent surplus is retained. The theorem is the manuscript's
lower saving inequality; it does not assert that current equals R or that
the signed residual converges to the conservative R-profile. Only w=0 is
addressed. The positive-presieve projection remains a separate ledger.
-/
namespace ImbalancedChen.P2OriginalFourteenSignedRetainedLower
noncomputable section
open scoped Classical BigOperators Topology
open Set MeasureTheory Filter VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalFourteenWeightedTrim
open P2OriginalFourteenSignedTrimPayment
open P2OriginalFourteenRetainedPrimeIntegral
open P2OriginalFourteenRetainedTupleOwnership
open P5OriginalCommonRefinedConstructor

def tupleWeight (p : Fin 8 → ℕ) : ℝ := ∏ i, 1 / ((p i : ℝ) - 1)

def guardedTupleResidual (data : OriginalData) (N cap : ℕ) (p : Fin 8 → ℕ) : ℝ :=
  actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
    (if CurrentParentGuard (actualPrimeTupleLog N p) (tupleCurrent data N p)
      then M (actualPrimeTupleLog N p) else tupleCurrent data N p) p

def restrictedSum (data : OriginalData) (N cap : ℕ) (D : Set Point) : ℝ :=
  ∑ p ∈ (actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu)).filter
    (fun p => actualPrimeTupleLog N p ∈ D ∧ p ∈ admitted data N cap ((N : ℝ) ^ mu)),
      tupleWeight p * guardedTupleResidual data N cap p

theorem restrictedSum_eq (data : OriginalData) (N cap : ℕ) (D : Set Point) :
    restrictedSum data N cap D =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
        tupleWeight p * (if actualPrimeTupleLog N p ∈ D ∧
          p ∈ admitted data N cap ((N : ℝ) ^ mu)
          then guardedTupleResidual data N cap p else 0) := by
  simp only [restrictedSum, Finset.sum_filter, mul_ite, mul_zero]

/-- An exact literal source partition, including signs on the discarded
part and the same actual admission mask on both sides. -/
theorem restrictedSum_partition (data : OriginalData) (N cap : ℕ)
    (delta : ℝ) (hdelta : 0 < delta) :
    restrictedSum data N cap region = restrictedSum data N cap (trimmedRegion delta) +
      restrictedSum data N cap (discarded delta) := by
  simp only [restrictedSum_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ trimmedRegion delta
  · have hr := trimmedRegion_subset_region delta hdelta ht
    simp [discarded, ht, hr]
  · by_cases hr : actualPrimeTupleLog N p ∈ region <;> simp [discarded, ht, hr]

/-- Exact retained frontier source, normalized on the original scale.
This is extracted from the existing raw signed ledger summand. -/
def sourceFrontierAt (data : OriginalData) (N cap : ℕ) (z : ℝ) : ℝ :=
  ((firstExitDepthFrontier 8 (policy6 data (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 z)).map (fun state =>
        if primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix ∈ region then
          actualEighthResidualDifference N cap (currentLevel (N : ℝ) (lambda6 data (N : ℝ)))
            (familyNextLevel (N : ℝ) (lambda6 data (N : ℝ))
              P4AOriginalAscending14Literal42.literalPattern) state.selectedPrefix *
                Real.log (N : ℝ) / singularSeries N else 0)).sum

def sourceFrontier (data : OriginalData) (N cap : ℕ) : ℝ :=
  sourceFrontierAt data N cap ((N : ℝ) ^ mu)

theorem admitted_source_filter_eq (data : OriginalData) (N cap : ℕ)
    (hN : 1 < N) (hcap : (N : ℝ) ^ mu ≤ (cap : ℝ)) :
    (admitted data N cap ((N : ℝ) ^ mu)).filter (fun p => actualPrimeTupleLog N p ∈ region) =
      (actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu)).filter
        (fun p => actualPrimeTupleLog N p ∈ region ∧ p ∈ admitted data N cap ((N : ℝ) ^ mu)) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, ht⟩
    have hh := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 _ hcap p).mp hp
    refine ⟨(mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr ?_, ht, hp⟩
    exact ⟨fun i => ⟨(hh.2.1 i).1, (hh.2.1 i).2.1⟩, region_subset_box ht⟩
  · rintro ⟨hp, ht, ha⟩
    exact ⟨ha, ht⟩

/-- The actual signed source equals the target-deleted tuple sum with
the original admission filter. No frontier equality is a hypothesis. -/
theorem sourceFrontierAt_eq_admitted_sum (data : OriginalData) (N cap : ℕ) (z : ℝ) :
    sourceFrontierAt data N cap z =
      ∑ p ∈ admitted data N cap z, if actualPrimeTupleLog N p ∈ region then
        tupleWeight p * guardedTupleResidual data N cap p else 0 := by
  let F : (Fin 8 → ℕ) → ℝ := fun p =>
    if actualPrimeTupleLog N p ∈ region then tupleWeight p * guardedTupleResidual data N cap p else 0
  have he := firstExitRootFrontier_sum_eq_admitted_tuple_sum 8 (policy6 data (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z)
    (roughPrimeUniverse_nodup N cap 0 z) F
  have hleft : sourceFrontierAt data N cap z =
      ((firstExitDepthFrontier 8 (policy6 data (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
          (roughPrimeUniverse N cap 0 z)).map
          (fun state => F (primeHistoryTuple 8 state.selectedPrefix))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro state hs
    have hl := firstExitDepthFrontier_selected_length 8 _ _ [] _ true 1 (by simp) state hs
    have hhist : history (primeHistoryTuple 8 state.selectedPrefix) = state.selectedPrefix :=
      primeHistoryTuple_reverse_ofFn hl
    change (if _ then _ else 0) = F _
    dsimp [F]
    by_cases ht : primeHistoryLogCoordinates (N : ℝ) 8 state.selectedPrefix ∈ region
    · rw [if_pos ht, if_pos ht]
      have hgate := literal_source_keeps_original_current_gate (N : ℝ)
        (lambda6 data (N : ℝ)) state.selectedPrefix ht
      have hm := primeHistoryTuple_reciprocal_mass hl
      have hprod := primeHistoryTuple_prod hl
      have hlast := primeHistoryTuple_last (k := 7) hl
      simp only [guardedTupleResidual, actualPrimeTupleInitialSaving, tupleCurrent, hhist,
        currentLevel, inheritedExponent, familyNextLevel, actualEighthResidualDifference,
        tupleWeight, hgate, hm, hprod, hlast]
      ring
    · simp only [if_neg ht]
  rw [hleft, he]
  rfl

theorem sourceFrontier_eq_restrictedSum (data : OriginalData) (N cap : ℕ)
    (hN : 1 < N) (hcap : (N : ℝ) ^ mu ≤ (cap : ℝ)) :
    sourceFrontier data N cap = restrictedSum data N cap region := by
  rw [sourceFrontier, sourceFrontierAt_eq_admitted_sum, ← Finset.sum_filter]
  rw [admitted_source_filter_eq data N cap hN hcap]
  rfl

/-- Changing only the outer cutoff cannot duplicate or delete a source
history whose largest prime is already below N^mu. This is an exact
admitted-tuple identity, with the same N, cap, policy and history. -/
theorem admitted_source_cutoff_eq (data : OriginalData) (N cap : ℕ) (z : ℝ)
    (hN : 1 < N) (hz : (N : ℝ) ^ mu ≤ z) (hcap : z ≤ (cap : ℝ)) :
    (admitted data N cap z).filter (fun p => actualPrimeTupleLog N p ∈ region) =
      (admitted data N cap ((N : ℝ) ^ mu)).filter
        (fun p => actualPrimeTupleLog N p ∈ region) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, ht⟩
    have hh := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 z hcap p).mp hp
    have hb : p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu) :=
      (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hh.2.1 i).1, (hh.2.1 i).2.1⟩, region_subset_box ht⟩
    have hpi := mem_actualPrimeBoxTuples_iff.mp hb
    refine ⟨(mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 _ (hz.trans hcap) p).mpr
      ⟨hh.1, ?_, hh.2.2⟩, ht⟩
    intro i
    exact ⟨(hpi i).1, (hpi i).2.1, Nat.cast_nonneg _, (hpi i).2.2.2⟩
  · rintro ⟨hp, ht⟩
    have hh := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 _ (hz.trans hcap) p).mp hp
    refine ⟨(mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8 _ N cap 0 z hcap p).mpr
      ⟨hh.1, ?_, hh.2.2⟩, ht⟩
    intro i
    exact ⟨(hh.2.1 i).1, (hh.2.1 i).2.1, (hh.2.1 i).2.2.1,
      (hh.2.1 i).2.2.2.trans_le hz⟩

theorem sourceFrontierAt_eq_sourceFrontier (data : OriginalData) (N cap : ℕ) (z : ℝ)
    (hN : 1 < N) (hz : (N : ℝ) ^ mu ≤ z) (hcap : z ≤ (cap : ℝ)) :
    sourceFrontierAt data N cap z = sourceFrontier data N cap := by
  rw [sourceFrontier, sourceFrontierAt_eq_admitted_sum, sourceFrontierAt_eq_admitted_sum,
    ← Finset.sum_filter, ← Finset.sum_filter, admitted_source_cutoff_eq data N cap z hN hz hcap]

/-- The full original family charge also has a complement term. This
identity keeps it signed; the source lower bound below does not silently
discard weak-face histories or any other component of the full charge. -/
theorem normalized_charge_eq_source_add_complement (data : OriginalData)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) :
    P2OriginalFourteenSignedParentLedger.charge N cap 0 z
        (lambda6 data (N : ℝ)) P4AOriginalAscending14Literal42.literalPattern
        (policy5 data (N : ℝ)) * Real.log (N : ℝ) / singularSeries N =
      sourceFrontierAt data N cap z +
        ∑ p ∈ admitted data N cap z, if actualPrimeTupleLog N p ∈ region then 0 else
          tupleWeight p * actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
            (familyNextExponent (N : ℝ) (lambda6 data (N : ℝ))
              P4AOriginalAscending14Literal42.literalPattern (history p)) p := by
  rw [normalized_charge_eq_admitted_sum data N cap hN z, sourceFrontierAt_eq_admitted_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ region
  · have hg := literal_source_keeps_original_current_gate (N : ℝ) (lambda6 data (N : ℝ))
      (history p) (by simpa only [history_log] using ht)
    simp only [history_log] at hg
    simp only [if_pos ht, add_zero, hg, tupleWeight, guardedTupleResidual, tupleCurrent,
      inheritedExponent]
  · simp only [if_neg ht, zero_add, tupleWeight]

private theorem guarded_residual_bound (N cap : ℕ) (hcap : (N : ℝ) ^ mu ≤ (cap : ℝ))
    (data : OriginalData) (p : Fin 8 → ℕ)
    (hp : p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu))
    (ht : actualPrimeTupleLog N p ∈ region)
    (hb : ∀ (t : Point) (v P y : ℝ), t ∈ region → CurrentParentGuard t v → 0 < P → 0 < y →
      Real.log P / Real.log (N : ℝ) = S t → Real.log y / Real.log (N : ℝ) = t 7 →
      y ≤ (cap : ℝ) → |normalizedResidual N cap P y v t| ≤ residualBound) :
    |guardedTupleResidual data N cap p| ≤ residualBound := by
  by_cases hg : CurrentParentGuard (actualPrimeTupleLog N p) (tupleCurrent data N p)
  · have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hpos (i : Fin 8) : 0 < p i := (hpi i).1.pos
    have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
    have hy : (0 : ℝ) < p 7 := by exact_mod_cast hpos 7
    have hh := hb _ (tupleCurrent data N p) (∏ i, p i : ℕ) (p 7 : ℝ) ht hg hP hy
      (actualPrimeTupleLog_sum_prod p hpos).symm rfl ((hpi 7).2.2.2.le.trans hcap)
    simpa only [guardedTupleResidual, if_pos hg, actualPrimeTupleInitialSaving,
      normalizedResidual] using hh
  · simp only [guardedTupleResidual, if_neg hg, actualPrimeTupleInitialSaving,
      sub_self, zero_mul, zero_div, abs_zero]
    exact residualBound_pos.le

/-- K's pointwise absolute bound pays the actual admission submask of
the discarded source. No cancellation in the full cube is reused as a
bound for a subset, and no gate is assumed true on discarded histories. -/
theorem discarded_mask_le_mass (N cap : ℕ) (hcap : (N : ℝ) ^ mu ≤ (cap : ℝ))
    (data : OriginalData) (delta : ℝ)
    (hb : ∀ (t : Point) (v P y : ℝ), t ∈ region → CurrentParentGuard t v → 0 < P → 0 < y →
      Real.log P / Real.log (N : ℝ) = S t → Real.log y / Real.log (N : ℝ) = t 7 →
      y ≤ (cap : ℝ) → |normalizedResidual N cap P y v t| ≤ residualBound) :
    |restrictedSum data N cap (discarded delta)| ≤ residualBound * discardedPrimeMass N delta := by
  rw [restrictedSum_eq]
  unfold discardedPrimeMass actualPrimeBoxTestSum
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg hp
  by_cases ht : actualPrimeTupleLog N p ∈ discarded delta
  · rw [indicator_of_mem ht, mul_one]
    by_cases ha : p ∈ admitted data N cap ((N : ℝ) ^ mu)
    · rw [if_pos ⟨ht, ha⟩, abs_mul, abs_of_nonneg hw]
      simpa only [tupleWeight, mul_comm] using mul_le_mul_of_nonneg_left
        (guarded_residual_bound N cap hcap data p hp ht.1 hb) hw
    · simp only [ha, and_false, if_false, mul_zero, abs_zero]
      exact mul_nonneg residualBound_pos.le (actualPrimeBoxWeight_nonneg hp)
  · simp only [ht, false_and, if_false, mul_zero, abs_zero, indicator_of_notMem ht,
      zero_mul, le_refl]

private theorem retained_comparison_le (data : OriginalData) (N cap : ℕ)
    (delta epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hown : ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
      actualPrimeTupleLog N p ∈ trimmedRegion delta →
        p ∈ admitted data N cap ((N : ℝ) ^ mu) ∧
          CurrentParentGuard (actualPrimeTupleLog N p) (tupleCurrent data N p))
    (hgain : ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu),
      actualPrimeTupleLog N p ∈ trimmedRegion delta →
      sourceGain (R (actualPrimeTupleLog N p)) (M (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p)
        - epsilon ≤ actualPrimeTupleInitialSaving N cap (tupleCurrent data N p)
          (M (actualPrimeTupleLog N p)) p) :
    retainedComparisonSum N delta - epsilon *
      actualPrimeBoxMass N (fun _ : Fin 8 => cutoff) (fun _ => mu) ≤
      restrictedSum data N cap (trimmedRegion delta) := by
  simp only [retainedComparisonSum, actualPrimeBoxTestSum, actualPrimeBoxMass,
    restrictedSum_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg hp
  by_cases ht : actualPrimeTupleLog N p ∈ trimmedRegion delta
  · obtain ⟨ha, hg⟩ := hown p hp ht
    rw [indicator_of_mem ht, if_pos ⟨ht, ha⟩, guardedTupleResidual, if_pos hg]
    have hh := mul_le_mul_of_nonneg_left (hgain p hp ht) hw
    simpa only [tupleWeight, mul_sub, mul_comm epsilon] using hh
  · simp only [indicator_of_notMem ht, ht, false_and, if_false, mul_zero, zero_sub]
    exact neg_nonpos.mpr (mul_nonneg hepsilon (actualPrimeBoxWeight_nonneg hp))

/-- One pre-N schedule pays both the actual signed discarded frontier
and the fixed-trim prime integral. The old constructor and all its original
rows remain the same throughout. The result is a lower bound, so the
nonnegative current-parent surplus is never silently set to zero. -/
theorem exists_actual_source_frontier_lower (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 → ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 N0 : ℕ, 2 ≤ N0 ∧
      ∀ data : OriginalData, data.e = e → data.chi = chi → m0 ≤ data.m → data.omega ≤ 1 / 100 →
      ∀ N cap : ℕ, N0 ≤ N → Even N → (N : ℝ) ^ mu ≤ (cap : ℝ) →
        |(∫ t in region, sourceDensity t) -
          (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 ∧
        (∫ t in region, sourceDensity t) - epsilon < sourceFrontier data N cap := by
  let eta : ℝ := epsilon / (4 * (residualBound + 1))
  have heta : 0 < eta := div_pos hepsilon (by linarith [residualBound_pos])
  obtain ⟨n, hInt, Nm, hNm, hmassDiscard⟩ := exists_common_trim_integral_and_prime_mass eta heta
  have htrim : |(∫ t in region, sourceDensity t) -
      (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 := by
    have hh := (abs_sourceIntegral_sub_trim_le _ (width_pos n)).trans_lt hInt
    have hη : eta < epsilon / 4 := by
      dsimp [eta]
      have hden : 1 < residualBound + 1 := by linarith [residualBound_pos]
      have hsmall := div_lt_self (show 0 < epsilon / 4 by positivity) hden
      simpa only [div_div] using hsmall
    exact hh.trans hη
  obtain ⟨e0, he0, hown⟩ := exists_retained_tuple_ownership (width n) (width_pos n)
  obtain ⟨Nr, hNr, hres⟩ := exists_uniform_absolute_residual_bound
  let B : ℝ := ∏ _i : Fin 8, Real.log (mu / cutoff)
  have hB : 0 ≤ B := Finset.prod_nonneg (fun _ _ =>
    Real.log_nonneg ((one_le_div cutoff_pos).mpr (by norm_num [cutoff, mu])))
  let gamma : ℝ := epsilon / (4 * (B + 1))
  have hgamma : 0 < gamma := div_pos hepsilon (by positivity)
  obtain ⟨Ng, hNg, hgain⟩ := P2OriginalFourteenUniformResidual.exists_uniform_comparison_gain gamma hgamma
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp
    ((tendsto_actualPrimeBoxMass (fun _ : Fin 8 => cutoff) (fun _ => mu)
      (fun _ => cutoff_pos) (fun _ => by norm_num [cutoff, mu])).eventually
      (gt_mem_nhds (lt_add_one B)))
  obtain ⟨Ni, hNi⟩ := eventually_atTop.mp (show ∀ᶠ N : ℕ in atTop,
      |retainedComparisonSum N (width n) - (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 from by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_retainedComparisonSum (width n) (width_pos n)) (epsilon / 4) (by positivity))
  refine ⟨n, e0, he0, ?_⟩
  intro e he hee chi hchi hchie
  obtain ⟨m0, hm0⟩ := hown e he hee chi hchi hchie
  let N0 := max Nm (max Nr (max Ng (max Nb Ni)))
  refine ⟨m0, N0, hNm.trans (le_max_left _ _), ?_⟩
  intro data hde hdc hdm homega N cap hN hEven hcap
  have hNmN : Nm ≤ N := (le_max_left _ _).trans hN
  have hNrN : Nr ≤ N := by dsimp [N0] at hN; omega
  have hNgN : Ng ≤ N := by dsimp [N0] at hN; omega
  have hNbN : Nb ≤ N := by dsimp [N0] at hN; omega
  have hNiN : Ni ≤ N := by dsimp [N0] at hN; omega
  have hN1 : 1 < N := by omega
  have hownership := hm0 data hde hdc hdm homega N cap hN1 hcap
  have hr := retained_comparison_le data N cap (width n) gamma hgamma.le hownership (by
    intro p hp ht
    have htreg := trimmedRegion_subset_region (width n) (width_pos n) ht
    obtain ⟨c, hc⟩ := mem_iUnion.mp htreg
    have hpi := mem_actualPrimeBoxTuples_iff.mp hp
    have hpos (i : Fin 8) : 0 < p i := (hpi i).1.pos
    have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
    have hy : (0 : ℝ) < p 7 := by exact_mod_cast hpos 7
    exact (hgain N hNgN hEven _ _ (tupleCurrent data N p) _ _
      (sourceRows_cellGuard c _ hc) (hownership p hp ht).2 hP hy
      (actualPrimeTupleLog_sum_prod p hpos).symm rfl cap ((hpi 7).2.2.2.le.trans hcap)).le)
  have hd := discarded_mask_le_mass N cap hcap data (width n) (by
    intro t v P y ht hg hP hy hlogP hlogy hcover
    exact hres N hNrN hEven t v P y ht hg hP hy hlogP hlogy cap hcover)
  have hd' : |restrictedSum data N cap (discarded (width n))| < epsilon / 4 := by
    have hm := mul_lt_mul_of_pos_left (hmassDiscard N hNmN) residualBound_pos
    have heq : (residualBound + 1) * eta = epsilon / 4 := by
      dsimp [eta]
      field_simp [show residualBound + 1 ≠ 0 by linarith [residualBound_pos]]
    nlinarith
  have hg' : gamma * actualPrimeBoxMass N (fun _ : Fin 8 => cutoff) (fun _ => mu) < epsilon / 4 := by
    have hh := mul_lt_mul_of_pos_left (hNb N hNbN) hgamma
    have heq : gamma * (B + 1) = epsilon / 4 := by
      dsimp [gamma]
      field_simp [show B + 1 ≠ 0 by positivity]
    rwa [heq] at hh
  refine ⟨htrim, ?_⟩
  rw [sourceFrontier_eq_restrictedSum data N cap hN1 hcap,
    restrictedSum_partition data N cap (width n) (width_pos n)]
  have hi := hNi N hNiN
  have htlo := (abs_lt.mp htrim).2
  have hilo := (abs_lt.mp hi).1
  have hdlo := (abs_lt.mp hd').1
  linarith

/-- The same schedule works inside the original larger rough carrier.
For example z=N^rho0 is legal whenever mu<=rho0 and the enumeration cap
covers z; no physical rho or root cutoff is redefined by this theorem. -/
theorem exists_actual_source_frontier_lower_at_original_cutoff
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 → ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 N0 : ℕ, 2 ≤ N0 ∧
      ∀ data : OriginalData, data.e = e → data.chi = chi → m0 ≤ data.m → data.omega ≤ 1 / 100 →
      ∀ N cap : ℕ, N0 ≤ N → Even N → ∀ z : ℝ,
        (N : ℝ) ^ mu ≤ z → z ≤ (cap : ℝ) →
        |(∫ t in region, sourceDensity t) -
          (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 ∧
        (∫ t in region, sourceDensity t) - epsilon < sourceFrontierAt data N cap z := by
  obtain ⟨n, e0, he0, hs⟩ := exists_actual_source_frontier_lower epsilon hepsilon
  refine ⟨n, e0, he0, ?_⟩
  intro e he hee chi hchi hchie
  obtain ⟨m0, N0, hN0, hbound⟩ := hs e he hee chi hchi hchie
  refine ⟨m0, N0, hN0, ?_⟩
  intro data hde hdc hdm homega N cap hN hEven z hz hcap
  rw [sourceFrontierAt_eq_sourceFrontier data N cap z (by omega) hz hcap]
  exact hbound data hde hdc hdm homega N cap hN hEven (hz.trans hcap)

end
end ImbalancedChen.P2OriginalFourteenSignedRetainedLower
