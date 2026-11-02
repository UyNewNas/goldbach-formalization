import ImbalancedChen.P2OriginalSaving16TrimmedHistory
import ImbalancedChen.AffinePrimeWallReserve

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Weighted loss for the actual 14-cell, 96-row saving16 source. The trim is
the J trim, not a new domain. A continuous majorant is built from its
literal affine rows. Degenerate rows are handled algebraically: a zero
identity contributes no positive-slack strip, and a nonzero constant is
eventually away from zero. There is no proper-row, null-wall, rejected
cost, convergence, or numerical endpoint premise.
-/
namespace ImbalancedChen.P2OriginalFourteenWeightedTrim
noncomputable section
open scoped Classical BigOperators Topology
open Set MeasureTheory Filter VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory

def width (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

theorem width_tendsto : Tendsto width atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def discarded (delta : ℝ) : Set Point := region \ trimmedRegion delta

theorem measurableSet_discarded (delta : ℝ) : MeasurableSet (discarded delta) :=
  measurableSet_region.diff (isCompact_trimmedRegion delta).measurableSet

theorem trimmedRegion_antitone {a b : ℝ} (hab : a ≤ b) :
    trimmedRegion b ⊆ trimmedRegion a := by
  intro t ht
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  exact mem_iUnion.mpr ⟨c, hc.1,
    mem_iInter.mpr (fun k => hab.trans (mem_iInter.mp hc.2 k))⟩

theorem region_eventually_retained {t : Point} (ht : t ∈ region) :
    ∀ᶠ n : ℕ in atTop, t ∈ trimmedRegion (width n) := by
  obtain ⟨delta, hdelta, hkeep⟩ := region_point_survives_trim ht
  filter_upwards [width_tendsto.eventually (gt_mem_nhds hdelta)] with n hn
  exact trimmedRegion_antitone hn.le hkeep

/-- The actual coefficient-four integral loses arbitrarily little under
the literal source trims. Integrability is supplied by J's real atlas. -/
theorem tendsto_discarded_sourceIntegral :
    Tendsto (fun n => ∫ t in discarded (width n), |sourceDensity t|)
      atTop (𝓝 0) := by
  let f : ℕ → Point → ℝ := fun n =>
    (discarded (width n)).indicator (fun t => |sourceDensity t|)
  let g : Point → ℝ := region.indicator (fun t => |sourceDensity t|)
  have hg : Integrable g :=
    integrableOn_sourceDensity_region.abs.integrable_indicator measurableSet_region
  have hf (n : ℕ) : Integrable (f n) :=
    (integrableOn_sourceDensity_region.abs.mono_set
      (show discarded (width n) ⊆ region from diff_subset)).integrable_indicator
        (measurableSet_discarded _)
  have hlim := tendsto_integral_of_dominated_convergence g
    (fun n => (hf n).aestronglyMeasurable) hg
    (fun n => Eventually.of_forall (fun t => by
      by_cases ht : t ∈ discarded (width n)
      · simp only [f, g, indicator_of_mem ht, indicator_of_mem ht.1,
          Real.norm_eq_abs, abs_abs, le_refl]
      · rw [show f n t = 0 by exact indicator_of_notMem ht _]
        rw [norm_zero]
        exact indicator_nonneg (fun _ _ => abs_nonneg _) t))
    (show ∀ᵐ t ∂(volume : Measure Point),
      Tendsto (fun n => f n t) atTop (𝓝 (0 : ℝ)) from Eventually.of_forall (fun t => by
      apply tendsto_const_nhds.congr'
      by_cases ht : t ∈ region
      · filter_upwards [region_eventually_retained ht] with n hn
        exact (indicator_of_notMem (by simp [discarded, hn]) _).symm
      · exact Eventually.of_forall (fun n =>
          (indicator_of_notMem (fun h => ht h.1) _).symm)))
  simpa only [f, integral_indicator (measurableSet_discarded _), integral_zero] using hlim

/-- Exact integral reconstruction on the actual union; no cell overlap
or triangulation assumption is needed for this source/trim partition. -/
theorem sourceIntegral_eq_trim_add_discard (delta : ℝ) (hdelta : 0 < delta) :
    (∫ t in region, sourceDensity t) =
      (∫ t in trimmedRegion delta, sourceDensity t) +
        ∫ t in discarded delta, sourceDensity t := by
  have hsub := trimmedRegion_subset_region delta hdelta
  have h := setIntegral_sdiff (isCompact_trimmedRegion delta).measurableSet
    integrableOn_sourceDensity_region hsub
  change (∫ t in discarded delta, sourceDensity t) =
    (∫ t in region, sourceDensity t) - (∫ t in trimmedRegion delta, sourceDensity t) at h
  linarith

theorem abs_sourceIntegral_sub_trim_le (delta : ℝ) (hdelta : 0 < delta) :
    |(∫ t in region, sourceDensity t) - (∫ t in trimmedRegion delta, sourceDensity t)| ≤
      ∫ t in discarded delta, |sourceDensity t| := by
  rw [sourceIntegral_eq_trim_add_discard delta hdelta, add_sub_cancel_left]
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (μ := volume.restrict (discarded delta)) sourceDensity)

def linearPart (row : Fin 9 → ℚ) : Point →L[ℝ] ℝ :=
  ∑ j : Fin 8, (row j.succ : ℝ) • ContinuousLinearMap.proj j

theorem evalRow_eq_linear (row : Fin 9 → ℚ) (t : Point) :
    evalRow row t = (row 0 : ℝ) + linearPart row t := by
  simp [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine, linearPart]

/-- An actual zero identity must not become a fake wall. -/
def zeroRow (row : Fin 9 → ℚ) : Prop := linearPart row = 0 ∧ (row 0 : ℝ) = 0

theorem evalRow_eq_zero_of_zeroRow {row : Fin 9 → ℚ} (h : zeroRow row) (t : Point) :
    evalRow row t = 0 := by simp [evalRow_eq_linear, h.1, h.2]

def rowMajorant (row : Fin 9 → ℚ) (n : ℕ) (t : Point) : ℝ :=
  if zeroRow row then 0 else affinePrimeClamp (2 - (n + 1 : ℝ) * |evalRow row t|)

theorem continuous_rowMajorant (row : Fin 9 → ℚ) (n : ℕ) :
    Continuous (rowMajorant row n) := by
  by_cases h : zeroRow row
  · simp only [rowMajorant, if_pos h]; exact continuous_const
  · simp only [rowMajorant, if_neg h]
    exact continuous_affinePrimeClamp.comp
      (continuous_const.sub (continuous_const.mul (continuous_evalRow row).abs))

theorem rowMajorant_bounds (row : Fin 9 → ℚ) (n : ℕ) (t : Point) :
    0 ≤ rowMajorant row n t ∧ rowMajorant row n t ≤ 1 := by
  by_cases h : zeroRow row
  · simp [rowMajorant, h]
  · simpa [rowMajorant, h] using affinePrimeClamp_bounds (2 - (n + 1 : ℝ) * |evalRow row t|)

theorem rowMajorant_ge_one (row : Fin 9 → ℚ) (n : ℕ) (t : Point)
    (hpos : 0 < evalRow row t) (hsmall : evalRow row t ≤ width n) :
    1 ≤ rowMajorant row n t := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hz : ¬ zeroRow row := fun h => by
    rw [evalRow_eq_zero_of_zeroRow h] at hpos
    exact lt_irrefl _ hpos
  have hh : (n + 1 : ℝ) * |evalRow row t| ≤ 1 := by
    rw [abs_of_pos hpos]
    have h := mul_le_mul_of_nonneg_left hsmall hn.le
    simpa only [width, mul_one_div_cancel hn.ne'] using h
  rw [rowMajorant, if_neg hz, affinePrimeClamp_eq_one (by linarith)]

theorem rowMajorant_tendsto_of_ne (row : Fin 9 → ℚ) (t : Point)
    (ht : evalRow row t ≠ 0) : Tendsto (fun n => rowMajorant row n t) atTop (𝓝 0) := by
  by_cases hz : zeroRow row
  · simp only [rowMajorant, if_pos hz]; exact tendsto_const_nhds
  · have hp := abs_pos.mpr ht
    have hg : Tendsto (fun n : ℕ => (n + 1 : ℝ) * |evalRow row t|) atTop atTop :=
      (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hp
    apply tendsto_const_nhds.congr'
    filter_upwards [hg.eventually (eventually_ge_atTop (2 : ℝ))] with n hn
    simp only [rowMajorant, if_neg hz, affinePrimeClamp_eq_zero (sub_nonpos.mpr hn)]

theorem ae_rowMajorant_tendsto (row : Fin 9 → ℚ) :
    ∀ᵐ t ∂(volume : Measure Point), Tendsto (fun n => rowMajorant row n t) atTop (𝓝 0) := by
  by_cases hL : linearPart row = 0
  · by_cases hc : (row 0 : ℝ) = 0
    · exact Eventually.of_forall (fun t => by
        simp only [rowMajorant, show zeroRow row from ⟨hL, hc⟩, if_true]
        exact tendsto_const_nhds)
    · exact Eventually.of_forall (fun t => rowMajorant_tendsto_of_ne row t
        (by simpa only [evalRow_eq_linear, hL, ContinuousLinearMap.zero_apply, add_zero] using hc))
  · have hwall : ∀ᵐ t ∂(volume : Measure Point), linearPart row t ≠ -(row 0 : ℝ) := by
      rw [ae_iff]
      simpa only [not_not] using affinePrimeWall_volume_zero (linearPart row) hL (-(row 0 : ℝ))
    filter_upwards [hwall] with t ht
    apply rowMajorant_tendsto_of_ne row t
    rw [evalRow_eq_linear]
    intro h
    exact ht (by linarith)

def wallMajorant (n : ℕ) (t : Point) : ℝ :=
  ∑ c : Cell, ∑ k : Fin 96, rowMajorant (rows c k).2 n t

def wallCount : ℝ := (Fintype.card Cell : ℝ) * 96

theorem continuous_wallMajorant (n : ℕ) : Continuous (wallMajorant n) := by
  exact continuous_finsetSum _ (fun c _ =>
    continuous_finsetSum _ (fun k _ => continuous_rowMajorant _ n))

theorem wallMajorant_bounds (n : ℕ) (t : Point) :
    0 ≤ wallMajorant n t ∧ wallMajorant n t ≤ wallCount := by
  refine ⟨Finset.sum_nonneg (fun c _ =>
    Finset.sum_nonneg (fun k _ => (rowMajorant_bounds _ n t).1)), ?_⟩
  calc
    wallMajorant n t ≤ ∑ _c : Cell, ∑ _k : Fin 96, (1 : ℝ) :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun k _ => (rowMajorant_bounds _ n t).2))
    _ = wallCount := by simp [wallCount]

theorem ae_wallMajorant_tendsto :
    ∀ᵐ t ∂(volume : Measure Point), Tendsto (fun n => wallMajorant n t) atTop (𝓝 0) := by
  have hall : ∀ᵐ t ∂(volume : Measure Point), ∀ c : Cell, ∀ k : Fin 96,
      Tendsto (fun n => rowMajorant (rows c k).2 n t) atTop (𝓝 0) :=
    ae_all_iff.mpr (fun c => ae_all_iff.mpr (fun k => ae_rowMajorant_tendsto _))
  filter_upwards [hall] with t ht
  simpa only [wallMajorant, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun c _ =>
      tendsto_finsetSum Finset.univ (fun k _ => ht c k))

/-- Failure of the actual trim has a small positive ORIGINAL row slack.
The source's genuine identities are never demanded to become strict. -/
theorem discarded_has_small_row (delta : ℝ) {t : Point} (ht : t ∈ discarded delta) :
    ∃ c : Cell, ∃ k : Fin 96, 0 < evalRow (rows c k).2 t ∧ evalRow (rows c k).2 t < delta := by
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht.1
  have hnot : ¬ ∀ k : Fin 96, delta ≤ evalRow (rows c k).2 t := by
    intro h
    exact ht.2 (mem_iUnion.mpr ⟨c, (cell_subset_safeCarrier c hc).1, mem_iInter.mpr h⟩)
  obtain ⟨k, hk⟩ := not_forall.mp hnot
  exact ⟨c, k, hc k, lt_of_not_ge hk⟩

theorem discarded_majorized (n : ℕ) {t : Point} (ht : t ∈ discarded (width n)) :
    1 ≤ wallMajorant n t := by
  obtain ⟨c, k, hp, hs⟩ := discarded_has_small_row _ ht
  exact (rowMajorant_ge_one _ n t hp hs.le).trans
    ((Finset.single_le_sum (fun j _ => (rowMajorant_bounds (rows c j).2 n t).1)
      (Finset.mem_univ k)).trans
        (Finset.single_le_sum (fun d _ => Finset.sum_nonneg
          (fun j _ => (rowMajorant_bounds (rows d j).2 n t).1)) (Finset.mem_univ c)))

def box : Set Point := logPrimeBox (fun _ : Fin 8 => cutoff) (fun _ => mu)

theorem region_subset_box : region ⊆ box := by
  intro t ht
  obtain ⟨c, hc⟩ := mem_iUnion.mp ht
  exact mem_logPrimeBox.mpr (fun i =>
    ⟨(sourceRows_coordinate_bounds c t hc i).1.le, (sourceRows_coordinate_bounds c t hc i).2⟩)

/-- A shrinking, continuous affine-strip majorant has zero limiting
reciprocal-coordinate mass. Every constant-row case has been discharged. -/
theorem tendsto_wallMajorant_integral :
    Tendsto (fun n => ∫ t in box, wallMajorant n t * ∏ i, 1 / t i) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict box) (fun t : Point => wallCount * ∏ i, 1 / t i)
    (fun n => (integrableOn_logPrimeBox_test_cube cutoff_pos _
      (continuous_wallMajorant n).continuousOn).aestronglyMeasurable)
    (integrableOn_logPrimeBox_const_mul_one_div wallCount _ _ (fun _ => cutoff_pos))
    (fun n => by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox _ _)] with t ht
      have hprod : 0 ≤ ∏ i, 1 / t i := Finset.prod_nonneg (fun i _ =>
        (one_div_pos.mpr (cutoff_pos.trans_le (mem_logPrimeBox.mp ht i).1)).le)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (wallMajorant_bounds n t).1,
        abs_of_nonneg hprod]
      exact mul_le_mul_of_nonneg_right (wallMajorant_bounds n t).2 hprod)
    (show ∀ᵐ t ∂volume.restrict box,
      Tendsto (fun n => wallMajorant n t * ∏ i, 1 / t i) atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [ae_restrict_of_ae ae_wallMajorant_tendsto] with t ht
      simpa only [zero_mul] using ht.mul_const (∏ i, 1 / t i))
  simpa only [integral_zero] using ht

def discardedPrimeMass (N : ℕ) (delta : ℝ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff) (fun _ => mu)
    ((discarded delta).indicator (fun _ => 1))

theorem discardedPrimeMass_le_majorant (N n : ℕ) :
    discardedPrimeMass N (width n) ≤
      actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff) (fun _ => mu) (wallMajorant n) := by
  unfold discardedPrimeMass actualPrimeBoxTestSum
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
  by_cases ht : actualPrimeTupleLog N p ∈ discarded (width n)
  · rw [indicator_of_mem ht]; exact discarded_majorized n ht
  · rw [indicator_of_notMem ht]; exact (wallMajorant_bounds n _).1

/-- Both the genuine source integral loss and the ACTUAL target-excluding
prime mass fit a reserve. The trim is fixed before one threshold for all
later targets. Neither a rejected-cost bound nor convergence is an input. -/
theorem exists_common_trim_integral_and_prime_mass
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ,
      (∫ t in discarded (width n), |sourceDensity t|) < epsilon ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        discardedPrimeMass N (width n) < epsilon := by
  have hreal := tendsto_discarded_sourceIntegral.eventually (gt_mem_nhds hepsilon)
  have hwall := tendsto_wallMajorant_integral.eventually (gt_mem_nhds (half_pos hepsilon))
  obtain ⟨n, hnreal, hnwall⟩ := (hreal.and hwall).exists
  have hcut : cutoff < mu := by norm_num [cutoff, mu]
  have hactual := (tendsto_actualPrimeBoxTestSum_cube cutoff_pos hcut (wallMajorant n)
    (continuous_wallMajorant n).continuousOn).eventually
      (gt_mem_nhds (show (∫ t in box, wallMajorant n t * ∏ i, 1 / t i) < epsilon
        by linarith))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hactual
  refine ⟨n, hnreal, max 2 N1, le_max_left _ _, ?_⟩
  intro N hN
  exact (discardedPrimeMass_le_majorant N n).trans_lt (hN1 N ((le_max_right _ _).trans hN))

end
end ImbalancedChen.P2OriginalFourteenWeightedTrim
