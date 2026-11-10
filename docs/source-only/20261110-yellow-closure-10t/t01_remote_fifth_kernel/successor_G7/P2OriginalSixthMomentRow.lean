import ImbalancedChen.P2OriginalSixthSimplexBinding
import ImbalancedChen.P2OriginalSixthHigherMoments

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Actual original G7 SIX-dimensional row, SEVEN physical vertices, EIGHT
positive affine factors. No integral or target-floor premise occurs in
Row. The factor floor53/4608 is the original G7 compact r cutoff.
Mass=abs(det6)/6!*sum7gap/7, weighted means denominator8. The generic
factor-index Q80/Q96 checker and existing log-gap analytic proof are
reused unchanged. Stored witness floors require separate finite checks.
-/
namespace ImbalancedChen.P2OriginalSixthMomentRow
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open P2PositiveAffineSimplexLogJensenSourceOnly
open P2DegreeSixLogGapSoundnessSourceOnly
open P2OriginalLogMomentQ96CheckerSourceOnly
open P2OriginalSixthHigherMoments (rationalMoment rationalMoment_cast realMoment
  integral_interpolate_mul_power)
open P2OriginalSixthSimplexBinding (QPoint castPoint edgeMatrix physicalVolumeQ)
open P2OriginalSixthSimplexBinding (edgeEquiv edge_vertices physicalVolumeQ_cast)

abbrev Point := Fin 6 → ℝ
namespace Bary
export P2OriginalSixthSimplexMoments
  (canonical bary interpolate pointInterpolate interpolate_continuous
   interpolate_bounds interpolate_const interpolate_sub interpolate_div
   vertices support jacobian physicalVolume jacobian_pos physicalVolume_pos
   vertices_interpolate support_compact support_measurable integral_support
   integral_interpolate integral_interpolate_mul)
end Bary

def cutoffQ : ℚ := 53 / 4608
def cutoff : ℝ := 53 / 4608
theorem cutoff_pos : 0 < cutoff := by norm_num [cutoff]
theorem cutoffQ_cast : (cutoffQ : ℝ) = cutoff := by norm_num [cutoffQ, cutoff]

structure Row where
  verticesQ : Fin 7 → QPoint
  gapsQ : Fin 7 → ℚ
  factorsQ : Fin 7 → Fin 8 → ℚ
  determinant_ne_zero : (edgeMatrix verticesQ).det ≠ 0
  gap_nonneg : ∀ i, 0 ≤ gapsQ i
  gapTotal_pos : 0 < ∑ i, gapsQ i
  factor_floor : ∀ i j, cutoffQ ≤ factorsQ i j

def rowMap (r : Row) : Point ≃L[ℝ] Point := edgeEquiv r.verticesQ r.determinant_ne_zero
def rowBase (r : Row) : Point := castPoint (r.verticesQ 0)
def rowCoordinates (r : Row) (t : Point) : Point := (rowMap r).symm (t - rowBase r)
def rowSupport (r : Row) : Set Point := Bary.support (rowMap r) (rowBase r)
def rowGap (r : Row) (t : Point) : ℝ :=
  Bary.interpolate (fun i => (r.gapsQ i : ℝ)) (rowCoordinates r t)
def rowFactors (r : Row) (t : Point) (j : Fin 8) : ℝ :=
  Bary.interpolate (fun i => (r.factorsQ i j : ℝ)) (rowCoordinates r t)
def rowDensity (r : Row) (t : Point) : ℝ := 4 * rowGap r t / ∏ j, rowFactors r t j
def rowMeasure (r : Row) : Measure Point := volume.restrict (rowSupport r)
def rowProbability (r : Row) : Measure Point := weightedProbability (rowMeasure r) (rowGap r)
def rowMassQ (r : Row) : ℚ := physicalVolumeQ r.verticesQ * (∑ i, r.gapsQ i) / 7
def rowMeansQ (r : Row) (j : Fin 8) : ℚ :=
  ((∑ i, r.factorsQ i j) + (∑ i, r.gapsQ i * r.factorsQ i j) / (∑ i, r.gapsQ i)) / 8
def rowTopsQ (r : Row) (j : Fin 8) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin 7 => r.factorsQ i j)
def rowMomentsQ (r : Row) (j : Fin 8) (k : ℕ) : ℚ :=
  rationalMoment r.gapsQ (fun i => 1 - r.factorsQ i j / rowTopsQ r j) k
def rowFloorQ (r : Row) : ℚ :=
  ((max (oldFloorQ96 (rowMassQ r) (rowMeansQ r))
    (newFloorQ96 (rowMassQ r) (rowMeansQ r) (rowMomentsQ r)) : ℤ) : ℚ) / (2 : ℚ)^96

theorem row_vertices (r : Row) :
    Bary.vertices (rowMap r) (rowBase r) = fun i => castPoint (r.verticesQ i) :=
  edge_vertices r.verticesQ r.determinant_ne_zero

theorem rowCoordinates_image (r : Row) (x : Point) :
    rowCoordinates r (rowBase r + rowMap r x) = x := by
  simp [rowCoordinates]

theorem row_pointInterpolate_coordinates (r : Row) (t : Point) :
    Bary.pointInterpolate (fun i => castPoint (r.verticesQ i)) (rowCoordinates r t) = t := by
  rw [← row_vertices, Bary.vertices_interpolate]
  simp [rowCoordinates]

theorem rowGap_image (r : Row) (x : Point) :
    rowGap r (rowBase r + rowMap r x) = Bary.interpolate (fun i => (r.gapsQ i : ℝ)) x := by
  rw [rowGap, rowCoordinates_image]
theorem rowFactors_image (r : Row) (x : Point) (j : Fin 8) :
    rowFactors r (rowBase r + rowMap r x) j =
      Bary.interpolate (fun i => (r.factorsQ i j : ℝ)) x := by
  rw [rowFactors, rowCoordinates_image]

theorem rowDensity_param (r : Row) (x : Point) :
    rowDensity r (rowBase r + rowMap r x) =
      4 * Bary.interpolate (fun i => (r.gapsQ i : ℝ)) x /
        ∏ j, Bary.interpolate (fun i => (r.factorsQ i j : ℝ)) x := by
  simp only [rowDensity, rowGap_image, rowFactors_image]

theorem rowFloorQ_formula (r : Row) :
    rowFloorQ r = ((max (oldFloorQ96 (rowMassQ r) (rowMeansQ r))
      (newFloorQ96 (rowMassQ r) (rowMeansQ r) (rowMomentsQ r)) : ℤ) : ℚ) / (2 : ℚ)^96 := rfl

def checkStoredRowFloor (r : Row) (stored : ℤ) : Bool :=
  checkStoredQ96 stored (rowMassQ r) (rowMeansQ r) (rowMomentsQ r)

theorem row_scaledDeviation_image (r : Row) (top : ℝ) (j : Fin 8) (x : Point) :
    scaledDeviation top (fun t => rowFactors r t j) (rowBase r + rowMap r x) =
      Bary.interpolate (fun i => 1 - (r.factorsQ i j : ℝ) / top) x := by
  simp only [scaledDeviation, rowFactors_image, Bary.interpolate_sub,
    Bary.interpolate_const, Bary.interpolate_div]

theorem continuous_rowGap (r : Row) : Continuous (rowGap r) :=
  (Bary.interpolate_continuous _).comp ((rowMap r).symm.continuous.comp
    (continuous_id.sub continuous_const))
theorem continuous_rowFactor (r : Row) (j : Fin 8) : Continuous (fun t => rowFactors r t j) :=
  (Bary.interpolate_continuous _).comp ((rowMap r).symm.continuous.comp
    (continuous_id.sub continuous_const))

theorem row_gap_nonneg (r : Row) {t : Point} (ht : t ∈ rowSupport r) : 0 ≤ rowGap r t := by
  obtain ⟨x, hx, rfl⟩ := ht
  rw [rowGap_image]
  change 0 ≤ ∑ i, Bary.bary i x * (r.gapsQ i : ℝ)
  exact Finset.sum_nonneg (fun i _ => mul_nonneg
    (P2OriginalSixthSimplexMoments.bary_nonneg hx i) (by exact_mod_cast r.gap_nonneg i))

theorem factor_le_top (r : Row) (i : Fin 7) (j : Fin 8) :
    r.factorsQ i j ≤ rowTopsQ r j :=
  Finset.le_sup' (f := fun i : Fin 7 => r.factorsQ i j) (Finset.mem_univ i)

theorem row_factor_bounds (r : Row) {t : Point} (ht : t ∈ rowSupport r) (j : Fin 8) :
    cutoff ≤ rowFactors r t j ∧ rowFactors r t j ≤ (rowTopsQ r j : ℝ) := by
  obtain ⟨x, hx, rfl⟩ := ht
  rw [rowFactors_image]
  exact Bary.interpolate_bounds _ (fun i => ⟨by
    rw [← cutoffQ_cast]; exact_mod_cast r.factor_floor i j,
    by exact_mod_cast factor_le_top r i j⟩) hx

theorem row_factor_pos (r : Row) {t : Point} (ht : t ∈ rowSupport r) (j : Fin 8) :
    0 < rowFactors r t j := cutoff_pos.trans_le (row_factor_bounds r ht j).1

theorem row_mass_semantics (r : Row) : (rowMassQ r : ℝ) = mass (rowMeasure r) (rowGap r) := by
  change (rowMassQ r : ℝ) = ∫ t in rowSupport r, rowGap r t
  rw [rowSupport, Bary.integral_support]
  simp_rw [rowGap_image]
  rw [Bary.integral_interpolate]
  have hv : (physicalVolumeQ r.verticesQ : ℝ) = Bary.physicalVolume (rowMap r) :=
    physicalVolumeQ_cast r.verticesQ r.determinant_ne_zero
  unfold rowMassQ
  push_cast
  rw [hv]
  dsimp [Bary.physicalVolume]
  norm_num <;> ring

theorem row_mass_pos (r : Row) : 0 < mass (rowMeasure r) (rowGap r) := by
  rw [← row_mass_semantics]
  have hv : (0 : ℝ) < physicalVolumeQ r.verticesQ := by
    rw [physicalVolumeQ_cast r.verticesQ r.determinant_ne_zero]
    exact Bary.physicalVolume_pos _
  have hG : (0 : ℝ) < ∑ i, (r.gapsQ i : ℝ) := by exact_mod_cast r.gapTotal_pos
  unfold rowMassQ
  push_cast
  exact div_pos (mul_pos hv hG) (by norm_num : (0 : ℝ) < 7)

theorem row_means_semantics (r : Row) (j : Fin 8) :
    (rowMeansQ r j : ℝ) = (∫ t, rowGap r t * rowFactors r t j ∂rowMeasure r) /
      mass (rowMeasure r) (rowGap r) := by
  change _ = (∫ t in rowSupport r, rowGap r t * rowFactors r t j) /
    (∫ t in rowSupport r, rowGap r t)
  have hmass : (∫ t in rowSupport r, rowGap r t) = (rowMassQ r : ℝ) :=
    (row_mass_semantics r).symm
  rw [hmass, rowSupport, Bary.integral_support]
  simp_rw [rowGap_image, rowFactors_image]
  rw [Bary.integral_interpolate_mul]
  have hJ := (Bary.jacobian_pos (rowMap r)).ne'
  have hG : (∑ i, (r.gapsQ i : ℝ)) ≠ 0 := by exact_mod_cast r.gapTotal_pos.ne'
  have hv : (physicalVolumeQ r.verticesQ : ℝ) = Bary.physicalVolume (rowMap r) :=
    physicalVolumeQ_cast r.verticesQ r.determinant_ne_zero
  unfold rowMeansQ rowMassQ
  push_cast
  rw [hv]
  dsimp [Bary.physicalVolume]
  norm_num <;> field_simp [hJ, hG] <;> ring

theorem row_means_pos (r : Row) (j : Fin 8) : 0 < rowMeansQ r j := by
  have hc : (0 : ℚ) < cutoffQ := by norm_num [cutoffQ]
  have hf (i : Fin 7) : 0 < r.factorsQ i j := hc.trans_le (r.factor_floor i j)
  unfold rowMeansQ
  apply div_pos _ (by norm_num)
  exact add_pos_of_pos_of_nonneg
    (Finset.sum_pos (fun i _ => hf i) Finset.univ_nonempty)
    (div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (r.gap_nonneg i) (hf i).le))
      r.gapTotal_pos.le)
theorem row_tops_pos (r : Row) (j : Fin 8) : 0 < rowTopsQ r j :=
  ((by norm_num [cutoffQ] : (0 : ℚ) < cutoffQ).trans_le (r.factor_floor 0 j)).trans_le
    (factor_le_top r 0 j)

theorem row_gap_integrable (r : Row) : Integrable (rowGap r) (rowMeasure r) :=
  (continuous_rowGap r).continuousOn.integrableOn_compact (Bary.support_compact _ _)
theorem row_gap_nonneg_ae (r : Row) : ∀ᵐ t ∂rowMeasure r, 0 ≤ rowGap r t := by
  filter_upwards [ae_restrict_mem (Bary.support_measurable (rowMap r) (rowBase r))] with t ht
  exact row_gap_nonneg r ht
theorem row_factors_pos_ae (r : Row) : ∀ᵐ t ∂rowMeasure r, ∀ j, 0 < rowFactors r t j := by
  filter_upwards [ae_restrict_mem (Bary.support_measurable (rowMap r) (rowBase r))] with t ht
  exact row_factor_pos r ht
theorem row_factor_integrable (r : Row) (j : Fin 8) :
    Integrable (fun t => rowGap r t * rowFactors r t j) (rowMeasure r) :=
  ((continuous_rowGap r).mul (continuous_rowFactor r j)).continuousOn.integrableOn_compact
    (Bary.support_compact _ _)
theorem row_log_integrable (r : Row) (j : Fin 8) :
    Integrable (fun t => rowGap r t * Real.log (rowFactors r t j)) (rowMeasure r) :=
  ((continuous_rowGap r).continuousOn.mul ((continuous_rowFactor r j).continuousOn.log
    (fun t ht => (row_factor_pos r ht j).ne'))).integrableOn_compact (Bary.support_compact _ _)
theorem row_reciprocal_integrable (r : Row) :
    Integrable (fun t => rowGap r t / ∏ j, rowFactors r t j) (rowMeasure r) := by
  have hp : Continuous (fun t => ∏ j : Fin 8, rowFactors r t j) :=
    continuous_finsetProd _ (fun j _ => continuous_rowFactor r j)
  exact ((continuous_rowGap r).continuousOn.div hp.continuousOn
    (fun t ht => (Finset.prod_pos (fun j _ => row_factor_pos r ht j)).ne')).integrableOn_compact
      (Bary.support_compact _ _)

theorem row_probability (r : Row) : IsProbabilityMeasure (rowProbability r) :=
  weightedProbability_isProbability _ _ (row_gap_integrable r) (row_gap_nonneg_ae r) (row_mass_pos r)

theorem row_power_integrable (r : Row) (top : ℝ) (j : Fin 8) (k : ℕ) :
    Integrable (fun t => scaledDeviation top (fun t => rowFactors r t j) t ^ k)
      (rowProbability r) := by
  have hc : Continuous (fun t => rowGap r t * scaledDeviation top (fun t => rowFactors r t j) t ^ k) :=
    (continuous_rowGap r).mul ((continuous_const.sub ((continuous_rowFactor r j).div_const top)).pow k)
  exact integrable_weightedProbability _ _ (continuous_rowGap r).measurable
    (row_gap_nonneg_ae r) (row_mass_pos r)
    (hc.continuousOn.integrableOn_compact (Bary.support_compact _ _))

theorem row_moments_semantics (r : Row) (j : Fin 8) (k : ℕ) (hk : k ≤ 6) :
    (rowMomentsQ r j k : ℝ) = ∫ t,
      scaledDeviation (rowTopsQ r j : ℝ) (fun t => rowFactors r t j) t ^ k ∂rowProbability r := by
  rw [rowProbability, integral_weightedProbability _ _ (continuous_rowGap r).measurable
    (row_gap_nonneg_ae r) (row_mass_pos r)]
  change _ = (∫ t in rowSupport r, rowGap r t *
    scaledDeviation (rowTopsQ r j : ℝ) (fun t => rowFactors r t j) t ^ k) /
      (∫ t in rowSupport r, rowGap r t)
  have hmass : (∫ t in rowSupport r, rowGap r t) = (rowMassQ r : ℝ) :=
    (row_mass_semantics r).symm
  rw [hmass, rowSupport, Bary.integral_support]
  simp_rw [rowGap_image, row_scaledDeviation_image]
  rw [integral_interpolate_mul_power _ _ k hk]
  rw [rowMomentsQ, rationalMoment_cast]
  have hJ := (Bary.jacobian_pos (rowMap r)).ne'
  have hG : (∑ i, (r.gapsQ i : ℝ)) ≠ 0 := by exact_mod_cast r.gapTotal_pos.ne'
  have hc : ((7 + k).choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ 7 + k)).ne'
  have hv : (physicalVolumeQ r.verticesQ : ℝ) = Bary.physicalVolume (rowMap r) :=
    physicalVolumeQ_cast r.verticesQ r.determinant_ne_zero
  unfold rowMassQ realMoment
  push_cast
  rw [hv]
  dsimp [Bary.physicalVolume]
  norm_num <;> field_simp [hJ, hG, hc] <;> ring

def rowRangeTop (r : Row) (j : Fin 8) : ℝ := 1 - cutoff / (rowTopsQ r j : ℝ)
theorem rowRangeTop_lt_one (r : Row) (j : Fin 8) : rowRangeTop r j < 1 := by
  have ht : (0 : ℝ) < rowTopsQ r j := by exact_mod_cast row_tops_pos r j
  have h := div_pos cutoff_pos ht
  dsimp [rowRangeTop]
  linarith
theorem row_deviation_range (r : Row) (j : Fin 8) : ∀ᵐ t ∂rowMeasure r,
    scaledDeviation (rowTopsQ r j : ℝ) (fun t => rowFactors r t j) t ∈ Icc 0 (rowRangeTop r j) := by
  filter_upwards [ae_restrict_mem (Bary.support_measurable (rowMap r) (rowBase r))] with t ht
  exact (scaledDeviation_range (by exact_mod_cast row_tops_pos r j) cutoff_pos
    (row_factor_bounds r ht j)).1

theorem row_computed_Q96_sound (r : Row) :
    (simplexLowerQ96 (rowMassQ r) (rowMeansQ r) (rowMomentsQ r) : ℝ) ≤
      ∫ t in rowSupport r, rowDensity r t := by
  have h := simplex_Q96_sound (rowMeasure r) (rowGap r) (fun j t => rowFactors r t j)
    (rowMassQ r) (rowMeansQ r) (rowTopsQ r) (rowMomentsQ r)
    (continuous_rowGap r).measurable (row_gap_integrable r) (row_gap_nonneg_ae r)
    (row_mass_pos r) (row_mass_semantics r) (row_means_pos r) (row_tops_pos r)
    (row_means_semantics r) (row_factors_pos_ae r) (row_factor_integrable r)
    (row_log_integrable r) (row_reciprocal_integrable r)
    (rowRangeTop r) (rowRangeTop_lt_one r) (row_deviation_range r)
    (fun j k _ _ => row_power_integrable r (rowTopsQ r j : ℝ) j k)
    (fun j k _ hk => row_moments_semantics r j k hk)
  simpa only [rowMeasure, rowDensity] using h

theorem row_factor_floor_nonneg (r : Row) (j : Fin 8) :
    0 ≤ factorLowerQ80 (rowMomentsQ r j) := by
  letI : IsProbabilityMeasure (rowProbability r) := row_probability r
  have hr : ∀ᵐ t ∂rowProbability r,
      scaledDeviation (rowTopsQ r j : ℝ) (fun t => rowFactors r t j) t ∈ Icc 0 (rowRangeTop r j) :=
    (withDensity_absolutelyContinuous _ _).ae_le (row_deviation_range r j)
  have hg := probability_gapSix_nonneg (rowProbability r)
    (scaledDeviation (rowTopsQ r j : ℝ) (fun t => rowFactors r t j))
    (hr.mono fun t ht => ht.1)
    (fun k _ _ => row_power_integrable r (rowTopsQ r j : ℝ) j k)
  have he := gapEvaluator_cast (rowProbability r)
    (scaledDeviation (rowTopsQ r j : ℝ) (fun t => rowFactors r t j)) (rowMomentsQ r j)
    (fun k _ hk => row_moments_semantics r j k hk)
  have hgQ : 0 ≤ gapEvaluator (rowMomentsQ r j) := by
    rw [← he] at hg
    exact_mod_cast hg
  exact roundDownQ_nonneg 80 hgQ

theorem rowFloorQ_eq (r : Row) :
    rowFloorQ r = simplexLowerQ96 (rowMassQ r) (rowMeansQ r) (rowMomentsQ r) := by
  have hm : 0 ≤ rowMassQ r := by
    have h := (row_mass_pos r).le
    rw [← row_mass_semantics] at h
    exact_mod_cast h
  have hle := oldFloorQ96_le_newFloorQ96 hm (rowMeansQ r) (row_means_pos r)
    (rowMomentsQ r) (row_factor_floor_nonneg r)
  simp only [rowFloorQ, max_eq_right hle, simplexLowerQ96, roundDownQ, newFloorQ96]

theorem row_floor_sound (r : Row) :
    (rowFloorQ r : ℝ) ≤ ∫ t in rowSupport r, rowDensity r t := by
  rw [rowFloorQ_eq]
  exact row_computed_Q96_sound r

theorem stored_row_floor_sound (r : Row) (stored : ℤ)
    (h : checkStoredRowFloor r stored = true) :
    (stored : ℝ) / (2 : ℝ)^96 ≤ ∫ t in rowSupport r, rowDensity r t := by
  have hq := storedQ96_le_computed stored (rowMassQ r) (rowMeansQ r) (rowMomentsQ r) h
  have hR : (stored : ℝ) / (2 : ℝ)^96 ≤
      (simplexLowerQ96 (rowMassQ r) (rowMeansQ r) (rowMomentsQ r) : ℝ) := by
    exact_mod_cast hq
  exact hR.trans (row_computed_Q96_sound r)

end
end ImbalancedChen.P2OriginalSixthMomentRow
