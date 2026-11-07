import ImbalancedChen.ActualThirdOriginalBoxMoments


/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Ordinary full-box mean_upper: integrate the OLD lower-endpoint chord, then
subtract it from the NEW Jensen bound. Strict old-range branch 2 <= lo < hi.
Coordinates are physical Fin 3 coordinates. No triangular half-kernel rule.
-/
namespace ImbalancedChen.OriginalThirdOldChordMeanSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdCompactPartitionSourceOnly

def actualOldArgument (t : BoxPoint) : ℝ :=
  (actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1-t 2)/t 2

def oldAffineMean (a b : BoxPoint) (A B C E : ℝ) : ℝ :=
  (A+B*boxEX a b+C*boxEY a b)*boxEZInv a b+E

def oldChordMean (a b : BoxPoint) (A B C E lo hi flo fhi : ℝ) : ℝ :=
  flo+(oldAffineMean a b A B C E-lo)/(hi-lo)*(fhi-flo)

private theorem affine_continuous (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (A B C E : ℝ) :
    ContinuousOn (affineArgument A B C E) (Icc a b) := by
  have h0 : ContinuousOn (fun t : BoxPoint => t 0) (Icc a b) :=
    (continuous_apply 0).continuousOn
  have h1 : ContinuousOn (fun t : BoxPoint => t 1) (Icc a b) :=
    (continuous_apply 1).continuousOn
  have h2 : ContinuousOn (fun t : BoxPoint => t 2) (Icc a b) :=
    (continuous_apply 2).continuousOn
  exact (((continuousOn_const.add (h0.const_mul B)).add (h1.const_mul C)).div h2
    (fun t ht => ((ha 2).trans_le (ht.1 2)).ne')).add continuousOn_const

private theorem measurable_actualOldArgument : Measurable actualOldArgument := by
  have hx : Measurable (fun t : BoxPoint => t 0) := (continuous_apply 0).measurable
  have hy : Measurable (fun t : BoxPoint => t 1) := (continuous_apply 1).measurable
  have hz : Measurable (fun t : BoxPoint => t 2) := (continuous_apply 2).measurable
  exact ((((measurable_actualExtendedThirdBufferedCap 0).sub hx).sub hy).sub hz).div hz

/-- The actual old cap need not be continuous at every cap switch. Its lower
factor is measurable and globally bounded, which is enough for integration. -/
private theorem integrable_actualOldFactor (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) :
    Integrable (fun t => actualExtendedThirdLowerFactor (actualOldArgument t))
      (boxProbability a b) := by
  let : IsProbabilityMeasure (boxProbability a b) :=
    boxProbability_isProbability a b ha hab
  apply Integrable.of_bound
    (measurable_actualExtendedThirdLowerFactor.comp
      measurable_actualOldArgument).aestronglyMeasurable
    (1/(2*Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun t => by
    change ‖actualExtendedThirdLowerFactor (actualOldArgument t)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (actualExtendedThirdLowerFactor_nonneg (actualOldArgument t))]
    exact actualExtendedThirdLowerFactor_le_normalization (actualOldArgument t))

/-- Exact ordinary-box sum moment; no independence claim on an ordered triangle. -/
theorem boxProbability_sum_mean (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) :
    (∫ t, t 0+t 1 ∂boxProbability a b)=boxEX a b+boxEY a b := by
  have hx := integrable_boxProbability_of_continuousOn a b ha hab
    (continuous_apply (0 : Fin 3)).continuousOn
  have hy := integrable_boxProbability_of_continuousOn a b ha hab
    (continuous_apply (1 : Fin 3)).continuousOn
  rw [integral_add hx hy, (boxProbability_moments a b ha hab).1,
    (boxProbability_moments a b ha hab).2.1]

/-- The mixed sum moment, including the true reciprocal-z weighting. -/
theorem boxProbability_sum_div_z_mean (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) :
    (∫ t, (t 0+t 1)/t 2 ∂boxProbability a b)=
      (boxEX a b+boxEY a b)*boxEZInv a b := by
  simpa only [affineArgument, zero_add, one_mul, add_zero] using
    boxProbability_affine_mean a b ha hab 0 1 1 0

/-- Integration of the original lower-query chord is exact. In particular,
flo and fhi are lower endpoints, not upper endpoints and not exact values. -/
theorem integral_old_query_chord (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (A B C E lo hi flo fhi : ℝ) :
    (∫ t, flo+(affineArgument A B C E t-lo)/(hi-lo)*(fhi-flo)
      ∂boxProbability a b)=oldChordMean a b A B C E lo hi flo fhi := by
  let : IsProbabilityMeasure (boxProbability a b) :=
    boxProbability_isProbability a b ha hab
  have hq := integrable_boxProbability_of_continuousOn a b ha hab
    (affine_continuous a b ha A B C E)
  rw [integral_add
    (f := fun _ : BoxPoint => flo)
    (g := fun t : BoxPoint => (affineArgument A B C E t-lo)/(hi-lo)*(fhi-flo))
    (integrable_const flo)
    (((hq.sub (integrable_const lo)).div_const (hi-lo)).mul_const (fhi-flo)),
    integral_mul_const, integral_div,
    integral_sub
      (f := fun t : BoxPoint => affineArgument A B C E t)
      (g := fun _ : BoxPoint => lo) hq (integrable_const lo)]
  simp only [integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  rw [boxProbability_affine_mean a b ha hab]
  rfl

/-- OLD subtraction supplier. The only cell-specific analytic inputs are the
actual cap-minorant geometry and its old range, plus correct endpoint queries. -/
theorem old_query_chord_le_integral_actual (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (A B C E lo hi flo fhi : ℝ)
    (hlo : 2≤lo) (hspan : lo<hi)
    (hrange : ∀ t∈Icc a b, affineArgument A B C E t∈Icc lo hi)
    (hminor : ∀ t∈Icc a b, affineArgument A B C E t≤actualOldArgument t)
    (hfl : flo≤actualExtendedThirdLowerFactor lo)
    (hfh : fhi≤actualExtendedThirdLowerFactor hi) :
    oldChordMean a b A B C E lo hi flo fhi ≤
      ∫ t, actualExtendedThirdLowerFactor (actualOldArgument t) ∂boxProbability a b := by
  let : IsProbabilityMeasure (boxProbability a b) :=
    boxProbability_isProbability a b ha hab
  have hq := integrable_boxProbability_of_continuousOn a b ha hab
    (affine_continuous a b ha A B C E)
  have hc := (integrable_const flo).add
    (((hq.sub (integrable_const lo)).div_const (hi-lo)).mul_const (fhi-flo))
  rw [← integral_old_query_chord a b ha hab]
  apply integral_mono_ae hc (integrable_actualOldFactor a b ha hab)
  filter_upwards [boxProbability_ae_mem a b] with t ht
  exact (actual_lower_query_endpoint_chord hlo hspan (hrange t ht) hfl hfh).trans
    (monotone_actualExtendedThirdLowerFactor (hminor t ht))

/-- Link the real Jensen mean to an outward rational query. The fixed-point
implementation must supply hmean and hquery with its original scaling. -/
theorem actual_new_mean_upper_of_query (a b : BoxPoint) (q : ℚ) (out : ℝ)
    (hmean : (thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1≤(q:ℝ))
    (hquery : actualExtendedThirdLowerFactor (q:ℝ)≤out) :
    actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)≤out := by
  exact (monotone_actualExtendedThirdLowerFactor hmean).trans hquery
/-- The original ordinary full-box Jensen-minus-OLD-chord candidate.
This bounds the actual difference, not merely its new positive term. -/
theorem ordinary_full_box_mean_difference_upper (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (A B C E lo hi flo fhi out : ℝ)
    (hlo : 2≤lo) (hspan : lo<hi)
    (hrange : ∀ t∈Icc a b, affineArgument A B C E t∈Icc lo hi)
    (hminor : ∀ t∈Icc a b, affineArgument A B C E t≤actualOldArgument t)
    (hfl : flo≤actualExtendedThirdLowerFactor lo)
    (hfh : fhi≤actualExtendedThirdLowerFactor hi)
    (hout : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)≤out) :
    (∫ t, actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ∂boxProbability a b) ≤
      max 0 (out-oldChordMean a b A B C E lo hi flo fhi) := by
  have hnew : Integrable (fun t : BoxPoint => actualExtendedThirdLowerFactor
      (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)) (boxProbability a b) :=
    integrable_boxProbability_of_continuousOn a b ha hab
      (continuous_actualExtendedThirdLowerFactor.comp_continuousOn
        (affine_continuous a b ha thirdPrefixTheta (-1) (-1) (-1)))
  rw [integral_sub
    (f := fun t : BoxPoint => actualExtendedThirdLowerFactor
      (affineArgument thirdPrefixTheta (-1) (-1) (-1) t))
    (g := fun t : BoxPoint => actualExtendedThirdLowerFactor (actualOldArgument t))
    hnew (integrable_actualOldFactor a b ha hab)]
  have hu := (ordinary_full_box_new_Jensen a b ha hab hfull).trans hout
  have hl := old_query_chord_le_integral_actual a b ha hab A B C E lo hi flo fhi
    hlo hspan hrange hminor hfl hfh
  exact (sub_le_sub hu hl).trans (le_max_right _ _)

/-- Restore the actual kernel's literal factor 4 and the actual box mass.
No halving of a nonsymmetric kernel integral is used. -/
theorem integral_compactKernel_eq_box_mean (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) :
    (∫ t in Icc a b, compactKernel t)=4*boxMass a b*
      (∫ t, actualExtendedThirdLowerFactor
          (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
        actualExtendedThirdLowerFactor (actualOldArgument t) ∂boxProbability a b) := by
  let g : BoxPoint → ℝ := fun t => actualExtendedThirdLowerFactor
      (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
    actualExtendedThirdLowerFactor (actualOldArgument t)
  have heq : (∫ t in Icc a b, compactKernel t)=
      ∫ t in Icc a b, 4*(boxWeight t*g t) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    have hz : t 2≠0 := ((ha 2).trans_le (ht.1 2)).ne'
    have harg : (thirdPrefixTheta-2*0-t 0-t 1-t 2)/t 2=
        affineArgument thirdPrefixTheta (-1) (-1) (-1) t := by
      unfold affineArgument
      field_simp [hz]
      ring
    dsimp only [compactKernel, actualExtendedThirdOrderedKernel]
    rw [harg]
    change 4*g t/(t 0*t 1*(t 2)^2)=4*(boxWeight t*g t)
    simp only [boxWeight, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, integral_const_mul, integral_boxProbability a b ha hab]
  have hm := (boxMass_pos a b ha hab).ne'
  change 4*(∫ t in Icc a b, boxWeight t*g t)=
    4*boxMass a b*((∫ t in Icc a b, boxWeight t*g t)/boxMass a b)
  field_simp [hm]

/-- A genuine ordinary full leaf in the original compact domain. The majorant
is the mean_upper candidate before fixed-point interval arithmetic and ceil. -/
theorem ordinary_full_leaf_old_chord_upper (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hrho : b 0≤thirdPrefixRho) (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (A B C E lo hi flo fhi out : ℝ)
    (hlo : 2≤lo) (hspan : lo<hi)
    (hrange : ∀ t∈Icc a b, affineArgument A B C E t∈Icc lo hi)
    (hminor : ∀ t∈Icc a b, affineArgument A B C E t≤actualOldArgument t)
    (hfl : flo≤actualExtendedThirdLowerFactor lo)
    (hfh : fhi≤actualExtendedThirdLowerFactor hi)
    (hout : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)≤out) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t) ≤
      4*boxMass a b*max 0 (out-oldChordMean a b A B C E lo hi flo fhi) := by
  have hs := ordinary_full_box_subset_compact a b ha hcut hyx hzy hrho hfull
  rw [inter_eq_right.mpr hs, integral_compactKernel_eq_box_mean a b ha hab]
  exact mul_le_mul_of_nonneg_left
    (ordinary_full_box_mean_difference_upper a b ha hab hfull A B C E lo hi flo fhi out
      hlo hspan hrange hminor hfl hfh hout)
    (mul_nonneg (by norm_num) (boxMass_pos a b ha hab).le)

end
end ImbalancedChen.OriginalThirdOldChordMeanSourceOnly
