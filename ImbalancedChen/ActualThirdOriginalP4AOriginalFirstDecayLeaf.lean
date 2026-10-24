import ImbalancedChen.ActualThirdOriginalP4AOrdinaryRawFallbackAllOld
import ImbalancedChen.ActualThirdOriginalP4AOriginalClippedGapAssembly
import ImbalancedChen.P4AOriginalAnchorDecay

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Actual ordinary consumer of the original FIRST decay candidate:
  if ao>=3*z1: high=min(high,sieve.decay(ao,z1)).
The imported anchor-decay supplier uses the same checked table and actual
canonical gap; no decay enclosure or whole-integral target is a premise.
The original gate itself supplies ca>x1+y1. Full ordinary mass and one final
UP are retained, including the original pre-mean min(raw,clipped,decay).
The second ao>=4*z1 derivative improvement is separate.
-/
namespace ImbalancedChen.OriginalThirdP4AOriginalFirstDecayLeafSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdP4AOrdinaryRawFallbackAllOldSourceOnly
open OriginalThirdP4AOrdinaryEarlyReturnSourceOnly
open OriginalThirdP4AOriginalClippedGapAssemblySourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open P4AOriginalAnchorDecay20261024zSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

/-- Original integer decay call; neither anchor values nor rounding is changed. -/
def firstDecayHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  literalDecay table (oldLowerNumerator lo hi) (hi 2)

def firstDecayPreMeanHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  min (min (rawFallbackHigh table lo hi) (clippedFallbackHigh table lo hi))
    (firstDecayHigh table lo hi)

/-- The original complete pre-mean fallback equals this first-decay stage
when its later four-threshold derivative branch is inactive. -/
theorem source_fallback_eq_firstDecay_of_lt_four (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (hgate : 3*hi 2≤oldLowerNumerator lo hi)
    (hnotFour : oldLowerNumerator lo hi<4*hi 2) :
    sourceFallbackHigh table (literalDecay table) lo hi=firstDecayPreMeanHigh table lo hi := by
  have h4 : ¬4*hi 2≤oldLowerNumerator lo hi := not_le_of_gt hnotFour
  simp only [sourceFallbackHigh,if_pos hgate,if_neg h4,firstDecayPreMeanHigh,firstDecayHigh]

theorem first_decay_gate_residual (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b) (hgate : 3*hi 2≤oldLowerNumerator lo hi) :
    hi 0+hi 1<sourceCapLower lo hi ∧
      (3:ℝ)≤(oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ) := by
  have hz := grid_upper_z_positive lo hi a b g
  have hzR : (0:ℝ)<(hi 2:ℝ) := by exact_mod_cast hz
  constructor
  · unfold oldLowerNumerator at hgate
    omega
  · apply (le_div_iff₀ hzR).2
    exact_mod_cast hgate

theorem actual_old_le_new_argument (a b : BoxPoint)
    (ha : ∀ i, 0<a i) {t : BoxPoint} (ht : t∈Icc a b) :
    actualOldArgument t≤affineArgument thirdPrefixTheta (-1) (-1) (-1) t := by
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hc : actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)≤thirdPrefixTheta := by
    unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
    simp only [mul_zero,sub_zero]
    exact min_le_left _ _
  have hd : (actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1-t 2)/t 2≤
      (thirdPrefixTheta-t 0-t 1-t 2)/t 2 :=
    (div_le_div_iff_of_pos_right hz).2 (by linarith)
  have he : (thirdPrefixTheta-t 0-t 1-t 2)/t 2=
      affineArgument thirdPrefixTheta (-1) (-1) (-1) t := by
    unfold affineArgument
    field_simp [hz.ne']
    ring
  simpa only [actualOldArgument,he] using hd

/-- Genuine factor comparison before the anchor supplier is applied. The
actual cap root gives OLD<=NEW; the cap-floor supplier gives s0<=OLD. -/
theorem first_decay_actual_correction_le_normalized_gap (lo hi : Fin 3 → ℤ)
    (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 3*hi 2≤oldLowerNumerator lo hi)
    {t : BoxPoint} (ht : t∈Icc (realBox a) (realBox b)) :
    0≤actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ∧
    actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t)≤
        upper ((oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ))-
          lower ((oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ)) := by
  obtain ⟨hassert,hs0⟩ := first_decay_gate_residual lo hi a b g hgate
  have hOld := original_old_endpoint_le_actual lo hi a b g hassert ht
  have hNew := actual_old_le_new_argument (realBox a) (realBox b) g.positive ht
  have hs0new := hOld.trans hNew
  have hs02 : (2:ℝ)≤(oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ) := by linarith
  have hnew2 : (2:ℝ)≤affineArgument thirdPrefixTheta (-1) (-1) (-1) t :=
    hs02.trans hs0new
  have hfactorUpper : actualExtendedThirdLowerFactor
      (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)≤
      upper (affineArgument thirdPrefixTheta (-1) (-1) (-1) t) := by
    rw [← lower_eq_actual hnew2]
    exact lower_le_upper hnew2
  have hUpper := upper_antitone hs02 hnew2 hs0new
  have hLower : lower ((oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ))≤
      actualExtendedThirdLowerFactor (actualOldArgument t) :=
    (lower_eq_actual hs02).le.trans (monotone_actualExtendedThirdLowerFactor hOld)
  exact ⟨sub_nonneg.mpr (monotone_actualExtendedThirdLowerFactor hNew),
    sub_le_sub (hfactorUpper.trans hUpper) hLower⟩

/-- The anchor table and squared-gap source proof are consumed here, not
accepted as desired decay premises. The original integer guard is unchanged. -/
theorem first_decay_actual_pointwise (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 3*hi 2≤oldLowerNumerator lo hi)
    {t : BoxPoint} (ht : t∈Icc (realBox a) (realBox b)) :
    0≤actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ∧
    actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t)≤value (firstDecayHigh table lo hi) := by
  have hc := first_decay_actual_correction_le_normalized_gap lo hi a b g hgate ht
  have ha := normalized_gap_le_literalDecay table (oldLowerNumerator lo hi) (hi 2)
    (grid_upper_z_positive lo hi a b g) hgate
  exact ⟨hc.1,hc.2.trans ha⟩

theorem firstDecayHigh_value_nonneg (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 3*hi 2≤oldLowerNumerator lo hi) : 0≤value (firstDecayHigh table lo hi) := by
  have hs0 := (first_decay_gate_residual lo hi a b g hgate).2
  have hs02 : (2:ℝ)≤(oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ) := by linarith
  exact (sub_nonneg.mpr (lower_le_upper hs02)).trans
    (normalized_gap_le_literalDecay table (oldLowerNumerator lo hi) (hi 2)
      (grid_upper_z_positive lo hi a b g) hgate)

theorem first_decay_actual_leaf_mean_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 3*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      4*boxMass (realBox a) (realBox b)*value (firstDecayHigh table lo hi) := by
  let : IsProbabilityMeasure (boxProbability (realBox a) (realBox b)) :=
    boxProbability_isProbability (realBox a) (realBox b) g.positive g.width
  have hnew := ordinary_factor_integrable (realBox a) (realBox b) g.positive g.width
    (affineArgument thirdPrefixTheta (-1) (-1) (-1)) (by unfold affineArgument; fun_prop)
  have holdMeas : Measurable actualOldArgument := by
    have hx : Measurable (fun t : BoxPoint => t 0) := (continuous_apply 0).measurable
    have hy : Measurable (fun t : BoxPoint => t 1) := (continuous_apply 1).measurable
    have hz : Measurable (fun t : BoxPoint => t 2) := (continuous_apply 2).measurable
    exact ((((measurable_actualExtendedThirdBufferedCap 0).sub hx).sub hy).sub hz).div hz
  have hold := ordinary_factor_integrable (realBox a) (realBox b) g.positive g.width
    actualOldArgument holdMeas
  have hh := integral_mono_ae (hnew.sub hold) (integrable_const (value (firstDecayHigh table lo hi)))
    ((boxProbability_ae_mem (realBox a) (realBox b)).mono
      (fun t ht => (first_decay_actual_pointwise table lo hi a b g hgate ht).2))
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  have hrho : realBox b 0≤thirdPrefixRho := g.mu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hs := ordinary_full_box_subset_compact (realBox a) (realBox b) g.positive
    g.cut g.xy g.yz hrho g.full
  rw [inter_eq_right.mpr hs,integral_compactKernel_eq_box_mean (realBox a) (realBox b)
    g.positive g.width]
  exact mul_le_mul_of_nonneg_left hh
    (mul_nonneg (by norm_num) (boxMass_pos (realBox a) (realBox b) g.positive g.width).le)

/-- Original standalone first-decay charge, through the unchanged full mass.
There is no extra ceiling between literalDecay and the original final UP. -/
theorem original_first_decay_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hgate : 3*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p) (firstDecayHigh table lo hi)) := by
  have hf := first_decay_actual_leaf_mean_upper table lo hi a b g hgate
  have hm := candidate_mass_upper lo hi a b g p
  have hh0 := firstDecayHigh_value_nonneg table lo hi a b g hgate
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (firstDecayHigh table lo hi) := hf
    _≤value (candidateMassHi lo hi p)*value (firstDecayHigh table lo hi) :=
      mul_le_mul_of_nonneg_right hm hh0
    _=value (firstDecayHigh table lo hi)*value (candidateMassHi lo hi p) := by ring
    _≤value (charge (candidateMassHi lo hi p) (firstDecayHigh table lo hi)) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

/-- The source's exact first-decay min: raw, clipped, then literalDecay.
Each analytic supplier is invoked internally; no leaf bound is a premise. -/
theorem original_first_decay_pre_mean_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hgate : 3*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p) (firstDecayPreMeanHigh table lo hi)) := by
  have hassert := (first_decay_gate_residual lo hi a b g hgate).1
  unfold firstDecayPreMeanHigh
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi a b g p),value_min]
  exact le_min (original_raw_clipped_min_integer_upper table lo hi a b g p hassert)
    (original_first_decay_integer_upper table lo hi a b g p hgate)

theorem original_first_decay_chord_outer_charge (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (husable : usableCandidate hi b p) (hgate : 3*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (min (firstDecayPreMeanHigh table lo hi) (candidateChordHigh table lo hi a b p))) := by
  have hf := original_first_decay_pre_mean_integer_upper table lo hi a b g p hgate
  have hj := original_finite_winner_stored_integer_upper table lo hi a b
    g.lower g.upper g.positive g.width g.cut g.xy g.yz g.mu g.full
    g.ratio g.logPositive p hselected husable
  have hj' :
      (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        value (charge (candidateMassHi lo hi p) (candidateChordHigh table lo hi a b p)) := by
    cases p <;> exact hj
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi a b g p),value_min]
  exact le_min hf hj'

theorem original_first_decay_early_outer_charge (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (hearly : candidateEarlyGuard lo a p) (hgate : 3*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (min (firstDecayPreMeanHigh table lo hi) (candidateEarlyHigh table a b p))) := by
  have hf := original_first_decay_pre_mean_integer_upper table lo hi a b g p hgate
  have hj :
      (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        value (charge (candidateMassHi lo hi p) (candidateEarlyHigh table a b p)) := by
    cases p with
    | base =>
        exact ordinary_B_high_le_two_integer_upper table lo hi a b g.lower g.upper
          g.positive g.width g.cut g.xy g.yz g.mu g.full hearly
    | tent s k =>
        exact (ordinary_tent_high_le_two_integer_upper table s k lo hi D₀
          (realBox a) (realBox b) rfl
          (realBox_grid_binding lo a g.lower) (realBox_grid_binding hi b g.upper)
          g.positive g.width g.cut g.xy g.yz g.mu g.full g.ratio g.logPositive hearly).2
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi a b g p),value_min]
  exact le_min hf hj

theorem original_source_first_decay_chord_charge (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (husable : usableCandidate hi b p) (hgate : 3*hi 2≤oldLowerNumerator lo hi)
    (hnotFour : oldLowerNumerator lo hi<4*hi 2) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table (literalDecay table) lo hi)
          (some (candidateChordHigh table lo hi a b p)))) := by
  rw [source_fallback_eq_firstDecay_of_lt_four table lo hi hgate hnotFour]
  exact original_first_decay_chord_outer_charge table lo hi a b g p hselected husable hgate

theorem original_source_first_decay_absent_mean_charge (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hgate : 3*hi 2≤oldLowerNumerator lo hi)
    (hnotFour : oldLowerNumerator lo hi<4*hi 2) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table (literalDecay table) lo hi) none)) := by
  rw [source_fallback_eq_firstDecay_of_lt_four table lo hi hgate hnotFour]
  exact original_first_decay_pre_mean_integer_upper table lo hi a b g p hgate

end
end ImbalancedChen.OriginalThirdP4AOriginalFirstDecayLeafSourceOnly
