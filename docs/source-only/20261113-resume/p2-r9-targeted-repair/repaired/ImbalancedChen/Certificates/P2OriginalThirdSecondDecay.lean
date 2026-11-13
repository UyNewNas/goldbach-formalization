import ImbalancedChen.ActualThirdOriginalP4AOriginalFirstDecayLeaf
import ImbalancedChen.P4AActualLowerIncrementGapBound

/-!
P2 SOURCE ONLY / UNCOMPILED.
The existing P160 compact-third ordinary leaf's second decay gate, with the SAME
checked reader, actual lower factors, cap floor and literal integer UP.
Reuses the existing derivative/increment, squared-gap anchors, raw/clipped
and first-decay suppliers. No new analytic theorem outside the manuscript,
historical tree, charge list, acceptance proof or P4 noncompact tail is supplied.
-/
namespace ImbalancedChen.P2OriginalThirdSecondDecay
noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdP4AOrdinaryRawFallbackAllOldSourceOnly
open OriginalThirdP4AOriginalClippedGapAssemblySourceOnly
open OriginalThirdP4AOriginalFirstDecayLeafSourceOnly
open OriginalThirdP4AActualLowerIncrementGapBoundSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open P4AOriginalAnchorDecay20261024zSourceOnly

local notation "T₀" => (481573208064:ℤ)

/-- Literal second decay of the existing P160 backend, including its inner UP.
This is not an ABI identity with the adopted historical Q80 charge stream. -/
def secondDecayHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  up (literalDecay table (oldLowerNumerator lo hi-hi 2) (hi 2)*
      (T₀-sourceCapLower lo hi)*hi 2) (lo 2*oldLowerNumerator lo hi)

/-- Four pre-mean candidates in the original left-associated order. -/
def secondDecayPreMeanHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  min (firstDecayPreMeanHigh table lo hi) (secondDecayHigh table lo hi)

theorem second_gate_implies_first (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b) (hgate : 4*hi 2≤oldLowerNumerator lo hi) :
    3*hi 2≤oldLowerNumerator lo hi := by
  have hz := grid_upper_z_positive lo hi a b g
  omega

theorem source_fallback_eq_secondDecay (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 4*hi 2≤oldLowerNumerator lo hi) :
    sourceFallbackHigh table (literalDecay table) lo hi=
      secondDecayPreMeanHigh table lo hi := by
  have h3 := second_gate_implies_first lo hi a b g hgate
  simp only [sourceFallbackHigh,if_pos h3,if_pos hgate,
    secondDecayPreMeanHigh,secondDecayHigh,firstDecayPreMeanHigh,firstDecayHigh]

/-- The gate pays all derivative and anchor domains, including equality at
four. Actual old/new and their increment come from the existing source cap
floor. No desired factor difference, derivative, decay or query bound is input. -/
theorem second_decay_actual_pointwise (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 4*hi 2≤oldLowerNumerator lo hi)
    {t : BoxPoint} (ht : t∈Icc (realBox a) (realBox b)) :
    0≤actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) ∧
    actualExtendedThirdLowerFactor
        (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t)≤
        value (secondDecayHigh table lo hi) := by
  have h3 := second_gate_implies_first lo hi a b g hgate
  have hassert := (first_decay_gate_residual lo hi a b g h3).1
  have hz1 := grid_upper_z_positive lo hi a b g
  have hz1R : (0:ℝ)<(hi 2:ℝ) := by exact_mod_cast hz1
  have hal := realBox_grid_binding lo a g.lower
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have hz0R : (0:ℝ)<(lo 2:ℝ) := (div_pos_iff_of_pos_right hD).mp
    (by simpa only [hal 2] using g.positive 2)
  have hz0 : 0<lo 2 := by exact_mod_cast hz0R
  have hao : 0<oldLowerNumerator lo hi := by omega
  have hgateR : (4:ℝ)*(hi 2:ℝ)≤(oldLowerNumerator lo hi:ℝ) := by
    exact_mod_cast hgate
  have hshift : 3*hi 2≤oldLowerNumerator lo hi-hi 2 := by omega
  have hanchor : canonicalFactorGap
      (((oldLowerNumerator lo hi:ℝ)-(hi 2:ℝ))/(hi 2:ℝ))≤
      value (literalDecay table (oldLowerNumerator lo hi-hi 2) (hi 2)) := by
    simpa only [canonicalFactorGap,Int.cast_sub] using
      normalized_gap_le_literalDecay table (oldLowerNumerator lo hi-hi 2) (hi 2) hz1 hshift
  have hold := original_old_endpoint_le_actual lo hi a b g hassert ht
  have hnew := actual_old_le_new_argument (realBox a) (realBox b) g.positive ht
  have hca : sourceCapLower lo hi≤T₀ := min_le_left _ _
  have hdelta := OriginalThirdP4AOriginalClippedGapSourceOnly.argument_gap_le_original_delta
    lo hi (sourceCapLower lo hi) (realBox a) (realBox b) hal g.positive hca ht
    (original_integer_cap_lower_le_actual lo hi a b g ht)
  have hz : 0<t 2 := (g.positive 2).trans_le (ht.1 2)
  have harg : OriginalThirdP4AOriginalClippedGapSourceOnly.newArgument t=
      affineArgument thirdPrefixTheta (-1) (-1) (-1) t := by
    unfold OriginalThirdP4AOriginalClippedGapSourceOnly.newArgument affineArgument
    field_simp [hz.ne']
    <;> ring
  rw [harg] at hdelta
  have hiBound := actualLowerFactor_increment_le_original_second_decay_anchor
    hz0R hz1R hgateR hold hnew hdelta hanchor
  have hceil := value_div_le_original_up
    (literalDecay table (oldLowerNumerator lo hi-hi 2) (hi 2)*
      (T₀-sourceCapLower lo hi)*hi 2)
    (lo 2*oldLowerNumerator lo hi) (mul_pos hz0 hao)
  have hround :
      value (literalDecay table (oldLowerNumerator lo hi-hi 2) (hi 2))*
        ((T₀-sourceCapLower lo hi:ℤ):ℝ)*(hi 2:ℝ)/
          ((lo 2:ℝ)*(oldLowerNumerator lo hi:ℝ))≤
      value (secondDecayHigh table lo hi) := by
    calc
      _=value (literalDecay table (oldLowerNumerator lo hi-hi 2) (hi 2)*
          (T₀-sourceCapLower lo hi)*hi 2)/((lo 2*oldLowerNumerator lo hi:ℤ):ℝ) := by
        unfold value
        push_cast
        ring
      _≤value (secondDecayHigh table lo hi) := hceil
  exact ⟨sub_nonneg.mpr (monotone_actualExtendedThirdLowerFactor hnew),
    hiBound.trans hround⟩

theorem secondDecayHigh_value_nonneg (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 4*hi 2≤oldLowerNumerator lo hi) :
    0≤value (secondDecayHigh table lo hi) := by
  have ht : realBox a∈Icc (realBox a) (realBox b) :=
    ⟨le_rfl,fun i => (g.width i).le⟩
  have hp := second_decay_actual_pointwise table lo hi a b g hgate ht
  exact hp.1.trans hp.2

/-- Actual full-box probability mean and its integral, retaining factor four,
the original density and the complete compact intersection. -/
theorem second_decay_actual_leaf_mean_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hgate : 4*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      4*boxMass (realBox a) (realBox b)*value (secondDecayHigh table lo hi) := by
  let : IsProbabilityMeasure (boxProbability (realBox a) (realBox b)) :=
    boxProbability_isProbability (realBox a) (realBox b) g.positive g.width
  have hnew := OriginalThirdP4AOrdinaryEarlyReturnSourceOnly.ordinary_factor_integrable (realBox a) (realBox b) g.positive g.width
    (affineArgument thirdPrefixTheta (-1) (-1) (-1)) (by unfold affineArgument; fun_prop)
  have holdMeas : Measurable actualOldArgument := by
    have hx : Measurable (fun t : BoxPoint => t 0) := (continuous_apply 0).measurable
    have hy : Measurable (fun t : BoxPoint => t 1) := (continuous_apply 1).measurable
    have hz : Measurable (fun t : BoxPoint => t 2) := (continuous_apply 2).measurable
    exact ((((measurable_actualExtendedThirdBufferedCap 0).sub hx).sub hy).sub hz).div hz
  have hold := OriginalThirdP4AOrdinaryEarlyReturnSourceOnly.ordinary_factor_integrable (realBox a) (realBox b) g.positive g.width
    actualOldArgument holdMeas
  have hh := integral_mono_ae (hnew.sub hold)
    (integrable_const (value (secondDecayHigh table lo hi)))
    ((boxProbability_ae_mem (realBox a) (realBox b)).mono
      (fun t ht => (second_decay_actual_pointwise table lo hi a b g hgate ht).2))
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  have hrho : realBox b 0≤thirdPrefixRho := g.mu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hs := ordinary_full_box_subset_compact (realBox a) (realBox b) g.positive
    g.cut g.xy g.yz hrho g.full
  rw [inter_eq_right.mpr hs,integral_compactKernel_eq_box_mean (realBox a) (realBox b)
    g.positive g.width]
  exact mul_le_mul_of_nonneg_left hh
    (mul_nonneg (by norm_num) (boxMass_pos (realBox a) (realBox b) g.positive g.width).le)

/-- The original inner decay UP followed by the original mass UP. -/
theorem original_second_decay_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hgate : 4*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p) (secondDecayHigh table lo hi)) := by
  have hf := second_decay_actual_leaf_mean_upper table lo hi a b g hgate
  have hm := candidate_mass_upper lo hi a b g p
  have hh0 := secondDecayHigh_value_nonneg table lo hi a b g hgate
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (secondDecayHigh table lo hi) := hf
    _≤value (candidateMassHi lo hi p)*value (secondDecayHigh table lo hi) :=
      mul_le_mul_of_nonneg_right hm hh0
    _=value (secondDecayHigh table lo hi)*value (candidateMassHi lo hi p) := by ring
    _≤value (charge (candidateMassHi lo hi p) (secondDecayHigh table lo hi)) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

theorem original_second_decay_pre_mean_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hgate : 4*hi 2≤oldLowerNumerator lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p) (secondDecayPreMeanHigh table lo hi)) := by
  unfold secondDecayPreMeanHigh
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi a b g p),value_min]
  exact le_min (original_first_decay_pre_mean_integer_upper table lo hi a b g p
    (second_gate_implies_first lo hi a b g hgate))
    (original_second_decay_integer_upper table lo hi a b g p hgate)

/-- Complete original fallback, for every combination of the two source
gates. The primitive producer assertion remains; no hnotFour restriction,
claimed cap floor, query, decay, mean or leaf-integral bound is an input. -/
theorem original_source_fallback_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (sourceFallbackHigh table (literalDecay table) lo hi)) := by
  by_cases h4 : 4*hi 2≤oldLowerNumerator lo hi
  · rw [source_fallback_eq_secondDecay table lo hi a b g h4]
    exact original_second_decay_pre_mean_integer_upper table lo hi a b g p h4
  · by_cases h3 : 3*hi 2≤oldLowerNumerator lo hi
    · simpa only [sourceFallbackHigh,if_pos h3,if_neg h4,
        firstDecayPreMeanHigh,firstDecayHigh] using
        original_first_decay_pre_mean_integer_upper table lo hi a b g p h3
    · simpa only [sourceFallbackHigh,if_neg h3,if_neg h4] using
        original_raw_clipped_min_integer_upper table lo hi a b g p hassert

/-- The SAME complete pre-mean fallback, optional original selected chord,
selected full mass and final UP. All three decay-gate regions are covered. -/
theorem original_source_chord_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi (48000*2^24) T₀=some p)
    (husable : usableCandidate hi b p) (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table (literalDecay table) lo hi)
          (some (candidateChordHigh table lo hi a b p)))) := by
  have hf := original_source_fallback_integer_upper table lo hi a b g p hassert
  have hj := original_all_old_chord_outer_min_integer_upper table lo hi a b g p
    hselected husable hassert
  have hm := candidate_mass_nonneg lo hi a b g p
  rw [charge_min _ _ _ hm,value_min] at hj
  change (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
    value (charge (candidateMassHi lo hi p)
      (min (sourceFallbackHigh table (literalDecay table) lo hi)
        (candidateChordHigh table lo hi a b p)))
  rw [charge_min _ _ _ hm,value_min]
  exact le_min hf (hj.trans (min_le_right _ _))

theorem original_source_early_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi (48000*2^24) T₀=some p)
    (hearly : candidateEarlyGuard lo a p) (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table (literalDecay table) lo hi)
          (some (candidateEarlyHigh table a b p)))) := by
  have hf := original_source_fallback_integer_upper table lo hi a b g p hassert
  have hj := original_all_old_early_outer_min_integer_upper table lo hi a b g p
    hselected hearly hassert
  have hm := candidate_mass_nonneg lo hi a b g p
  rw [charge_min _ _ _ hm,value_min] at hj
  change (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
    value (charge (candidateMassHi lo hi p)
      (min (sourceFallbackHigh table (literalDecay table) lo hi)
        (candidateEarlyHigh table a b p)))
  rw [charge_min _ _ _ hm,value_min]
  exact le_min hf (hj.trans (min_le_right _ _))

theorem original_source_absent_mean_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table (literalDecay table) lo hi) none)) := by
  exact original_source_fallback_integer_upper table lo hi a b g p hassert

end
end ImbalancedChen.P2OriginalThirdSecondDecay
