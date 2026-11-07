import ImbalancedChen.ActualThirdOriginalP4AOrdinaryOuterMinimum

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Original raw fallback for ALL OLD query branches, without the former
ao<=2*z1 zero-clamp restriction. The literal seven-term integer cap lower
bound is proved below the actual gated cap. The original source assertion
ca>x1+y1 pays numerator positivity in the OLD denominator comparison.
No cap/minorant/query/whole-integral upper bound is a hypothesis.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryRawFallbackAllOldSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdP4AOrdinaryEarlyReturnSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

private theorem scale_pos : (0:ℝ)<(D₀:ℝ) := by norm_num

theorem integer_floor_div_cast_le (n d : ℤ) (hd : 0<d) :
    ((n/d:ℤ):ℝ)≤(n:ℝ)/(d:ℝ) := by
  have hf : ⌊(n:ℝ)/(d:ℝ)⌋=n/d := by
    simpa using Int.floor_div_cast_of_nonneg (k:=ℝ) hd.le (n:ℝ)
  have h := Int.floor_le ((n:ℝ)/(d:ℝ))
  simpa only [hf] using h

theorem raw_sum_div_scale (v : Fin 3 → ℤ) (p : Fin 3 → ℚ)
    (hp : ∀ i, p i=(v i:ℚ)/(D₀:ℚ)) (s : TentSum) :
    (rawSum s v:ℝ)/(D₀:ℝ)=tentSum s (realBox p) := by
  have hbind := realBox_grid_binding v p hp
  unfold rawSum tentSum
  rw [hbind 0,hbind 1,hbind 2,←literalTentX_cast s,
    ←literalTentY_cast s,←literalTentZ_cast s]
  push_cast
  ring

/-- Both original floor divisions are retained before taking their minimum. -/
theorem raw_tent_floor_le_v (n : ℤ) :
    (rawTentLower n:ℝ)/(D₀:ℝ)≤VariableEnvelope.v ((n:ℝ)/(D₀:ℝ)) := by
  have hr : (rawTentLower n:ℝ)≤((D₀+n:ℤ):ℝ)/2 := by
    have hm : rawTentLower n≤(D₀+n)/2 := min_le_left _ _
    have hmR : (rawTentLower n:ℝ)≤(((D₀+n)/2:ℤ):ℝ) := by exact_mod_cast hm
    exact hmR.trans (by simpa only [Int.cast_ofNat] using
      integer_floor_div_cast_le (D₀+n) 2 (by norm_num))
  have hf : (rawTentLower n:ℝ)≤((57*D₀-96*n:ℤ):ℝ)/64 := by
    have hm : rawTentLower n≤(57*D₀-96*n)/64 := min_le_right _ _
    have hmR : (rawTentLower n:ℝ)≤(((57*D₀-96*n)/64:ℤ):ℝ) := by exact_mod_cast hm
    exact hmR.trans (by simpa only [Int.cast_ofNat] using
      integer_floor_div_cast_le (57*D₀-96*n) 64 (by norm_num))
  rw [VariableEnvelope.v_eq_min]
  apply le_min
  · calc
      (rawTentLower n:ℝ)/(D₀:ℝ)≤(((D₀+n:ℤ):ℝ)/2)/(D₀:ℝ) :=
        div_le_div_of_nonneg_right hr scale_pos.le
      _=VariableEnvelope.A ((n:ℝ)/(D₀:ℝ)) := by
        unfold VariableEnvelope.A
        push_cast
        field_simp [scale_pos.ne']
        ring
  · calc
      (rawTentLower n:ℝ)/(D₀:ℝ)≤(((57*D₀-96*n:ℤ):ℝ)/64)/(D₀:ℝ) :=
        div_le_div_of_nonneg_right hf scale_pos.le
      _=VariableEnvelope.C ((n:ℝ)/(D₀:ℝ)) := by
        unfold VariableEnvelope.C
        push_cast
        field_simp [scale_pos.ne']
        ring

/-- Endpoint minimum is a genuine whole-interval lower bound even when
the tent crosses mu; no active-side assumption is used. -/
theorem v_endpoint_min_le {l u t : ℝ} (hlt : l≤t) (htu : t≤u) :
    min (VariableEnvelope.v l) (VariableEnvelope.v u)≤VariableEnvelope.v t := by
  have hl : min (VariableEnvelope.v l) (VariableEnvelope.v u)≤VariableEnvelope.A l :=
    (min_le_left _ _).trans (by rw [VariableEnvelope.v_eq_min]; exact min_le_left _ _)
  have hu : min (VariableEnvelope.v l) (VariableEnvelope.v u)≤VariableEnvelope.C u :=
    (min_le_right _ _).trans (by rw [VariableEnvelope.v_eq_min]; exact min_le_right _ _)
  rw [VariableEnvelope.v_eq_min]
  apply le_min
  · exact hl.trans (by unfold VariableEnvelope.A; linarith)
  · exact hu.trans (by unfold VariableEnvelope.C; linarith)

theorem tent_floor_endpoint_min_le (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b) (s : TentSum) {t : BoxPoint}
    (ht : t∈Icc (realBox a) (realBox b)) :
    ((min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)):ℤ):ℝ)/(D₀:ℝ)≤
      VariableEnvelope.v (tentSum s t) := by
  have hl :
      ((min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)):ℤ):ℝ)/(D₀:ℝ)≤
        VariableEnvelope.v (tentSum s (realBox a)) := by
    have hm : min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi))≤
        rawTentLower (rawSum s lo) := min_le_left _ _
    have hmR :
        ((min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)):ℤ):ℝ)≤
          (rawTentLower (rawSum s lo):ℝ) := by exact_mod_cast hm
    have hh := (div_le_div_of_nonneg_right hmR scale_pos.le).trans
      (raw_tent_floor_le_v (rawSum s lo))
    rwa [raw_sum_div_scale lo a g.lower s] at hh
  have hu :
      ((min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)):ℤ):ℝ)/(D₀:ℝ)≤
        VariableEnvelope.v (tentSum s (realBox b)) := by
    have hm : min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi))≤
        rawTentLower (rawSum s hi) := min_le_right _ _
    have hmR :
        ((min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)):ℤ):ℝ)≤
          (rawTentLower (rawSum s hi):ℝ) := by exact_mod_cast hm
    have hh := (div_le_div_of_nonneg_right hmR scale_pos.le).trans
      (raw_tent_floor_le_v (rawSum s hi))
    rwa [raw_sum_div_scale hi b g.upper s] at hh
  exact (le_min hl hu).trans
    (v_endpoint_min_le (tentSum_mono s ht.1) (tentSum_mono s ht.2))

theorem raw_B_floor_le (hi : Fin 3 → ℤ) (b : Fin 3 → ℚ)
    (hb : ∀ i, b i=(hi i:ℚ)/(D₀:ℚ)) {t : BoxPoint} (ht : t≤realBox b) :
    ((((153*D₀-96*hi 2)/256:ℤ):ℝ)/(D₀:ℝ))≤VariableEnvelope.B (t 2) := by
  have hh := div_le_div_of_nonneg_right
    (integer_floor_div_cast_le (153*D₀-96*hi 2) 256 (by norm_num)) scale_pos.le
  have he : (((153*D₀-96*hi 2:ℤ):ℝ)/(256:ℝ))/(D₀:ℝ)=
      VariableEnvelope.B (realBox b 2) := by
    rw [(realBox_grid_binding hi b hb) 2]
    unfold VariableEnvelope.B VariableEnvelope.cap
    push_cast
    field_simp [scale_pos.ne']
    ring
  rw [he] at hh
  exact hh.trans (by unfold VariableEnvelope.B; linarith [ht 2])

theorem normalized_foldr_max_le (zs : List ℤ) (base : ℤ) (u : ℝ)
    (hb : (base:ℝ)/(D₀:ℝ)≤u)
    (hz : ∀ z∈zs, (z:ℝ)/(D₀:ℝ)≤u) :
    ((zs.foldr max base:ℤ):ℝ)/(D₀:ℝ)≤u := by
  revert hz
  induction zs with
  | nil => intro hz; exact hb
  | cons z zs ih =>
      intro hz
      have hh := ih (fun v hv => hz v (List.mem_cons_of_mem z hv))
      change ((max z (zs.foldr max base):ℤ):ℝ)/(D₀:ℝ)≤u
      rcases le_total z (zs.foldr max base) with h | h
      · rw [max_eq_right h]
        exact hh
      · rw [max_eq_left h]
        exact hz z (by simp)

/-- The original seven floor-rounded operands, their maximum and root min
are now proved below the ACTUAL gated buffered cap. -/
theorem original_integer_cap_lower_le_actual (lo hi : Fin 3 → ℤ)
    (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b) {t : BoxPoint}
    (ht : t∈Icc (realBox a) (realBox b)) :
    (sourceCapLower lo hi:ℝ)/(D₀:ℝ)≤
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
  have hz : 0<t 2 := (g.positive 2).trans_le (ht.1 2)
  have hordered : VariableEnvelope.Ordered (t 0) (t 1) (t 2) :=
    ⟨hz.le,(ht.2 2).trans (g.yz.trans (ht.1 1)),
      (ht.2 1).trans (g.xy.trans (ht.1 0)),(ht.2 0).trans g.mu⟩
  have hbase : (((153*D₀-96*hi 2)/256:ℤ):ℝ)/(D₀:ℝ)≤
      VariableEnvelope.six (t 0) (t 1) (t 2) :=
    (raw_B_floor_le hi b g.upper ht.2).trans (VariableEnvelope.B_le_six _ _ _)
  have hterms : ∀ z∈sourceSums.map (fun s =>
      min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi))),
      (z:ℝ)/(D₀:ℝ)≤VariableEnvelope.six (t 0) (t 1) (t 2) := by
    intro z hz
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
    exact (tent_floor_endpoint_min_le lo hi a b g s ht).trans (tent_v_le_six s hordered)
  have hfold := normalized_foldr_max_le _ _ _ hbase hterms
  have hminRight : sourceCapLower lo hi≤
      (sourceSums.map (fun s =>
        min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)))).foldr max
          ((153*D₀-96*hi 2)/256) := min_le_right _ _
  have hminRightR : (sourceCapLower lo hi:ℝ)≤
      (((sourceSums.map (fun s =>
        min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)))).foldr max
          ((153*D₀-96*hi 2)/256):ℤ):ℝ) := by exact_mod_cast hminRight
  have hsix := (div_le_div_of_nonneg_right hminRightR scale_pos.le).trans hfold
  have hminLeft : sourceCapLower lo hi≤T₀ := min_le_left _ _
  have hminLeftR : (sourceCapLower lo hi:ℝ)≤(T₀:ℝ) := by exact_mod_cast hminLeft
  have htheta : (T₀:ℝ)/(D₀:ℝ)=thirdPrefixTheta := by norm_num [thirdPrefixTheta]
  have hroot : (sourceCapLower lo hi:ℝ)/(D₀:ℝ)≤thirdPrefixTheta := by
    rw [← htheta]
    exact div_le_div_of_nonneg_right hminLeftR scale_pos.le
  unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  simp only [mul_zero,sub_zero]
  rw [actualExtendedThirdEnvelope_eq_six hordered]
  exact le_min hroot hsix

theorem original_old_endpoint_cast (lo hi : Fin 3 → ℤ) (b : Fin 3 → ℚ)
    (hb : ∀ i, b i=(hi i:ℚ)/(D₀:ℚ)) (hz : 0<realBox b 2) :
    (oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ)=
      ((sourceCapLower lo hi:ℝ)/(D₀:ℝ)-realBox b 0-realBox b 1)/realBox b 2-1 := by
  have hbind := realBox_grid_binding hi b hb
  have hz0 : (hi 2:ℝ)≠0 := by
    intro h
    have hbad : realBox b 2=0 := by rw [hbind 2,h]; simp
    exact (ne_of_gt hz) hbad
  rw [hbind 0,hbind 1,hbind 2]
  unfold oldLowerNumerator
  push_cast
  field_simp [scale_pos.ne',hz0]
  ring

/-- The producer's actual assert ca>x1+y1 pays the numerator sign. It is
stronger than merely having positive z, and is retained as an integer fact. -/
theorem original_old_endpoint_le_actual (lo hi : Fin 3 → ℤ)
    (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hassert : hi 0+hi 1<sourceCapLower lo hi)
    {t : BoxPoint} (ht : t∈Icc (realBox a) (realBox b)) :
    (oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ)≤actualOldArgument t := by
  have hb := realBox_grid_binding hi b g.upper
  have hassertR : (hi 0:ℝ)+(hi 1:ℝ)<(sourceCapLower lo hi:ℝ) := by exact_mod_cast hassert
  have hn : 0<(sourceCapLower lo hi:ℝ)/(D₀:ℝ)-realBox b 0-realBox b 1 := by
    rw [hb 0,hb 1]
    have hh := div_pos (show 0<(sourceCapLower lo hi:ℝ)-(hi 0:ℝ)-(hi 1:ℝ) by linarith) scale_pos
    simpa only [sub_div] using hh
  have hcap := original_integer_cap_lower_le_actual lo hi a b g ht
  have hnum : (sourceCapLower lo hi:ℝ)/(D₀:ℝ)-realBox b 0-realBox b 1≤
      actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1 := by
    linarith [ht.2 0,ht.2 1]
  have hz : 0<t 2 := (g.positive 2).trans_le (ht.1 2)
  have hdiv := div_le_div₀ (hn.le.trans hnum) hnum hz (ht.2 2)
  rw [original_old_endpoint_cast lo hi b g.upper ((g.positive 2).trans (g.width 2))]
  have he : actualOldArgument t=
      (actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1)/t 2-1 := by
    unfold actualOldArgument
    field_simp [hz.ne']
    ring
  rw [he]
  exact sub_le_sub_right hdiv 1

theorem original_new_pointwise_le_endpoint (lo hi : Fin 3 → ℤ)
    (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    {t : BoxPoint} (ht : t∈Icc (realBox a) (realBox b)) :
    affineArgument thirdPrefixTheta (-1) (-1) (-1) t≤
      (newUpperNumerator lo:ℝ)/(lo 2:ℝ) := by
  have hn : 0≤thirdPrefixTheta-t 0-t 1 := by
    have hb2 : 0<realBox b 2 := (g.positive 2).trans (g.width 2)
    linarith [g.full,ht.2 0,ht.2 1]
  have hnum : thirdPrefixTheta-t 0-t 1≤thirdPrefixTheta-realBox a 0-realBox a 1 := by
    linarith [ht.1 0,ht.1 1]
  have hdiv := div_le_div₀ (hn.trans hnum) hnum (g.positive 2) (ht.1 2)
  rw [original_new_endpoint_cast lo a g.lower (g.positive 2)]
  have he : (thirdPrefixTheta-realBox a 0-realBox a 1-realBox a 2)/realBox a 2=
      (thirdPrefixTheta-realBox a 0-realBox a 1)/realBox a 2-1 := by
    field_simp [(g.positive 2).ne']
    ring
  rw [he]
  simpa only [affineArgument,neg_one_mul,sub_eq_add_neg] using add_le_add_right hdiv (-1)

/-- Original upper NEW read minus original lower OLD read, on ONE immutable
table. All query branches remain certified, including positive OLD and tail. -/
theorem original_raw_pointwise_correction_le (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hassert : hi 0+hi 1<sourceCapLower lo hi)
    {t : BoxPoint} (ht : t∈Icc (realBox a) (realBox b)) :
    actualExtendedThirdLowerFactor (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
      actualExtendedThirdLowerFactor (actualOldArgument t)≤value (rawFallbackHigh table lo hi) := by
  have hal := realBox_grid_binding lo a g.lower
  have hzR : (0:ℝ)<(lo 2:ℝ) := (div_pos_iff_of_pos_right scale_pos).mp
    (by simpa only [hal 2] using g.positive 2)
  have hz : 0<lo 2 := by exact_mod_cast hzR
  have hnewQuery := (CheckedBlockTable.query_encloses_all table
    (newUpperNumerator lo) (lo 2) hz).2
  have holdQuery := (CheckedBlockTable.query_encloses_all table
    (oldLowerNumerator lo hi) (hi 2) (grid_upper_z_positive lo hi a b g)).1
  have hnew : actualExtendedThirdLowerFactor
      (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)≤
      value (readQueryHi160 (assembledRead table.blocks) (newUpperNumerator lo) (lo 2)) := by
    apply (monotone_actualExtendedThirdLowerFactor
      (original_new_pointwise_le_endpoint lo hi a b g ht)).trans
    simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using hnewQuery
  have hold : value (readQueryLo160 (assembledRead table.blocks)
      (oldLowerNumerator lo hi) (hi 2))≤actualExtendedThirdLowerFactor (actualOldArgument t) := by
    have hh : value (readQueryLo160 (assembledRead table.blocks)
        (oldLowerNumerator lo hi) (hi 2))≤
        actualExtendedThirdLowerFactor ((oldLowerNumerator lo hi:ℝ)/(hi 2:ℝ)) := by
      simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using holdQuery
    exact hh.trans (monotone_actualExtendedThirdLowerFactor
      (original_old_endpoint_le_actual lo hi a b g hassert ht))
  have hd := sub_le_sub hnew hold
  have hm :
      value (readQueryHi160 (assembledRead table.blocks) (newUpperNumerator lo) (lo 2))-
        value (readQueryLo160 (assembledRead table.blocks) (oldLowerNumerator lo hi) (hi 2))≤
      value (rawFallbackHigh table lo hi) := by
    simp only [rawFallbackHigh,value_max,value_zero,value_sub]
    exact le_max_right _ _
  exact hd.trans hm

theorem original_raw_all_old_leaf_mean_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      4*boxMass (realBox a) (realBox b)*value (rawFallbackHigh table lo hi) := by
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
  have hh := integral_mono_ae (hnew.sub hold) (integrable_const (value (rawFallbackHigh table lo hi)))
    ((boxProbability_ae_mem (realBox a) (realBox b)).mono
      (fun t ht => original_raw_pointwise_correction_le table lo hi a b g hassert ht))
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  have hrho : realBox b 0≤thirdPrefixRho := g.mu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hs := ordinary_full_box_subset_compact (realBox a) (realBox b) g.positive
    g.cut g.xy g.yz hrho g.full
  rw [inter_eq_right.mpr hs,integral_compactKernel_eq_box_mean (realBox a) (realBox b)
    g.positive g.width]
  exact mul_le_mul_of_nonneg_left hh
    (mul_nonneg (by norm_num) (boxMass_pos (realBox a) (realBox b) g.positive g.width).le)

/-- Complete original raw fallback charge for ALL OLD branches. The original
ca>x1+y1 assertion is the only additional raw arithmetic gate. -/
theorem original_raw_all_old_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p) (rawFallbackHigh table lo hi)) := by
  have hf := original_raw_all_old_leaf_mean_upper table lo hi a b g hassert
  have hm := candidate_mass_upper lo hi a b g p
  have hh0 : 0≤value (rawFallbackHigh table lo hi) := by
    rw [rawFallbackHigh,value_max,value_zero]
    exact le_max_left _ _
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (rawFallbackHigh table lo hi) := hf
    _≤value (candidateMassHi lo hi p)*value (rawFallbackHigh table lo hi) :=
      mul_le_mul_of_nonneg_right hm hh0
    _=value (rawFallbackHigh table lo hi)*value (candidateMassHi lo hi p) := by ring
    _≤value (charge (candidateMassHi lo hi p) (rawFallbackHigh table lo hi)) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

/-- All-OLD replacement for the earlier clamp-only raw/chord minimum.
Both actual suppliers are invoked internally, before the same one mass UP. -/
theorem original_all_old_chord_outer_min_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (husable : usableCandidate hi b p)
    (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (min (rawFallbackHigh table lo hi) (candidateChordHigh table lo hi a b p))) := by
  have hf := original_raw_all_old_integer_upper table lo hi a b g p hassert
  have hj := original_finite_winner_stored_integer_upper table lo hi a b
    g.lower g.upper g.positive g.width g.cut g.xy g.yz g.mu g.full
    g.ratio g.logPositive p hselected husable
  have hj' :
      (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        value (charge (candidateMassHi lo hi p) (candidateChordHigh table lo hi a b p)) := by
    cases p <;> exact hj
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi a b g p),value_min]
  exact le_min hf hj'

theorem original_all_old_early_outer_min_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (hearly : candidateEarlyGuard lo a p)
    (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (min (rawFallbackHigh table lo hi) (candidateEarlyHigh table a b p))) := by
  have hf := original_raw_all_old_integer_upper table lo hi a b g p hassert
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

end
end ImbalancedChen.OriginalThirdP4AOrdinaryRawFallbackAllOldSourceOnly
