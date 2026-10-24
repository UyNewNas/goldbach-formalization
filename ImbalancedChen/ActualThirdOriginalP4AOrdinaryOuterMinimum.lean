import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteDispatch
import ImbalancedChen.ActualThirdOriginalP4AOrdinaryEarlyReturnLeaf

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Actual original outer minimum on the precisely identified subbranch where
the initial OLD fallback query clamps to zero and the always-present clipped
fallback does not tighten it (an integer comparison, not an integral premise).
The two decay gates are then proved false. The initial fallback is supplied
from the actual kernel's NEW integral, its true box expectation, endpoint
monotonicity and the original SAME-reader query. No whole-integral upper
bound is a hypothesis. Chord and high<=2 mean branches use the real sibling
suppliers. The final min stays BEFORE literal mass.hi multiplication and UP.

General OLD-positive initial fallback and genuinely tightening clipped/decay
branches are OPEN here. Their literal operation tree is retained below, but
no unsupported analytic soundness theorem is claimed for them.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryBCandidateSourceOnly
open OriginalThirdP4AOrdinaryEarlyReturnSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

/-- Only primitive grid/geometry/log facts; no target, cap, query, or mass bound. -/
structure OrdinaryGrid (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) : Prop where
  lower : ∀ i, a i=(lo i:ℚ)/(D₀:ℚ)
  upper : ∀ i, b i=(hi i:ℚ)/(D₀:ℚ)
  positive : ∀ i, 0<realBox a i
  width : ∀ i, realBox a i<realBox b i
  cut : (1:ℝ)/100≤realBox a 2
  xy : realBox b 1≤realBox a 0
  yz : realBox b 2≤realBox a 1
  mu : realBox b 0≤VariableEnvelope.mu
  full : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta
  ratio : ∀ i : Fin 2, realBox b i.castSucc/realBox a i.castSucc≤2
  logPositive : ∀ i : Fin 2,
    0<(originalLnUnit (realBox b i.castSucc/realBox a i.castSucc)).lo

def rawTentLower (t : ℤ) : ℤ := min ((D₀+t)/2) ((57*D₀-96*t)/64)

/-- Original below-mu cap_bounds(c)[0], with its seven integer lower operands. -/
def sourceCapLower (lo hi : Fin 3 → ℤ) : ℤ :=
  min T₀ ((sourceSums.map (fun s =>
    min (rawTentLower (rawSum s lo)) (rawTentLower (rawSum s hi)))).foldr max
      ((153*D₀-96*hi 2)/256))

def newUpperNumerator (lo : Fin 3 → ℤ) : ℤ := T₀-lo 0-lo 1-lo 2

def oldLowerNumerator (lo hi : Fin 3 → ℤ) : ℤ :=
  sourceCapLower lo hi-hi 0-hi 1-hi 2

def rawFallbackHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  max 0 (readQueryHi160 (assembledRead table.blocks) (newUpperNumerator lo) (lo 2)-
    readQueryLo160 (assembledRead table.blocks) (oldLowerNumerator lo hi) (hi 2))

def clippedStart (lo hi : Fin 3 → ℤ) : ℤ := max (2*hi 2) (oldLowerNumerator lo hi)

/-- The original always-applied second high candidate, without simplification. -/
def clippedFallbackHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) : ℤ :=
  max 0 (readQueryHi160 (assembledRead table.blocks)
      (clippedStart lo hi*lo 2+(T₀-sourceCapLower lo hi)*hi 2) (hi 2*lo 2)-
    readQueryLo160 (assembledRead table.blocks) (clippedStart lo hi) (hi 2))

/-- Exact order of box()'s pre-mean minima. decay is the original integer
reader operation when instantiated; no soundness of it is assumed or claimed. -/
def sourceFallbackHigh (table : CheckedBlockTable) (decay : ℤ → ℤ → ℤ)
    (lo hi : Fin 3 → ℤ) : ℤ :=
  let ao := oldLowerNumerator lo hi
  let ca := sourceCapLower lo hi
  let h := min (rawFallbackHigh table lo hi) (clippedFallbackHigh table lo hi)
  let h := if 3*hi 2≤ao then min h (decay ao (hi 2)) else h
  if 4*hi 2≤ao then
    min h (up (decay (ao-hi 2) (hi 2)*(T₀-ca)*hi 2) (lo 2*ao)) else h

def charge (massHi high : ℤ) : ℤ := up (high*massHi) P160

theorem up_mono {d a b : ℤ} (hd : 0<d) (hab : a≤b) : up a d≤up b d := by
  unfold up
  exact neg_le_neg (Int.ediv_le_ediv hd (neg_le_neg hab))

theorem charge_mono {massHi h j : ℤ} (hm : 0≤massHi) (hh : h≤j) :
    charge massHi h≤charge massHi j := by
  exact up_mono P160_pos (mul_le_mul_of_nonneg_right hh hm)

/-- This is the exact integer identity needed to keep the minimum before UP. -/
theorem charge_min (massHi h j : ℤ) (hm : 0≤massHi) :
    charge massHi (min h j)=min (charge massHi h) (charge massHi j) := by
  rcases le_total h j with hh | hh
  · rw [min_eq_left hh,min_eq_left (charge_mono hm hh)]
  · rw [min_eq_right hh,min_eq_right (charge_mono hm hh)]

def candidateMassHi (lo hi : Fin 3 → ℤ) : Candidate → ℤ
  | .base => (OriginalThirdBelowMuBMassCeilSourceOnly.literalOrdinaryMass lo hi).hi
  | .tent _ _ => (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryMass lo hi).hi

def candidateChordHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (a b : Fin 3 → ℚ) : Candidate → ℤ
  | .base => baseHigh table a b
  | .tent s k => tentHigh table lo hi a b s k

def candidateEarlyHigh (table : CheckedBlockTable) (a b : Fin 3 → ℚ) : Candidate → ℤ
  | .base => bStoredOut table a b
  | .tent _ _ => tentEarlyOut table (realBox a) (realBox b)

def candidateEarlyGuard (lo : Fin 3 → ℤ) (a : Fin 3 → ℚ) : Candidate → Prop
  | .base => OriginalThirdBelowMuBRoundedSourceOnly.bHighQ a≤2
  | .tent s k => literalTentEndpoint s k lo D₀≤2

theorem candidate_mass_upper (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b) (p : Candidate) :
    4*boxMass (realBox a) (realBox b)≤value (candidateMassHi lo hi p) := by
  have hal := realBox_grid_binding lo a g.lower
  have hbu := realBox_grid_binding hi b g.upper
  cases p with
  | base =>
      exact (OriginalThirdBelowMuBMassCeilSourceOnly.literal_ordinary_mass_encloses
        lo hi (realBox a) (realBox b) hal hbu g.positive g.width
        g.cut g.xy g.yz g.mu).2
  | tent s k =>
      exact (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literal_ordinary_mass_encloses
        lo hi D₀ (realBox a) (realBox b) rfl hal hbu g.positive g.width g.ratio).2

theorem candidate_mass_nonneg (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b) (p : Candidate) : 0≤candidateMassHi lo hi p := by
  have hm := candidate_mass_upper lo hi a b g p
  have hpos := boxMass_pos (realBox a) (realBox b) g.positive g.width
  apply value_le_iff.mp
  rw [value_zero]
  exact (mul_nonneg (by norm_num) hpos.le).trans hm

/-- True reciprocal-box expectation is below the original NEW endpoint query.
The proof uses a pointwise affine range and integrates it under boxProbability. -/
theorem actual_new_mean_le_lower_corner (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta) :
    (thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1≤
      (thirdPrefixTheta-a 0-a 1-a 2)/a 2 := by
  let : IsProbabilityMeasure (boxProbability a b) := boxProbability_isProbability a b ha hab
  have hc : ContinuousOn (affineArgument thirdPrefixTheta (-1) (-1) (-1)) (Icc a b) := by
    have hx : ContinuousOn (fun t : BoxPoint => t 0) (Icc a b) :=
      (continuous_apply 0).continuousOn
    have hy : ContinuousOn (fun t : BoxPoint => t 1) (Icc a b) :=
      (continuous_apply 1).continuousOn
    have hz : ContinuousOn (fun t : BoxPoint => t 2) (Icc a b) :=
      (continuous_apply 2).continuousOn
    exact (((continuousOn_const.add (hx.const_mul (-1))).add
      (hy.const_mul (-1))).div hz
      (fun t ht => ((ha 2).trans_le (ht.1 2)).ne')).add continuousOn_const
  have hi := integrable_boxProbability_of_continuousOn a b ha hab hc
  have hpoint (t : BoxPoint) (ht : t∈Icc a b) :
      affineArgument thirdPrefixTheta (-1) (-1) (-1) t≤
        (thirdPrefixTheta-a 0-a 1)/a 2-1 := by
    have hn : 0≤thirdPrefixTheta-t 0-t 1 := by
      have hb2 : 0<b 2 := (ha 2).trans (hab 2)
      linarith [ht.2 0,ht.2 1]
    have hnum : thirdPrefixTheta-t 0-t 1≤thirdPrefixTheta-a 0-a 1 := by
      linarith [ht.1 0,ht.1 1]
    have hdiv := div_le_div₀ (hn.trans hnum) hnum (ha 2) (ht.1 2)
    simpa only [affineArgument,neg_one_mul,sub_eq_add_neg] using add_le_add_right hdiv (-1)
  have hh := integral_mono_ae hi (integrable_const ((thirdPrefixTheta-a 0-a 1)/a 2-1))
    ((boxProbability_ae_mem a b).mono (fun t ht => hpoint t ht))
  rw [boxProbability_affine_mean a b ha hab thirdPrefixTheta (-1) (-1) (-1)] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,
    neg_one_mul] at hh
  have he : (thirdPrefixTheta-a 0-a 1)/a 2-1=
      (thirdPrefixTheta-a 0-a 1-a 2)/a 2 := by
    field_simp [(ha 2).ne']
    ring
  have hh' : (thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1≤
      (thirdPrefixTheta-a 0-a 1)/a 2-1 := by
    simpa only [sub_eq_add_neg] using hh
  rw [he] at hh'
  exact hh'

theorem original_new_endpoint_cast (lo : Fin 3 → ℤ) (a : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/(D₀:ℚ)) (hz : 0<realBox a 2) :
    (newUpperNumerator lo:ℝ)/(lo 2:ℝ)=
      (thirdPrefixTheta-realBox a 0-realBox a 1-realBox a 2)/realBox a 2 := by
  have hal := realBox_grid_binding lo a haBind
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have hz0 : (lo 2:ℝ)≠0 := by
    intro h
    have hbad : realBox a 2=0 := by rw [hal 2,h]; simp
    exact (ne_of_gt hz) hbad
  have htheta : (T₀:ℝ)=(D₀:ℝ)*thirdPrefixTheta := by norm_num [thirdPrefixTheta]
  rw [hal 0,hal 1,hal 2]
  unfold newUpperNumerator
  push_cast
  rw [htheta]
  field_simp [hD.ne',hz0]
  ring

theorem original_raw_fallback_clamped (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (hclamp : oldLowerNumerator lo hi≤2*hi 2) :
    rawFallbackHigh table lo hi=
      max 0 (readQueryHi160 (assembledRead table.blocks) (newUpperNumerator lo) (lo 2)) := by
  simp only [rawFallbackHigh,readQueryLo160,if_pos hclamp,zero_mul,sub_zero]

/-- First ORIGINAL fallback, actually proved from the kernel/NEW expectation.
The OLD read=0 gate is literal integer arithmetic, not a semantic leaf bound. -/
theorem original_raw_fallback_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hclamp : oldLowerNumerator lo hi≤2*hi 2) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p) (rawFallbackHigh table lo hi)) := by
  have hal := realBox_grid_binding lo a g.lower
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have hzR : (0:ℝ)<(lo 2:ℝ) := (div_pos_iff_of_pos_right hD).mp
    (by simpa only [hal 2] using g.positive 2)
  have hz : 0<lo 2 := by exact_mod_cast hzR
  have hquery := (CheckedBlockTable.query_encloses_all table
    (newUpperNumerator lo) (lo 2) hz).2
  have hquery' : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-realBox a 0-realBox a 1-realBox a 2)/realBox a 2)≤
      value (readQueryHi160 (assembledRead table.blocks) (newUpperNumerator lo) (lo 2)) := by
    rw [← original_new_endpoint_cast lo a g.lower (g.positive 2)]
    simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using hquery
  have hout := (monotone_actualExtendedThirdLowerFactor
    (actual_new_mean_le_lower_corner (realBox a) (realBox b)
      g.positive g.width g.full)).trans hquery'
  have hrho : realBox b 0≤thirdPrefixRho := g.mu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hleaf := ordinary_new_only_leaf_upper (realBox a) (realBox b)
    g.positive g.width g.cut g.xy g.yz hrho g.full _ hout
  have hout0 : 0≤value (readQueryHi160 (assembledRead table.blocks)
      (newUpperNumerator lo) (lo 2)) :=
    (actualExtendedThirdLowerFactor_nonneg _).trans hquery'
  have hraw : value (rawFallbackHigh table lo hi)=
      value (readQueryHi160 (assembledRead table.blocks) (newUpperNumerator lo) (lo 2)) := by
    rw [original_raw_fallback_clamped table lo hi hclamp,value_max,value_zero,
      max_eq_right hout0]
  have hm := candidate_mass_upper lo hi a b g p
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (rawFallbackHigh table lo hi) := by
          simpa only [hraw] using hleaf
    _≤value (candidateMassHi lo hi p)*value (rawFallbackHigh table lo hi) :=
      mul_le_mul_of_nonneg_right hm (by rw [hraw]; exact hout0)
    _=value (rawFallbackHigh table lo hi)*value (candidateMassHi lo hi p) := by ring
    _≤value (charge (candidateMassHi lo hi p) (rawFallbackHigh table lo hi)) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

/-- The exact raw fallback branch cannot enter either decay gate. The clipped
comparison is an explicit integer source check, not an assumed integral bound. -/
theorem sourceFallbackHigh_eq_raw (table : CheckedBlockTable) (decay : ℤ → ℤ → ℤ)
    (lo hi : Fin 3 → ℤ) (hz : 0<hi 2)
    (hclamp : oldLowerNumerator lo hi≤2*hi 2)
    (hnoTighten : rawFallbackHigh table lo hi≤clippedFallbackHigh table lo hi) :
    sourceFallbackHigh table decay lo hi=rawFallbackHigh table lo hi := by
  have h3 : ¬3*hi 2≤oldLowerNumerator lo hi := by omega
  have h4 : ¬4*hi 2≤oldLowerNumerator lo hi := by omega
  simp only [sourceFallbackHigh,if_neg h3,if_neg h4,min_eq_left hnoTighten]

theorem original_chord_outer_min_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (husable : usableCandidate hi b p)
    (hclamp : oldLowerNumerator lo hi≤2*hi 2) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (min (rawFallbackHigh table lo hi) (candidateChordHigh table lo hi a b p))) := by
  have hf := original_raw_fallback_integer_upper table lo hi a b g p hclamp
  have hj := original_finite_winner_stored_integer_upper table lo hi a b
    g.lower g.upper g.positive g.width g.cut g.xy g.yz g.mu g.full
    g.ratio g.logPositive p hselected husable
  have hj' :
      (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        value (charge (candidateMassHi lo hi p) (candidateChordHigh table lo hi a b p)) := by
    cases p <;> exact hj
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi a b g p),value_min]
  exact le_min hf hj'

/-- Early mean_upper branch uses precisely its NEW-only out. OLD fl/fh are
not evaluated, and the initial raw fallback remains the original expression. -/
theorem original_early_outer_min_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (hearly : candidateEarlyGuard lo a p)
    (hclamp : oldLowerNumerator lo hi≤2*hi 2) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (min (rawFallbackHigh table lo hi) (candidateEarlyHigh table a b p))) := by
  have hf := original_raw_fallback_integer_upper table lo hi a b g p hclamp
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

theorem grid_upper_z_positive (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b) : 0<hi 2 := by
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have hbu := realBox_grid_binding hi b g.upper
  have hp : (0:ℝ)<(hi 2:ℝ)/(D₀:ℝ) := by
    simpa only [← hbu 2] using (g.positive 2).trans (g.width 2)
  have hh : (0:ℝ)<(hi 2:ℝ) := (div_pos_iff_of_pos_right hD).mp hp
  exact_mod_cast hh

/-- Final original pre-mean fallback chain and selected chord, through its
ONE literal mass ceiling. The undecayed/no-tightening branch is identified
by raw integer tests; neither fallback nor chord integral bounds are inputs. -/
theorem original_source_chord_outer_charge (table : CheckedBlockTable)
    (decay : ℤ → ℤ → ℤ) (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (husable : usableCandidate hi b p)
    (hclamp : oldLowerNumerator lo hi≤2*hi 2)
    (hnoTighten : rawFallbackHigh table lo hi≤clippedFallbackHigh table lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table decay lo hi)
          (some (candidateChordHigh table lo hi a b p)))) := by
  rw [sourceFallbackHigh_eq_raw table decay lo hi
    (grid_upper_z_positive lo hi a b g) hclamp hnoTighten]
  exact original_chord_outer_min_integer_upper table lo hi a b g p hselected husable hclamp

theorem original_source_early_outer_charge (table : CheckedBlockTable)
    (decay : ℤ → ℤ → ℤ) (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (hearly : candidateEarlyGuard lo a p)
    (hclamp : oldLowerNumerator lo hi≤2*hi 2)
    (hnoTighten : rawFallbackHigh table lo hi≤clippedFallbackHigh table lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table decay lo hi)
          (some (candidateEarlyHigh table a b p)))) := by
  rw [sourceFallbackHigh_eq_raw table decay lo hi
    (grid_upper_z_positive lo hi a b g) hclamp hnoTighten]
  exact original_early_outer_min_integer_upper table lo hi a b g p hselected hearly hclamp

/-- Original None branch retains the fully supplied fallback. This theorem
does not insert the NEW Jensen mean as an extra source candidate. -/
theorem original_source_absent_mean_charge (table : CheckedBlockTable)
    (decay : ℤ → ℤ → ℤ) (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (g : OrdinaryGrid lo hi a b) (p : Candidate)
    (hclamp : oldLowerNumerator lo hi≤2*hi 2)
    (hnoTighten : rawFallbackHigh table lo hi≤clippedFallbackHigh table lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (applyOptionalMean (sourceFallbackHigh table decay lo hi) none)) := by
  rw [sourceFallbackHigh_eq_raw table decay lo hi
    (grid_upper_z_positive lo hi a b g) hclamp hnoTighten]
  exact original_raw_fallback_integer_upper table lo hi a b g p hclamp

end
end ImbalancedChen.OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
