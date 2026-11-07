import ImbalancedChen.ActualThirdOriginalP4ASixTentSymmetricLeaf
import ImbalancedChen.ActualThirdOriginalP4AOrdinaryBCandidateLeaf

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
The original B tuple (153,0,0,-96,256) on a symmetric below-mu full leaf.
This is not one of the six tents. The cap minorant is proved on the actual
ordered prism; no impossible ordinary-box b_y <= a_x condition is imposed.
The original signed OLD operations, exact Fraction queries, half mass and
final UP are retained. No leaf/K estimate or query-output order is assumed.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricBLeaf

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly OriginalThirdBelowMuBRoundedSourceOnly
open OriginalThirdP4AOrdinaryBCandidateSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ABalancedSymmetricLeaf
open OriginalThirdP4ASixTentSymmetricLeaf

private theorem prism_mem_ae (a b c d : ℝ) :
    ∀ᵐ p ∂prismProbability a b c d, p∈prismRegion a b c d := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem ((measurableSet_xyTriangle a b).prod measurableSet_Icc))

theorem symmetric_B_residual {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu) :
    0<(153:ℝ)/256-b-b := by
  dsimp [VariableEnvelope.mu] at hmu
  linarith

/-- The actual ordered integration support supplies y<=x. The B(z) plane
survives both the true gated envelope and root minimum below mu. -/
theorem symmetric_B_le_actual_cap {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    {p : PrismPoint} (hp : p∈prismRegion a b c d) :
    VariableEnvelope.B p.2≤actualExtendedThirdBufferedCap 0 p.1.1 p.1.2 p.2 := by
  have hz : 0<p.2 := (symmetric_positive hg).2.trans_le hp.2.1
  have ho : VariableEnvelope.Ordered p.1.1 p.1.2 p.2 :=
    ⟨hz.le,hp.2.2.trans (hg.z_below_xy.trans hp.1.1.2.1),
      hp.1.2,hp.1.1.1.2.trans hmu⟩
  unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  simp only [mul_zero,sub_zero]
  apply le_min
  · dsimp [VariableEnvelope.B,VariableEnvelope.cap,thirdPrefixTheta]
    linarith
  · rw [actualExtendedThirdEnvelope_eq_six ho]
    exact VariableEnvelope.B_le_six p.1.1 p.1.2 p.2

theorem symmetric_B_old_range {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    {p : PrismPoint} (hp : p∈prismRegion a b c d) :
    bOldArgument (prismPoint p)∈Icc
      (bOldLow (symmetricRight b d)) (bOldHigh (symmetricLeft a c)) := by
  have hc := (symmetric_positive hg).2
  have hz : 0<p.2 := hc.trans_le hp.2.1
  have hn := symmetric_B_residual hg hmu
  have hl : (153:ℝ)/256-b-b≤(153:ℝ)/256-p.1.1-p.1.2 := by
    linarith [hp.1.1.1.2,hp.1.1.2.2]
  have hh : (153:ℝ)/256-p.1.1-p.1.2≤(153:ℝ)/256-a-a := by
    linarith [hp.1.1.1.1,hp.1.1.2.1]
  have hdivl := div_le_div₀ (hn.le.trans hl) hl hz hp.2.2
  have hdivh := div_le_div₀ ((hn.le.trans hl).trans hh) hh hc hp.2.1
  constructor
  · simpa only [bOldLow,bOldArgument,affineArgument,symmetricRight,prismPoint,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,neg_one_mul,neg_div,←sub_eq_add_neg] using
      sub_le_sub_right hdivl (11/8)
  · simpa only [bOldHigh,bOldArgument,affineArgument,symmetricLeft,prismPoint,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,neg_one_mul,neg_div,←sub_eq_add_neg] using
      sub_le_sub_right hdivh (11/8)

theorem symmetric_B_old_span {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu) :
    bOldLow (symmetricRight b d)<bOldHigh (symmetricLeft a c) := by
  have hc := (symmetric_positive hg).2
  have hd := hc.trans hg.width_z
  have hn := symmetric_B_residual hg hmu
  have hnumlt : (153:ℝ)/256-b-b<(153:ℝ)/256-a-a := by
    linarith [hg.width_xy]
  have hfirst := (div_lt_div_iff_of_pos_right hd).2 hnumlt
  have hsecond := div_le_div₀ (hn.trans hnumlt).le
    (le_refl ((153:ℝ)/256-a-a)) hc hg.width_z.le
  simpa only [bOldLow,bOldHigh,bOldArgument,affineArgument,symmetricLeft,symmetricRight,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,neg_one_mul,neg_div,←sub_eq_add_neg] using
    sub_lt_sub_right (hfirst.trans_le hsecond) (11/8)

theorem symmetric_B_old_minorant {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    {p : PrismPoint} (hp : p∈prismRegion a b c d) :
    bOldArgument (prismPoint p)≤actualPrismOld p := by
  have hz : 0<p.2 := (symmetric_positive hg).2.trans_le hp.2.1
  have hcap := symmetric_B_le_actual_cap hg hmu hp
  have heq : bOldArgument (prismPoint p)=
      (VariableEnvelope.B p.2-p.1.1-p.1.2-p.2)/p.2 := by
    unfold bOldArgument affineArgument prismPoint VariableEnvelope.B VariableEnvelope.cap
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]
    field_simp [hz.ne'] <;> ring
  rw [heq]
  unfold actualPrismOld
  exact (div_le_div_iff_of_pos_right hz).2 (by linarith)

/-- B has the equal OLD coefficients -1,-1. Hence its true ordered mean
equals the original producer square mean, using E[max]+E[min]=2*squareEx. -/
theorem symmetric_B_old_mean {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    (∫ p, bOldArgument (prismPoint p) ∂prismProbability a b c d)=
      bOldMean (symmetricLeft a c) (symmetricRight b d) := by
  change (∫ p, prismAffine (153/256) (-1) (-1) (-11/8) p
    ∂prismProbability a b c d)=_
  rw [prism_affine_mean hg]
  simp only [bOldMean,symmetricLeft,symmetricRight,boxEX,boxEY,boxEZInv,
    minMean,sumMean,invZMean,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ring

private theorem integrable_B_argument {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu) :
    Integrable (fun p => bOldArgument (prismPoint p)) (prismProbability a b c d) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hm : Measurable (fun p => bOldArgument (prismPoint p)) := by
    change Measurable (prismAffine (153/256) (-1) (-1) (-11/8))
    unfold prismAffine
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable
    (|bOldLow (symmetricRight b d)|+|bOldHigh (symmetricLeft a c)|)
  filter_upwards [prism_mem_ae a b c d] with p hp
  have hr := symmetric_B_old_range hg hmu hp
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (bOldLow (symmetricRight b d)),
      abs_nonneg (bOldHigh (symmetricLeft a c)),hr.1]
  · linarith [le_abs_self (bOldHigh (symmetricLeft a c)),
      abs_nonneg (bOldLow (symmetricRight b d)),hr.2]

private theorem integrable_actual_old {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    Integrable (fun p => actualExtendedThirdLowerFactor (actualPrismOld p))
      (prismProbability a b c d) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hm : Measurable (prismPoint : PrismPoint → BoxPoint) := by
    apply measurable_pi_iff.2
    intro i
    fin_cases i
    · exact measurable_fst.fst
    · exact measurable_fst.snd
    · exact measurable_snd
  have hc := (measurable_actualExtendedThirdBufferedCap 0).comp hm
  have ho : Measurable actualPrismOld :=
    (((hc.sub measurable_fst.fst).sub measurable_fst.snd).sub measurable_snd).div measurable_snd
  apply Integrable.of_bound
    (measurable_actualExtendedThirdLowerFactor.comp ho).aestronglyMeasurable
    (1/(2*Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun p => by
    change ‖actualExtendedThirdLowerFactor (actualPrismOld p)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (actualExtendedThirdLowerFactor_nonneg _)]
    exact actualExtendedThirdLowerFactor_le_normalization _)

theorem symmetric_B_old_mean_mem_range {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu) :
    bOldMean (symmetricLeft a c) (symmetricRight b d)∈Icc
      (bOldLow (symmetricRight b d)) (bOldHigh (symmetricLeft a c)) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hi := integrable_B_argument hg hmu
  have hr : ∀ᵐ p ∂prismProbability a b c d,
      bOldArgument (prismPoint p)∈Icc
        (bOldLow (symmetricRight b d)) (bOldHigh (symmetricLeft a c)) := by
    filter_upwards [prism_mem_ae a b c d] with p hp
    exact symmetric_B_old_range hg hmu hp
  have hl := integral_mono_ae (integrable_const (bOldLow (symmetricRight b d))) hi
    (hr.mono (fun _ h => h.1))
  have hh := integral_mono_ae hi (integrable_const (bOldHigh (symmetricLeft a c)))
    (hr.mono (fun _ h => h.2))
  rw [symmetric_B_old_mean hg] at hl hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hl hh
  exact ⟨hl,hh⟩

/-- The original B producer chord is a genuine actual OLD integral lower
bound. Endpoint-query order is entirely unrestricted. -/
theorem symmetric_B_chord_le_actual_integral {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hlo : 2≤bOldLow (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (bOldLow (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (bOldHigh (symmetricLeft a c))) :
    bOldChord (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hi := integrable_B_argument hg hmu
  have hch := (integrable_const flo).add
    (((hi.sub (integrable_const (bOldLow (symmetricRight b d)))).div_const
      (bOldHigh (symmetricLeft a c)-bOldLow (symmetricRight b d))).mul_const (fhi-flo))
  have hb := integral_mono_ae hch (integrable_actual_old hg) (show
      (fun p => flo+(bOldArgument (prismPoint p)-bOldLow (symmetricRight b d))/
        (bOldHigh (symmetricLeft a c)-bOldLow (symmetricRight b d))*(fhi-flo))
        ≤ᵐ[prismProbability a b c d]
      (fun p => actualExtendedThirdLowerFactor (actualPrismOld p)) from by
    filter_upwards [prism_mem_ae a b c d] with p hp
    exact (actual_lower_query_endpoint_chord hlo (symmetric_B_old_span hg hmu)
      (symmetric_B_old_range hg hmu hp) hfl hfh).trans
      (monotone_actualExtendedThirdLowerFactor (symmetric_B_old_minorant hg hmu hp)))
  rw [integral_add' (integrable_const flo)
    (((hi.sub (integrable_const (bOldLow (symmetricRight b d)))).div_const
      (bOldHigh (symmetricLeft a c)-bOldLow (symmetricRight b d))).mul_const (fhi-flo)),
    integral_mul_const,integral_div,
    integral_sub' hi (integrable_const (bOldLow (symmetricRight b d)))] at hb
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hb
  rw [symmetric_B_old_mean hg] at hb
  exact hb

theorem symmetric_B_exact_leaf_upper {a b c d flo fhi out : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hlo : 2≤bOldLow (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (bOldLow (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (bOldHigh (symmetricLeft a c)))
    (hout : actualExtendedThirdLowerFactor (newMean a b c d)≤out) :
    (∫ t in compactRegion∩symmetricBox a b c d,compactKernel t)≤
      prismMass a b c d*max 0
        (out-bOldChord (symmetricLeft a c) (symmetricRight b d) flo fhi) := by
  exact symmetric_leaf_upper_of_old_chord hg
    (symmetric_B_chord_le_actual_integral hg hmu hlo hfl hfh) hout

/-- Exact signed B OLD expression from the original tuple. In particular
both multiplication operands retain the original interval-left order. -/
def symmetricBOldWeight (a b c d : ℝ) (low high : ℚ) : IV :=
  OriginalThirdBelowMuBRoundedSourceOnly.divRat
    (sub (roundedOld (symmetricLeft a c) (symmetricRight b d)
      (originalLnUnit (b/a)) (originalLnUnit (b/a))) (ofReal (low:ℝ))) (high-low)

theorem symmetric_B_weight_encloses {a b c d : ℝ} (low high : ℚ)
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hlow : (low:ℝ)=bOldLow (symmetricRight b d))
    (hhigh : (high:ℝ)=bOldHigh (symmetricLeft a c))
    (hratio : b/a≤2) (hpositive : 0<(originalLnUnit (b/a)).lo) :
    Encloses (symmetricBOldWeight a b c d low high)
      ((bOldMean (symmetricLeft a c) (symmetricRight b d)-
        bOldLow (symmetricRight b d))/
        (bOldHigh (symmetricLeft a c)-bOldLow (symmetricRight b d))) := by
  have hlog := original_positive256_ln_sound
    ((le_div_iff₀ (symmetric_positive hg).1).2 (by linarith [hg.width_xy])) hratio
  have hm := roundedOld_encloses (a := symmetricLeft a c) (b := symmetricRight b d)
    hlog hlog hpositive hpositive
  have hq : (0:ℚ)<high-low := by
    have hr : (0:ℝ)<((high-low:ℚ):ℝ) := by
      simpa only [Rat.cast_sub,hlow,hhigh] using sub_pos.mpr (symmetric_B_old_span hg hmu)
    exact_mod_cast hr
  simpa only [symmetricBOldWeight,Rat.cast_sub,hlow,hhigh] using
    OriginalThirdBelowMuBRoundedSourceOnly.divRat_sound
      (sub_sound hm (ofReal_sound (low:ℝ))) hq

theorem symmetric_B_rounded_leaf {a b c d : ℝ} (low high : ℚ) (fl fh out : ℤ)
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hlow : (low:ℝ)=bOldLow (symmetricRight b d))
    (hhigh : (high:ℝ)=bOldHigh (symmetricLeft a c))
    (hlo : 2≤(low:ℝ)) (hratio : b/a≤2)
    (hpositive : 0<(originalLnUnit (b/a)).lo)
    (hfl : value fl≤actualExtendedThirdLowerFactor (low:ℝ))
    (hfh : value fh≤actualExtendedThirdLowerFactor (high:ℝ))
    (hout : actualExtendedThirdLowerFactor
      (symmetricNewQuery a b c d (originalLnUnit (b/a)):ℝ)≤value out) :
    (∫ t in compactRegion∩symmetricBox a b c d,compactKernel t)≤
      prismMass a b c d*value (meanHigh
        (symmetricBOldWeight a b c d low high).lo
        (symmetricBOldWeight a b c d low high).hi fl fh out) := by
  have hspan := symmetric_B_old_span hg hmu
  have hr := symmetric_B_old_mean_mem_range hg hmu
  have hw := symmetric_B_weight_encloses low high hg hmu hlow hhigh hratio hpositive
  have hw0 : 0≤(bOldMean (symmetricLeft a c) (symmetricRight b d)-
      bOldLow (symmetricRight b d))/
      (bOldHigh (symmetricLeft a c)-bOldLow (symmetricRight b d)) :=
    div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr hspan).le
  have hw1 : (bOldMean (symmetricLeft a c) (symmetricRight b d)-
      bOldLow (symmetricRight b d))/
      (bOldHigh (symmetricLeft a c)-bOldLow (symmetricRight b d))≤1 :=
    (div_le_one (sub_pos.mpr hspan)).2 (by linarith [hr.2])
  have hround := meanHigh_sound (fl := fl) (fh := fh) (out := out) hw0 hw1 hw.1 hw.2
  have hlog := original_positive256_ln_sound
    ((le_div_iff₀ (symmetric_positive hg).1).2 (by linarith [hg.width_xy])) hratio
  have hnew := actual_new_factor_upper_of_original_query hlog hpositive hout
  have hleaf := symmetric_B_exact_leaf_upper hg hmu
    (by simpa only [←hlow] using hlo)
    (by simpa only [←hlow] using hfl) (by simpa only [←hhigh] using hfh) hnew
  have hc : max 0 (value out-
      bOldChord (symmetricLeft a c) (symmetricRight b d) (value fl) (value fh))≤
      value (meanHigh (symmetricBOldWeight a b c d low high).lo
        (symmetricBOldWeight a b c d low high).hi fl fh out) := by
    simpa only [bOldChord] using hround
  exact hleaf.trans (mul_le_mul_of_nonneg_left hc (symmetric_prism_mass_pos hg).le)

/-- Literal original B Fraction, evaluated at hi for low and lo for high. -/
def savedBLow (x z : ℤ) : ℚ := literalBEndpoint ![x,x,z] (48000*2^24)
def savedBHigh (x z : ℤ) : ℚ := literalBEndpoint ![x,x,z] (48000*2^24)

theorem saved_B_endpoint_cast (x z : ℤ) (a c : ℚ)
    (ha : a=(x:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z:ℚ)/((48000*2^24:ℤ):ℚ)) (hz : 0<z) :
    (literalBEndpoint ![x,x,z] (48000*2^24):ℝ)=
      bOldArgument (symmetricLeft (a:ℝ) (c:ℝ)) := by
  have hb : ∀ i, (![a,a,c] : Fin 3 → ℚ) i=
      (![x,x,z] i:ℚ)/((48000*2^24:ℤ):ℚ) := by
    intro i
    fin_cases i
    · exact ha
    · exact ha
    · exact hc
  have hz' : (![x,x,z] : Fin 3 → ℤ) 2≠0 := by
    simpa only [Matrix.cons_val_two] using hz.ne'
  have heq := literalBEndpoint_eq_bLowQ ![x,x,z] ![a,a,c] hb hz'
  have hcst := congrArg (fun q : ℚ => (q:ℝ)) heq
  rw [cast_bLowQ] at hcst
  exact hcst.symm

theorem saved_B_endpoints_eq (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) :
    (savedBLow x1 z1:ℝ)=bOldLow (symmetricRight (b:ℝ) (d:ℝ)) ∧
      (savedBHigh x0 z0:ℝ)=bOldHigh (symmetricLeft (a:ℝ) (c:ℝ)) := by
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
  exact ⟨saved_B_endpoint_cast x1 z1 b d hb hd hz1,
    saved_B_endpoint_cast x0 z0 a c ha hc hz0⟩

theorem saved_B_span (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) : savedBLow x1 z1<savedBHigh x0 z0 := by
  have he := saved_B_endpoints_eq x0 x1 z0 z1 a b c d ha hb hc hd hg
  have hr : (savedBLow x1 z1:ℝ)<(savedBHigh x0 z0:ℝ) := by
    rw [he.1,he.2]
    exact symmetric_B_old_span hg hmu
  exact_mod_cast hr

/-- The source B root and low_num rejection tests are consequences of the
saved symmetric below-mu geometry, rather than extra semantic hypotheses. -/
theorem saved_B_source_guards (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) :
    153*(48000*2^24:ℤ)-96*z0≤256*481573208064 ∧
      0<153*(48000*2^24:ℤ)-256*x1-256*x1 := by
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have hbR : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hxR : (128:ℝ)*(x1:ℝ)≤25*((48000*2^24:ℤ):ℝ) := by
    have hx := (div_le_iff₀ hD).1
      (by simpa only [hbR,VariableEnvelope.mu] using hmu :
        (x1:ℝ)/((48000*2^24:ℤ):ℝ)≤25/128)
    linarith only [hx]
  have hx : 128*x1≤25*(48000*2^24:ℤ) := by exact_mod_cast hxR
  exact ⟨ordinary_B_literal_root ![x0,x0,z0] hz0.le,
    ordinary_B_literal_residual ![x1,x1,z1] hx hx⟩

/-- Same checked reader, exact OLD rational operands, with the original
unreduced stored NEW.hi/P160 query supplied by the shared source bridge. -/
theorem symmetric_B_three_saved_queries (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) :
    value (readQueryLo160 (assembledRead table.blocks)
      (savedBLow x1 z1).num ((savedBLow x1 z1).den:ℤ))≤
        actualExtendedThirdLowerFactor (bOldLow (symmetricRight (b:ℝ) (d:ℝ))) ∧
    value (readQueryLo160 (assembledRead table.blocks)
      (savedBHigh x0 z0).num ((savedBHigh x0 z0).den:ℤ))≤
        actualExtendedThirdLowerFactor (bOldHigh (symmetricLeft (a:ℝ) (c:ℝ))) ∧
    actualExtendedThirdLowerFactor (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
      (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ)≤value
        (readQueryHi160 (assembledRead table.blocks) (storedGridNew x0 x1 z0 z1).hi P160) := by
  have he := saved_B_endpoints_eq x0 x1 z0 z1 a b c d ha hb hc hd hg
  refine ⟨?_,?_,symmetric_saved_tent_new_query table x0 x1 z0 z1 a b c d ha hb hc hd hg⟩
  · rw [←he.1]
    exact (stored_rat_query_encloses table (savedBLow x1 z1)).1
  · rw [←he.2]
    exact (stored_rat_query_encloses table (savedBHigh x0 z0)).1

def symmetricBCost (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  let low := savedBLow x1 z1
  let high := savedBHigh x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks) (storedGridNew x0 x1 z0 z1).hi P160
  let wt := symmetricBOldWeight (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) low high
  literalSymmetricUpper x0 x1 z0 z1 (meanHigh wt.lo wt.hi fl fh out)

/-- Complete original B symmetric below-mu strict-chord leaf, with all
three SAME-reader factor queries, signed OLD interval operations, clipping,
the original half mass.hi and final integer UP proved internally. -/
theorem original_B_symmetric_stored_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hlow : (2:ℚ)≤savedBLow x1 z1)
    (hratio : x1≤2*x0)
    (hpositive : 0<(originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (symmetricBCost table x0 x1 z0 z1 a b c d) := by
  have he := saved_B_endpoints_eq x0 x1 z0 z1 a b c d ha hb hc hd hg
  have hx0 := positive_grid_binding x0 a ha (symmetric_positive hg).1
  have hx0R : (0:ℝ)<(x0:ℝ) := by exact_mod_cast hx0
  have haR : (a:ℝ)=(x0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [ha]; simp only [Rat.cast_div,Rat.cast_intCast]
  have hbR : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]; simp only [Rat.cast_div,Rat.cast_intCast]
  have hratioEq : (b:ℝ)/(a:ℝ)=(x1:ℝ)/(x0:ℝ) := by
    rw [haR,hbR]
    exact producer_log_ratio _ _ _ (by norm_num) hx0R.ne'
  have hratioR : (x1:ℝ)/(x0:ℝ)≤2 :=
    (div_le_iff₀ hx0R).2 (by exact_mod_cast hratio)
  have hratioPhysical : (b:ℝ)/(a:ℝ)≤2 := by simpa only [hratioEq] using hratioR
  have hpositivePhysical : 0<(originalLnUnit ((b:ℝ)/(a:ℝ))).lo := by
    simpa only [hratioEq] using hpositive
  have hloR : (2:ℝ)≤(savedBLow x1 z1:ℝ) := by exact_mod_cast hlow
  have hqueries := symmetric_B_three_saved_queries table x0 x1 z0 z1 a b c d ha hb hc hd hg
  let wt := symmetricBOldWeight (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
    (savedBLow x1 z1) (savedBHigh x0 z0)
  let fl := readQueryLo160 (assembledRead table.blocks)
    (savedBLow x1 z1).num ((savedBLow x1 z1).den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks)
    (savedBHigh x0 z0).num ((savedBHigh x0 z0).den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks) (storedGridNew x0 x1 z0 z1).hi P160
  have hleaf := symmetric_B_rounded_leaf (savedBLow x1 z1) (savedBHigh x0 z0)
    fl fh out hg hmu he.1 he.2 hloR hratioPhysical hpositivePhysical
    (by rw [he.1]; exact hqueries.1) (by rw [he.2]; exact hqueries.2.1) hqueries.2.2
  have hmass := (literal_symmetric_mass_encloses_ratio x0 x1 z0 z1 a b c d
    ha hb hc hd hg hratioPhysical).2
  have hnonneg : 0≤value (meanHigh wt.lo wt.hi fl fh out) := by
    rw [meanHigh,value_max,value_zero]
    exact le_max_left _ _
  calc
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
        prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*value (meanHigh wt.lo wt.hi fl fh out) := hleaf
    _≤value (literalSymmetricMass x0 x1 z0 z1).hi*value (meanHigh wt.lo wt.hi fl fh out) :=
      mul_le_mul_of_nonneg_right hmass hnonneg
    _=value (meanHigh wt.lo wt.hi fl fh out)*value (literalSymmetricMass x0 x1 z0 z1).hi := by ring
    _≤value (symmetricBCost table x0 x1 z0 z1 a b c d) := by
      exact literal_product_UP_ge _ _

end
end ImbalancedChen.OriginalThirdP4ASymmetricBLeaf
