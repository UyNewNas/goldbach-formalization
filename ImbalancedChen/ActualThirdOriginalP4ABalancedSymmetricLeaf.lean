import ImbalancedChen.ActualThirdOriginalP4ASymmetricTentPrerequisites

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
The original below-mu symmetric xy/xyz strict-chord mean_upper candidate,
through SAME-reader queries, rounded OLD, raw weight, clipping, NEW Jensen,
literal half mass.hi, and the original final integer UP. No above-mu C(x)
leaf theorem is invoked. No desired leaf or K estimate is an assumption.
-/
namespace ImbalancedChen.OriginalThirdP4ABalancedSymmetricLeaf

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdRoundedOldWeightSourceOnly OriginalThirdPositiveLogSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly OriginalThirdP4ASymmetricTentPrerequisites

private theorem prism_mem_ae (a b c d : ℝ) :
    ∀ᵐ p ∂prismProbability a b c d, p∈prismRegion a b c d := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem ((measurableSet_xyTriangle a b).prod measurableSet_Icc))

theorem symmetric_prism_mass_pos {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    0<prismMass a b c d := by
  have hp := symmetric_positive hg
  exact mul_pos (mul_pos (by norm_num) (triangleMass_pos hp.1 hg.width_xy))
    (div_pos (sub_pos.mpr hg.width_z) (mul_pos hp.2 (hp.2.trans hg.width_z)))

private theorem measurable_prism_old : Measurable actualPrismOld := by
  have hm : Measurable (prismPoint : PrismPoint → BoxPoint) := by
    apply measurable_pi_iff.2
    intro i
    fin_cases i
    · exact measurable_fst.fst
    · exact measurable_fst.snd
    · exact measurable_snd
  have hc := (measurable_actualExtendedThirdBufferedCap 0).comp hm
  exact (((hc.sub measurable_fst.fst).sub measurable_fst.snd).sub measurable_snd).div
    measurable_snd

private theorem integrable_factor {a b c d : ℝ} (hg : SymmetricFullBox a b c d)
    (f : PrismPoint → ℝ) (hf : Measurable f) :
    Integrable (fun p => actualExtendedThirdLowerFactor (f p))
      (prismProbability a b c d) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  apply Integrable.of_bound (measurable_actualExtendedThirdLowerFactor.comp hf).aestronglyMeasurable
    (1/(2*Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun p => by
    change ‖actualExtendedThirdLowerFactor (f p)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (actualExtendedThirdLowerFactor_nonneg _)]
    exact actualExtendedThirdLowerFactor_le_normalization _)

private theorem new_argument_range {a b c d : ℝ} (hg : SymmetricFullBox a b c d)
    {p : PrismPoint} (hp : p∈prismRegion a b c d) :
    prismAffine thirdPrefixTheta (-1) (-1) (-1) p∈
      Icc 2 ((thirdPrefixTheta-2*a)/c-1) := by
  have hc := (symmetric_positive hg).2
  have hz : 0<p.2 := hc.trans_le hp.2.1
  have hraw : p.1.1+p.1.2+3*p.2≤thirdPrefixTheta := by
    linarith [hp.1.1.1.2,hp.1.1.2.2,hp.2.2,hg.raw_full]
  have hnum : thirdPrefixTheta-p.1.1-p.1.2≤thirdPrefixTheta-2*a := by
    linarith [hp.1.1.1.1,hp.1.1.2.1]
  have hcap : 0≤thirdPrefixTheta-2*a := by linarith
  have hl := (le_div_iff₀ hz).2
    (show 3*p.2≤thirdPrefixTheta-p.1.1-p.1.2 by linarith)
  have hh := div_le_div₀ hcap hnum hc hp.2.1
  constructor
  · simpa only [prismAffine,neg_one_mul,←sub_eq_add_neg] using
      (show 2≤(thirdPrefixTheta-p.1.1-p.1.2)/p.2-1 by linarith)
  · simpa only [prismAffine,neg_one_mul,←sub_eq_add_neg] using sub_le_sub_right hh 1

private theorem integrable_new_argument {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    Integrable (prismAffine thirdPrefixTheta (-1) (-1) (-1))
      (prismProbability a b c d) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hm : Measurable (prismAffine thirdPrefixTheta (-1) (-1) (-1)) := by
    unfold prismAffine
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (2+|(thirdPrefixTheta-2*a)/c-1|)
  filter_upwards [prism_mem_ae a b c d] with p hp
  have hr := new_argument_range hg hp
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [abs_nonneg ((thirdPrefixTheta-2*a)/c-1),hr.1]
  · linarith [le_abs_self ((thirdPrefixTheta-2*a)/c-1),hr.2]

/-- NEW Jensen on the genuine ordered-prism law, valid on either mu side.
No OLD minorant or fixed C(x) result enters this theorem. -/
theorem symmetric_new_Jensen {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    (∫ p, actualExtendedThirdLowerFactor (prismAffine thirdPrefixTheta (-1) (-1) (-1) p)
      ∂prismProbability a b c d)≤actualExtendedThirdLowerFactor (newMean a b c d) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hm : Measurable (prismAffine thirdPrefixTheta (-1) (-1) (-1)) := by
    unfold prismAffine
    fun_prop
  have hr : ∀ᵐ p ∂prismProbability a b c d,
      2≤prismAffine thirdPrefixTheta (-1) (-1) (-1) p :=
    (prism_mem_ae a b c d).mono (fun _ hp => (new_argument_range hg hp).1)
  have hJ := actual_lower_Jensen_probability (prismProbability a b c d)
    (prismAffine thirdPrefixTheta (-1) (-1) (-1)) hr
    (integrable_new_argument hg) (integrable_factor hg _ hm)
  rw [prism_affine_mean hg] at hJ
  have heq : (thirdPrefixTheta+(-1)*maxMean a b+(-1)*minMean a b)*invZMean c d+(-1)=
      newMean a b c d := by unfold newMean minMean; ring
  rw [heq] at hJ
  exact hJ

/-- True ordered-tent OLD subtraction and NEW Jensen, transported to the
actual Fin3 compact leaf with its original factor4 reciprocal density. -/
theorem symmetric_tent_exact_leaf_upper
    (s : TentSum) (k : TentSide) {a b c d flo fhi out : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlo : 2≤tentOldLow s k (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k (symmetricLeft a c)))
    (hout : actualExtendedThirdLowerFactor (newMean a b c d)≤out) :
    (∫ t in compactRegion∩symmetricBox a b c d,compactKernel t)≤
      prismMass a b c d*max 0 (out-orderedTentChord s k a b c d flo fhi) := by
  have hp := symmetric_positive hg
  let g : PrismPoint → ℝ := fun p => actualExtendedThirdLowerFactor
      (prismAffine thirdPrefixTheta (-1) (-1) (-1) p)-
    actualExtendedThirdLowerFactor (actualPrismOld p)
  have hnewm : Measurable (prismAffine thirdPrefixTheta (-1) (-1) (-1)) := by
    unfold prismAffine
    fun_prop
  have hin := integrable_factor hg _ hnewm
  have hio := integrable_factor hg actualPrismOld measurable_prism_old
  have hOld := symmetric_tent_chord_le_actual_integral s k hg hmu hactive hroot hres hlo hfl hfh
  have hmean : (∫ p, g p ∂prismProbability a b c d)≤
      max 0 (out-orderedTentChord s k a b c d flo fhi) := by
    dsimp only [g]
    rw [integral_sub hin hio]
    exact (sub_le_sub ((symmetric_new_Jensen hg).trans hout) hOld).trans (le_max_right _ _)
  have heq : (∫ p in prismRegion a b c d,compactKernel (prismPoint p))=
      ∫ p in prismRegion a b c d,prismWeight p*g p := by
    apply setIntegral_congr_fun ((measurableSet_xyTriangle a b).prod measurableSet_Icc)
    intro p h
    have hz := (hp.2.trans_le h.2.1).ne'
    have ha : (thirdPrefixTheta-2*0-p.1.1-p.1.2-p.2)/p.2=
        prismAffine thirdPrefixTheta (-1) (-1) (-1) p := by
      unfold prismAffine
      field_simp [hz] <;> ring
    simp only [compactKernel,prismPoint,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,actualExtendedThirdOrderedKernel]
    rw [ha]
    change 4*g p/(p.1.1*p.1.2*p.2^2)=prismWeight p*g p
    simp only [prismWeight,xyWeight,div_eq_mul_inv,mul_inv_rev]
    ring
  have hprob := integral_prismProbability hp.1 hg.width_xy hp.2 hg.width_z g
  rw [compact_inter_symmetricBox a b c d hg,←prism_actual_integral_eq_ordered,
    heq,←(eq_div_iff (symmetric_prism_mass_pos hg).ne').mp hprob]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hmean (symmetric_prism_mass_pos hg).le

theorem ordinary_symmetric_new_eq (a b c d : ℝ) :
    ordinaryNew (symmetricLeft a c) (symmetricRight b d)=
      symmetricNew a b c d (originalLnUnit (b/a)) := by
  rfl

/-- The original square-law mean is inside its OLD endpoint interval. This
supports clipping and uses only the literal rectangular reciprocal law;
it does not assert the square and triangle laws agree in general. -/
theorem balanced_tent_weight_encloses
    (s : TentSum) (k : TentSide) {a b c d : ℝ} (low high : ℚ)
    (hg : SymmetricFullBox a b c d)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlow : (low:ℝ)=tentOldLow s k (symmetricRight b d))
    (hhigh : (high:ℝ)=tentOldHigh s k (symmetricLeft a c))
    (hratio : b/a≤2) (hpositive : 0<(originalLnUnit (b/a)).lo) :
    Encloses (ordinaryTentWeight s k (symmetricLeft a c) (symmetricRight b d) low high)
      ((tentOldMean s k (symmetricLeft a c) (symmetricRight b d)-
        tentOldLow s k (symmetricRight b d))/
        (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d))) := by
  have hratios : ∀ i : Fin 2,
      symmetricRight b d i.castSucc/symmetricLeft a c i.castSucc≤2 := by
    intro i
    fin_cases i <;> exact hratio
  have hpositives : ∀ i : Fin 2,
      0<(originalLnUnit (symmetricRight b d i.castSucc/symmetricLeft a c i.castSucc)).lo := by
    intro i
    fin_cases i <;> exact hpositive
  have hm := ordinary_tent_means_enclose s k (symmetricLeft a c) (symmetricRight b d)
    (symmetric_left_positive hg) (symmetric_widths hg) hratios hpositives
  have hspan := symmetric_tent_span s k hg hres
  have hspanQ : (0:ℚ)<high-low := by
    have hreal : (0:ℝ)<((high-low:ℚ):ℝ) := by
      simpa only [Rat.cast_sub,hlow,hhigh] using sub_pos.mpr hspan
    exact_mod_cast hreal
  simpa only [ordinaryTentWeight,Rat.cast_sub,hlow,hhigh] using
    divRat_sound (sub_sound hm.2 (ofReal_sound (low:ℝ))) hspanQ

/-- Balanced xy/xyz only: original rounded OLD and clipped weight now
majorize the actual ordered-triangle Jensen-minus-chord candidate. -/
theorem balanced_symmetric_rounded_leaf
    (s : TentSum) (k : TentSide) (hs : s=.xy ∨ s=.xyz)
    {a b c d : ℝ} (low high : ℚ) (fl fh out : ℤ)
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlow : (low:ℝ)=tentOldLow s k (symmetricRight b d))
    (hhigh : (high:ℝ)=tentOldHigh s k (symmetricLeft a c))
    (hlo : 2≤(low:ℝ)) (hratio : b/a≤2)
    (hpositive : 0<(originalLnUnit (b/a)).lo)
    (hfl : value fl≤actualExtendedThirdLowerFactor (low:ℝ))
    (hfh : value fh≤actualExtendedThirdLowerFactor (high:ℝ))
    (hout : actualExtendedThirdLowerFactor
      (symmetricNewQuery a b c d (originalLnUnit (b/a)):ℝ)≤value out) :
    (∫ t in compactRegion∩symmetricBox a b c d,compactKernel t)≤
      prismMass a b c d*value (meanHigh
        (ordinaryTentWeight s k (symmetricLeft a c) (symmetricRight b d) low high).lo
        (ordinaryTentWeight s k (symmetricLeft a c) (symmetricRight b d) low high).hi fl fh out) := by
  have hspan := symmetric_tent_span s k hg hres
  have hw := balanced_tent_weight_encloses s k low high hg hres hlow hhigh hratio hpositive
  have hr := tentOldMean_mem_range s k (symmetricLeft a c) (symmetricRight b d)
    (symmetric_left_positive hg) (symmetric_widths hg) hres
  have hw0 : 0≤(tentOldMean s k (symmetricLeft a c) (symmetricRight b d)-
      tentOldLow s k (symmetricRight b d))/
      (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d)) :=
    div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr hspan).le
  have hw1 : (tentOldMean s k (symmetricLeft a c) (symmetricRight b d)-
      tentOldLow s k (symmetricRight b d))/
      (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d))≤1 :=
    (div_le_one (sub_pos.mpr hspan)).2 (by linarith [hr.2])
  have hround := meanHigh_sound (fl:=fl) (fh:=fh) (out:=out) hw0 hw1 hw.1 hw.2
  have hlog := original_positive256_ln_sound
    ((le_div_iff₀ (symmetric_positive hg).1).2 (by linarith [hg.width_xy])) hratio
  have hnew := actual_new_factor_upper_of_original_query hlog hpositive hout
  have hleaf := symmetric_tent_exact_leaf_upper s k hg hmu hactive hroot hres
    (by simpa only [←hlow] using hlo)
    (by simpa only [←hlow] using hfl) (by simpa only [←hhigh] using hfh) hnew
  have hc : max 0 (value out-orderedTentChord s k a b c d (value fl) (value fh))≤
      value (meanHigh
        (ordinaryTentWeight s k (symmetricLeft a c) (symmetricRight b d) low high).lo
        (ordinaryTentWeight s k (symmetricLeft a c) (symmetricRight b d) low high).hi fl fh out) := by
    rw [balanced_tent_chord_eq_producer s k a b c d (value fl) (value fh) hs]
    simpa only [tentOldChord] using hround
  exact hleaf.trans (mul_le_mul_of_nonneg_left hc (symmetric_prism_mass_pos hg).le)

/-- Original literal half-mass operation tree, with the below-mu no-range-
reduction log branch. No above-mu C(x) theorem or target mass bound is used. -/
theorem literal_symmetric_mass_encloses_ratio
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hratio : (b:ℝ)/(a:ℝ)≤2) :
    Encloses (literalSymmetricMass x0 x1 z0 z1)
      (prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) := by
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have haR : (a:ℝ)=(x0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [ha]; simp only [Rat.cast_div,Rat.cast_intCast]
  have hbR : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]; simp only [Rat.cast_div,Rat.cast_intCast]
  have hcR : (c:ℝ)=(z0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hc]; simp only [Rat.cast_div,Rat.cast_intCast]
  have hdR : (d:ℝ)=(z1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hd]; simp only [Rat.cast_div,Rat.cast_intCast]
  have hx0 := positive_grid_binding x0 a ha (symmetric_positive hg).1
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
  have hx0R : (0:ℝ)<(x0:ℝ) := by exact_mod_cast hx0
  have hz0R : (0:ℝ)<(z0:ℝ) := by exact_mod_cast hz0
  have hz1R : (0:ℝ)<(z1:ℝ) := by exact_mod_cast hz1
  have hratioEq : (b:ℝ)/(a:ℝ)=(x1:ℝ)/(x0:ℝ) := by
    rw [haR,hbR]
    exact producer_log_ratio _ _ _ hD.ne' hx0R.ne'
  have hlog : Encloses (originalLnUnit ((x1:ℝ)/(x0:ℝ)))
      (Real.log ((b:ℝ)/(a:ℝ))) := by
    rw [←hratioEq]
    exact original_positive256_ln_sound
      ((le_div_iff₀ (symmetric_positive hg).1).2 (by linarith [hg.width_xy])) hratio
  have hfactor :
      (((4*(48000*2^24:ℤ)*(z1-z0):ℤ):ℝ)/((z0*z1:ℤ):ℝ))=
      4*((d:ℝ)-(c:ℝ))/((c:ℝ)*(d:ℝ)) := by
    rw [hcR,hdR]
    push_cast
    field_simp [hD.ne',hz0R.ne',hz1R.ne'] <;> ring
  have hraw := divNat_sound
    (mul_sound (mul_sound hlog hlog) (literalMassZ_sound hz0 hz1))
    (by norm_num : (0:ℕ)<2)
  have heq : (Real.log ((b:ℝ)/(a:ℝ))*Real.log ((b:ℝ)/(a:ℝ))*
      (((4*(48000*2^24:ℤ)*(z1-z0):ℤ):ℝ)/((z0*z1:ℤ):ℝ)))/2=
      prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) := by
    rw [symmetric_mass_formula,hfactor,pow_two]
  rw [heq] at hraw
  exact hraw

/-- The exact candidate integer with original query operands and original
interval OLD operation tree. This is one candidate, not the box minimum. -/
def balancedSymmetricCost (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  let low := savedTentLow s k x1 z1
  let high := savedTentHigh s k x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks) (storedGridNew x0 x1 z0 z1).hi P160
  let wt := ordinaryTentWeight s k (symmetricLeft (a:ℝ) (c:ℝ))
    (symmetricRight (b:ℝ) (d:ℝ)) low high
  literalSymmetricUpper x0 x1 z0 z1 (meanHigh wt.lo wt.hi fl fh out)

/-- Complete balanced original symmetric strict-chord candidate through its
actual integer cell ceiling. Same-reader queries and all analytic estimates
are proved internally. No hquery, target leaf integral, or K allowance is
assumed. The original selected s/k and its literal tests remain explicit. -/
theorem original_balanced_symmetric_stored_integer_upper
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (hs : s=.xy ∨ s=.xyz) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hbranch : literalSymmetricBranch s k x0 x1 z0 z1)
    (hroot : literalSymmetricRoot s k x0 x1 z0 z1)
    (hres : literalSymmetricResidual s k x1)
    (hlow : (2:ℚ)≤savedTentLow s k x1 z1)
    (hratio : x1≤2*x0)
    (hpositive : 0<(originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (balancedSymmetricCost table s k x0 x1 z0 z1 a b c d) := by
  have hguards := original_selected_tent_guard_bridge s k ![x0,x0,z0] ![x1,x1,z1]
    (48000*2^24) 481573208064
    (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))
    rfl rfl (symmetric_grid_bind x0 z0 a c ha hc) (symmetric_grid_bind x1 z1 b d hb hd)
    (by simpa only [literalSymmetricBranch,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hbranch)
    (by simpa only [literalSymmetricRoot,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hroot)
    (by simpa only [literalSymmetricResidual,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hres)
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
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
  have hloEq : (savedTentLow s k x1 z1:ℝ)=
      tentOldLow s k (symmetricRight (b:ℝ) (d:ℝ)) :=
    saved_tent_endpoint_cast s k x1 z1 b d hb hd hz1
  have hhiEq : (savedTentHigh s k x0 z0:ℝ)=
      tentOldHigh s k (symmetricLeft (a:ℝ) (c:ℝ)) :=
    saved_tent_endpoint_cast s k x0 z0 a c ha hc hz0
  have hloR : (2:ℝ)≤(savedTentLow s k x1 z1:ℝ) := by exact_mod_cast hlow
  have hqueries := symmetric_saved_tent_three_queries table s k x0 x1 z0 z1
  have hnew := symmetric_saved_tent_new_query table x0 x1 z0 z1 a b c d ha hb hc hd hg
  let wt := ordinaryTentWeight s k (symmetricLeft (a:ℝ) (c:ℝ))
    (symmetricRight (b:ℝ) (d:ℝ)) (savedTentLow s k x1 z1) (savedTentHigh s k x0 z0)
  let fl := readQueryLo160 (assembledRead table.blocks)
    (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks)
    (savedTentHigh s k x0 z0).num ((savedTentHigh s k x0 z0).den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks) (storedGridNew x0 x1 z0 z1).hi P160
  have hleaf := balanced_symmetric_rounded_leaf s k hs (savedTentLow s k x1 z1)
    (savedTentHigh s k x0 z0) fl fh out hg hmu hguards.1 hguards.2.1 hguards.2.2
    hloEq hhiEq hloR hratioPhysical hpositivePhysical hqueries.1 hqueries.2.1 hnew
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
    _≤value (balancedSymmetricCost table s k x0 x1 z0 z1 a b c d) := by
      exact literal_product_UP_ge _ _

end
end ImbalancedChen.OriginalThirdP4ABalancedSymmetricLeaf
