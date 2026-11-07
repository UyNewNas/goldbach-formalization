import ImbalancedChen.ActualThirdOriginalP4AOrdinaryBCandidateLeaf
import ImbalancedChen.ActualThirdOriginalSixTentOrdinaryMassCeil

/-!
SOURCEONLY / UNCOMPILED / MAIN OPEN30.
Original ordinary mean_upper tail: crossing rejects before NEW arithmetic;
high<=2 returns exactly out, before any OLD chord or OLD reader access.
The source minorant choice/coefficient/root/residual prechecks are separate.
This file consumes the original ordinary B32 and tent unit-log operations.
No target integral, saved cost, K/C result or query inequality is assumed by
either stored-integer leaf theorem.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryEarlyReturnSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdBelowMuBRoundedSourceOnly
open OriginalThirdP4AOrdinaryBCandidateSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdSixTentOrdinaryMassCeilSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- Exact source tail after original minorant/coefficient/residual prechecks.
The arbitrary wt endpoints are read only by the final strict-chord branch.
No semantic assertion is attached to a rejected None. -/
def originalMeanUpperTail (low high : ℚ) (wtLo wtHi fl fh out : ℤ) : Option ℤ :=
  if low<2 ∧ 2<high then none
  else if high≤2 then some out
  else if low=high then some (max 0 (out-fl))
  else some (meanHigh wtLo wtHi fl fh out)

theorem crossing_rejected (low high : ℚ) (wtLo wtHi fl fh out : ℤ)
    (hcross : low<2 ∧ 2<high) :
    originalMeanUpperTail low high wtLo wtHi fl fh out=none := by
  simp only [originalMeanUpperTail,if_pos hcross]

theorem crossing_no_charge (low high : ℚ) (wtLo wtHi fl fh out charge : ℤ)
    (hcross : low<2 ∧ 2<high) :
    originalMeanUpperTail low high wtLo wtHi fl fh out≠some charge := by
  rw [crossing_rejected low high wtLo wtHi fl fh out hcross]
  simp

theorem high_le_two_returns_out (low high : ℚ) (wtLo wtHi fl fh out : ℤ)
    (hhigh : high≤2) :
    originalMeanUpperTail low high wtLo wtHi fl fh out=some out := by
  have hnotCross : ¬(low<2 ∧ 2<high) := by
    rintro ⟨_,hh⟩
    exact (not_lt_of_ge hhigh) hh
  simp only [originalMeanUpperTail,if_neg hnotCross,if_pos hhigh]

theorem strict_chord_tail (low high : ℚ) (wtLo wtHi fl fh out : ℤ)
    (hlow : 2≤low) (hspan : low<high) :
    originalMeanUpperTail low high wtLo wtHi fl fh out=
      some (meanHigh wtLo wtHi fl fh out) := by
  have hnotCross : ¬(low<2 ∧ 2<high) := by
    rintro ⟨hl,_⟩
    exact (not_lt_of_ge hlow) hl
  have hnotHigh : ¬high≤2 := not_le_of_gt (hlow.trans_lt hspan)
  simp only [originalMeanUpperTail,if_neg hnotCross,if_neg hnotHigh,
    if_neg (ne_of_lt hspan)]

/-- Exhaustive source dispatch for the genuine positive-width OLD span.
high=2 belongs to early return; low=2 with high>2 belongs to strict chord. -/
theorem ordinary_old_span_dispatch_exhaustive (low high : ℚ) (hspan : low<high) :
    high≤2 ∨ (low<2 ∧ 2<high) ∨ (2≤low ∧ low<high) := by
  by_cases hh : high≤2
  · exact Or.inl hh
  · by_cases hl : low<2
    · exact Or.inr (Or.inl ⟨hl,lt_of_not_ge hh⟩)
    · exact Or.inr (Or.inr ⟨le_of_not_gt hl,hspan⟩)

theorem originalMeanUpperTail_none_iff (low high : ℚ) (wtLo wtHi fl fh out : ℤ) :
    originalMeanUpperTail low high wtLo wtHi fl fh out=none ↔ low<2 ∧ 2<high := by
  by_cases hc : low<2 ∧ 2<high
  · exact ⟨fun _ => hc,fun _ => crossing_rejected low high wtLo wtHi fl fh out hc⟩
  · rw [originalMeanUpperTail,if_neg hc]
    split_ifs <;> simp [hc]

/-- The actual globally bounded factor is integrable for any measurable
argument under the true ordinary-box probability measure. This includes
the discontinuous actual cap argument, without a continuity assumption. -/
theorem ordinary_factor_integrable (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (g : BoxPoint → ℝ) (hg : Measurable g) :
    Integrable (fun t => actualExtendedThirdLowerFactor (g t)) (boxProbability a b) := by
  let : IsProbabilityMeasure (boxProbability a b) :=
    boxProbability_isProbability a b ha hab
  apply Integrable.of_bound
    (measurable_actualExtendedThirdLowerFactor.comp hg).aestronglyMeasurable
    (1/(2*Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun t => by
    change ‖actualExtendedThirdLowerFactor (g t)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (actualExtendedThirdLowerFactor_nonneg (g t))]
    exact actualExtendedThirdLowerFactor_le_normalization (g t))

private theorem measurable_actual_old_argument : Measurable actualOldArgument := by
  have hx : Measurable (fun t : BoxPoint => t 0) := (continuous_apply 0).measurable
  have hy : Measurable (fun t : BoxPoint => t 1) := (continuous_apply 1).measurable
  have hz : Measurable (fun t : BoxPoint => t 2) := (continuous_apply 2).measurable
  exact ((((measurable_actualExtendedThirdBufferedCap 0).sub hx).sub hy).sub hz).div hz

/-- True NEW-only ordinary full-leaf bound. The actual OLD subtraction is
discarded using its proved nonnegativity. This is not a hypothesized leaf
bound and does not identify the OLD minorant with the actual cap. -/
theorem ordinary_new_only_leaf_upper (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hrho : b 0≤thirdPrefixRho)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (out : ℝ)
    (hout : actualExtendedThirdLowerFactor
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)≤out) :
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤4*boxMass a b*out := by
  have hnew : Integrable (fun t : BoxPoint => actualExtendedThirdLowerFactor
      (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)) (boxProbability a b) := by
    apply ordinary_factor_integrable a b ha hab
    unfold affineArgument
    fun_prop
  have hold := ordinary_factor_integrable a b ha hab actualOldArgument
    measurable_actual_old_argument
  have hdiff :
      (∫ t, actualExtendedThirdLowerFactor
          (affineArgument thirdPrefixTheta (-1) (-1) (-1) t)-
        actualExtendedThirdLowerFactor (actualOldArgument t) ∂boxProbability a b)≤out := by
    rw [integral_sub hnew hold]
    exact (sub_le_self _ (integral_nonneg (fun t =>
      actualExtendedThirdLowerFactor_nonneg (actualOldArgument t)))).trans
      ((ordinary_full_box_new_Jensen a b ha hab hfull).trans hout)
  have hs := ordinary_full_box_subset_compact a b ha hcut hyx hzy hrho hfull
  rw [inter_eq_right.mpr hs,integral_compactKernel_eq_box_mean a b ha hab]
  exact mul_le_mul_of_nonneg_left hdiff
    (mul_nonneg (by norm_num) (boxMass_pos a b ha hab).le)

/-- At the early-return threshold the B minorant's OLD factor is zero
throughout the box. The actual OLD factor is only required to be >=0. -/
theorem B_old_factor_zero_of_high_le_two (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hyx : b 1≤a 0) (hmu : b 0≤VariableEnvelope.mu)
    (hhigh : bOldHigh a≤2) {t : BoxPoint} (ht : t∈Icc a b) :
    actualExtendedThirdLowerFactor (bOldArgument t)=0 := by
  exact actualExtendedThirdLowerFactor_of_le_two
    ((below_mu_B_old_range a b ha hab hyx hmu ht).2.trans hhigh)

theorem tent_old_factor_zero_of_high_le_two (s : TentSum) (k : TentSide)
    (a b : BoxPoint) (ha : ∀ i, 0<a i)
    (hres : 0<OriginalThirdSixTentCandidatesSourceOnly.oldNumerator s k b)
    (hhigh : tentOldHigh s k a≤2) {t : BoxPoint} (ht : t∈Icc a b) :
    actualExtendedThirdLowerFactor (tentOldArgument s k t)=0 := by
  exact actualExtendedThirdLowerFactor_of_le_two
    ((original_tent_old_range s k a b ha hres ht).2.trans hhigh)

/-- ONLY the original NEW read occurs before the high<=2 early return. -/
theorem B_new_stored_query_encloses (table : CheckedBlockTable) (a b : Fin 3 → ℚ) :
    actualExtendedThirdLowerFactor
      (newQuery (realBox a) (realBox b)
        (originalLn32 (realBox b 0/realBox a 0))
        (originalLn32 (realBox b 1/realBox a 1)):ℝ)≤value (bStoredOut table a b) := by
  have hout := (CheckedBlockTable.query_encloses_all table
    (roundedNew (realBox a) (realBox b)
      (originalLn32 (realBox b 0/realBox a 0))
      (originalLn32 (realBox b 1/realBox a 1))).hi P160 P160_pos).2
  simpa only [bStoredOut,newQuery,Rat.cast_div,Rat.cast_intCast,value,
    P160,Int.cast_pow,Int.cast_ofNat] using hout

/-- Full original-grid B early charge. All raw log guards, NEW arithmetic,
same-reader query, full original mass.hi and final UP are supplied. No OLD
query is used. high<=2 binds the exact original early-return branch. -/
theorem ordinary_B_high_le_two_integer_upper
    (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/((48000*2^24:ℤ):ℚ))
    (hbBind : ∀ i, b i=(hi i:ℚ)/((48000*2^24:ℤ):ℚ))
    (ha : ∀ i, 0<realBox a i) (hab : ∀ i, realBox a i<realBox b i)
    (hcut : (1:ℝ)/100≤realBox a 2)
    (hyx : realBox b 1≤realBox a 0) (hzy : realBox b 2≤realBox a 1)
    (hmu : realBox b 0≤VariableEnvelope.mu)
    (hfull : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta)
    (hhigh : bHighQ a≤2) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (OriginalThirdBelowMuBMassCeilSourceOnly.literalOrdinaryUpper lo hi
        (bStoredOut table a b)) := by
  have hr := below_mu_B_log_ratios (realBox a) (realBox b) ha hab hcut hyx hzy hmu
  have hg := original_stored_ordinary_log32_guards lo hi a b haBind hbBind
    ha hab hyx (by simpa only [VariableEnvelope.mu] using hmu) hr.1.2 hr.2.2
  have hn := roundedNew_encloses (a := realBox a) (b := realBox b)
    (originalLn32_sound hr.1.1 hr.1.2)
    (originalLn32_sound hr.2.1 hr.2.2) hg.1 hg.2
  have hmean :
      (thirdPrefixTheta-boxEX (realBox a) (realBox b)-boxEY (realBox a) (realBox b))*
        boxEZInv (realBox a) (realBox b)-1≤
      (newQuery (realBox a) (realBox b)
        (originalLn32 (realBox b 0/realBox a 0))
        (originalLn32 (realBox b 1/realBox a 1)):ℝ) := by
    simpa only [newQuery,Rat.cast_div,Rat.cast_intCast,value] using hn.2
  have hquery := B_new_stored_query_encloses table a b
  have hout := actual_new_mean_upper_of_query (realBox a) (realBox b) _ _ hmean hquery
  have hrho : realBox b 0≤thirdPrefixRho := hmu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hleaf := ordinary_new_only_leaf_upper (realBox a) (realBox b) ha hab
    hcut hyx hzy hrho hfull (value (bStoredOut table a b)) hout
  have haReal (i : Fin 3) : realBox a i=(lo i:ℝ)/((48000*2^24:ℤ):ℝ) := by
    dsimp only [realBox]
    rw [haBind i]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hbReal (i : Fin 3) : realBox b i=(hi i:ℝ)/((48000*2^24:ℤ):ℝ) := by
    dsimp only [realBox]
    rw [hbBind i]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hmass := (OriginalThirdBelowMuBMassCeilSourceOnly.literal_ordinary_mass_encloses
    lo hi (realBox a) (realBox b) haReal hbReal ha hab hcut hyx hzy hmu).2
  have hout0 : 0≤value (bStoredOut table a b) :=
    (actualExtendedThirdLowerFactor_nonneg _).trans hquery
  have hdispatch := high_le_two_returns_out (bLowQ b) (bHighQ a)
    0 0 0 0 (bStoredOut table a b) hhigh
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (bStoredOut table a b) := hleaf
    _≤value (OriginalThirdBelowMuBMassCeilSourceOnly.literalOrdinaryMass lo hi).hi*
        value (bStoredOut table a b) := mul_le_mul_of_nonneg_right hmass hout0
    _=value (bStoredOut table a b)*
        value (OriginalThirdBelowMuBMassCeilSourceOnly.literalOrdinaryMass lo hi).hi := by ring
    _≤value (OriginalThirdBelowMuBMassCeilSourceOnly.literalOrdinaryUpper lo hi
        (bStoredOut table a b)) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

def tentEarlyOut (table : CheckedBlockTable) (a b : BoxPoint) : ℤ :=
  readQueryHi160 (assembledRead table.blocks) (ordinaryNew a b).hi P160

theorem tent_new_stored_query_encloses (table : CheckedBlockTable) (a b : BoxPoint) :
    actualExtendedThirdLowerFactor (ordinaryNewQuery a b:ℝ)≤value (tentEarlyOut table a b) := by
  have h := (CheckedBlockTable.query_encloses_all table (ordinaryNew a b).hi P160 P160_pos).2
  simpa only [tentEarlyOut,ordinaryNewQuery,Rat.cast_div,Rat.cast_intCast,value,
    P160,Int.cast_pow,Int.cast_ofNat] using h

/-- The unit-log ordinary tent NEW charge, independent of the selected
plane's OLD chord. A selector that reaches high<=2 returns this exact out.
This mathematical bound needs no OLD query or OLD range assumption. -/
theorem ordinary_tent_new_only_integer_upper
    (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (D : ℤ) (a b : BoxPoint)
    (hD : D=48000*2^24)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2)
    (hpositive : ∀ i : Fin 2, 0<(originalLnUnit (b i.castSucc/a i.castSucc)).lo) :
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤
      value (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryUpper lo hi
        (tentEarlyOut table a b)) := by
  have hn := (ordinary_tent_means_enclose .x .rise a b ha hab hratio hpositive).1
  have hmean : (thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1≤
      (ordinaryNewQuery a b:ℝ) := by
    simpa only [ordinaryNewQuery,Rat.cast_div,Rat.cast_intCast,value] using hn.2
  have hquery := tent_new_stored_query_encloses table a b
  have hout := actual_new_mean_upper_of_query a b _ _ hmean hquery
  have hrho : b 0≤thirdPrefixRho := hmu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  have hleaf := ordinary_new_only_leaf_upper a b ha hab hcut hyx hzy hrho hfull
    (value (tentEarlyOut table a b)) hout
  have hmass := (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literal_ordinary_mass_encloses
    lo hi D a b hD haBind hbBind ha hab hratio).2
  have hout0 : 0≤value (tentEarlyOut table a b) :=
    (actualExtendedThirdLowerFactor_nonneg _).trans hquery
  calc
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤
        4*boxMass a b*value (tentEarlyOut table a b) := hleaf
    _≤value (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryMass lo hi).hi*
        value (tentEarlyOut table a b) := mul_le_mul_of_nonneg_right hmass hout0
    _=value (tentEarlyOut table a b)*
        value (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryMass lo hi).hi := by ring
    _≤value (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryUpper lo hi
        (tentEarlyOut table a b)) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

/-- Literal tent early-return binding at the exact raw Fraction endpoints.
The weight and OLD query placeholders are universally quantified, so no OLD
evaluation is needed or smuggled into the producer's early-return charge. -/
theorem ordinary_tent_high_le_two_dispatch
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) (D : ℤ)
    (hhigh : literalTentEndpoint s k lo D≤2)
    (wtLo wtHi fl fh out : ℤ) :
    originalMeanUpperTail (literalTentEndpoint s k hi D)
      (literalTentEndpoint s k lo D) wtLo wtHi fl fh out=some out := by
  exact high_le_two_returns_out _ _ wtLo wtHi fl fh out hhigh

theorem ordinary_B_high_le_two_dispatch
    (a b : Fin 3 → ℚ) (hhigh : bHighQ a≤2) (wtLo wtHi fl fh out : ℤ) :
    originalMeanUpperTail (bLowQ b) (bHighQ a) wtLo wtHi fl fh out=some out := by
  exact high_le_two_returns_out _ _ wtLo wtHi fl fh out hhigh

/-- One combined literal-tent branch contract: the exact source tail returns
the same NEW integer whose ordinary integral/mass/UP bound is proved here. -/
theorem ordinary_tent_high_le_two_integer_upper
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) (D : ℤ) (a b : BoxPoint)
    (hD : D=48000*2^24)
    (haBind : ∀ i, a i=(lo i:ℝ)/(D:ℝ))
    (hbBind : ∀ i, b i=(hi i:ℝ)/(D:ℝ))
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (hratio : ∀ i : Fin 2, b i.castSucc/a i.castSucc≤2)
    (hpositive : ∀ i : Fin 2, 0<(originalLnUnit (b i.castSucc/a i.castSucc)).lo)
    (hhigh : literalTentEndpoint s k lo D≤2) :
    originalMeanUpperTail (literalTentEndpoint s k hi D)
      (literalTentEndpoint s k lo D) 0 0 0 0 (tentEarlyOut table a b)=
        some (tentEarlyOut table a b) ∧
    (∫ t in compactRegion ∩ Icc a b,compactKernel t)≤
      value (OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryUpper lo hi
        (tentEarlyOut table a b)) := by
  exact ⟨ordinary_tent_high_le_two_dispatch s k lo hi D hhigh 0 0 0 0 _,
    ordinary_tent_new_only_integer_upper table lo hi D a b hD haBind hbBind
      ha hab hcut hyx hzy hmu hfull hratio hpositive⟩

theorem ordinary_tent_crossing_rejected
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) (D : ℤ)
    (hcross : literalTentEndpoint s k hi D<2 ∧ 2<literalTentEndpoint s k lo D)
    (wtLo wtHi fl fh out : ℤ) :
    originalMeanUpperTail (literalTentEndpoint s k hi D)
      (literalTentEndpoint s k lo D) wtLo wtHi fl fh out=none := by
  exact crossing_rejected _ _ wtLo wtHi fl fh out hcross

theorem ordinary_B_crossing_rejected
    (a b : Fin 3 → ℚ) (hcross : bLowQ b<2 ∧ 2<bHighQ a)
    (wtLo wtHi fl fh out : ℤ) :
    originalMeanUpperTail (bLowQ b) (bHighQ a) wtLo wtHi fl fh out=none := by
  exact crossing_rejected _ _ wtLo wtHi fl fh out hcross

end
end ImbalancedChen.OriginalThirdP4AOrdinaryEarlyReturnSourceOnly
