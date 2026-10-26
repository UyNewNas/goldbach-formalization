import ImbalancedChen.ActualThirdOriginalBelowMuBCandidate
import ImbalancedChen.ActualThirdOriginalPositive256LogRange32

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30.
Original ordinary below-mu B mean_upper arithmetic. Primitive log soundness
and the original positive-divisor guards remain explicit. No mean, weight,
clipped chord or leaf upper bound is a hypothesis. -/
namespace ImbalancedChen.OriginalThirdBelowMuBRoundedSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly

/-- The original positive rational division arm, with no reciprocal interval. -/
def divRat (v : IV) (q : ℚ) : IV :=
  ⟨v.lo*(q.den:ℤ)/q.num,up (v.hi*(q.den:ℤ)) q.num⟩

private theorem scaled_floor_div_le {d : ℤ} (hd : 0<d) (n : ℤ) :
    value (n/d)≤(n:ℝ)/(d:ℝ)/(P160:ℝ) := by
  have hf : ⌊(n:ℝ)/(d:ℝ)⌋=n/d := by
    simpa using Int.floor_div_cast_of_nonneg (k:=ℝ) hd.le (n:ℝ)
  have h := Int.floor_le ((n:ℝ)/(d:ℝ))
  rw [hf] at h
  exact (div_le_div_iff_of_pos_right P160_real_pos).2 h

private theorem le_scaled_up_div {d : ℤ} (hd : 0<d) (n : ℤ) :
    (n:ℝ)/(d:ℝ)/(P160:ℝ)≤value (up n d) := by
  have h := neg_le_neg (scaled_floor_div_le hd (-n))
  simpa only [up, value, Int.cast_neg, neg_div, neg_neg] using h

/-- Reuse of the scalar proof from RoundedOldWeight, isolated from its
symmetric analytic ancestry to avoid redeclaring the shared box ancestors. -/
theorem divRat_sound {v : IV} {x : ℝ} {q : ℚ}
    (hv : Encloses v x) (hq : 0<q) : Encloses (divRat v q) (x/(q:ℝ)) := by
  have hn : 0<q.num := Rat.num_pos.mpr hq
  have hqr : (0:ℝ)<(q:ℝ) := by exact_mod_cast hq
  have alg (z : ℤ) : ((z*(q.den:ℤ):ℤ):ℝ)/(q.num:ℝ)/(P160:ℝ)=value z/(q:ℝ) := by
    simp only [value,Rat.cast_def,Int.cast_mul,Int.cast_natCast,div_eq_mul_inv,
      mul_inv_rev,inv_inv]
    ring
  constructor
  · calc
      value (v.lo*(q.den:ℤ)/q.num) ≤ ((v.lo*(q.den:ℤ):ℤ):ℝ)/(q.num:ℝ)/(P160:ℝ) :=
        scaled_floor_div_le hn _
      _ = value v.lo/(q:ℝ) := alg _
      _ ≤ x/(q:ℝ) := (div_le_div_iff_of_pos_right hqr).2 hv.1
  · calc
      x/(q:ℝ) ≤ value v.hi/(q:ℝ) := (div_le_div_iff_of_pos_right hqr).2 hv.2
      _ = ((v.hi*(q.den:ℤ):ℤ):ℝ)/(q.num:ℝ)/(P160:ℝ) := (alg _).symm
      _ ≤ value (up (v.hi*(q.den:ℤ)) q.num) := le_scaled_up_div hn _

def realBox (a : Fin 3 → ℚ) : BoxPoint := fun i => (a i:ℝ)
def bLowQ (b : Fin 3 → ℚ) : ℚ := (153/256-b 0-b 1)/b 2-11/8
def bHighQ (a : Fin 3 → ℚ) : ℚ := (153/256-a 0-a 1)/a 2-11/8

@[simp] theorem cast_bLowQ (b : Fin 3 → ℚ) :
    (bLowQ b:ℝ)=bOldLow (realBox b) := by
  norm_num [bLowQ,bOldLow,bOldArgument,affineArgument,realBox]
  <;> ring

@[simp] theorem cast_bHighQ (a : Fin 3 → ℚ) :
    (bHighQ a:ℝ)=bOldHigh (realBox a) := by
  norm_num [bHighQ,bOldHigh,bOldArgument,affineArgument,realBox]
  <;> ring

/-- ex and ey are separate original reciprocal-interval divisions. -/
def ex (a b : BoxPoint) (lx : IV) : IV := divide (ofReal (b 0-a 0)) lx
def ey (a b : BoxPoint) (ly : IV) : IV := divide (ofReal (b 1-a 1)) ly

/-- Literal ordinary branch: (-1)*ex invokes ex.__rmul__, hence ex is
on the left of mul. Keep both signed products and both additions. -/
def roundedOld (a b : BoxPoint) (lx ly : IV) : IV :=
  add (mul (add (add (ofReal (153/256)) (mul (ex a b lx) (ofReal (-1))))
    (mul (ey a b ly) (ofReal (-1)))) (ofReal (boxEZInv a b))) (ofReal (-11/8))

def roundedNew (a b : BoxPoint) (lx ly : IV) : IV :=
  sub (mul (sub (sub (ofReal thirdPrefixTheta) (ex a b lx)) (ey a b ly))
    (ofReal (boxEZInv a b))) (ofReal 1)

theorem roundedOld_encloses {a b : BoxPoint} {lx ly : IV}
    (hlx : Encloses lx (Real.log (b 0/a 0)))
    (hly : Encloses ly (Real.log (b 1/a 1)))
    (hpx : 0<lx.lo) (hpy : 0<ly.lo) :
    Encloses (roundedOld a b lx ly) (bOldMean a b) := by
  have hx := divide_sound (ofReal_sound (b 0-a 0)) hlx hpx
  have hy := divide_sound (ofReal_sound (b 1-a 1)) hly hpy
  have h := add_sound (mul_sound
    (add_sound (add_sound (ofReal_sound (153/256))
      (mul_sound hx (ofReal_sound (-1)))) (mul_sound hy (ofReal_sound (-1))))
    (ofReal_sound (boxEZInv a b))) (ofReal_sound (-11/8))
  have heq : (153/256+((b 0-a 0)/Real.log (b 0/a 0))*(-1)+
      ((b 1-a 1)/Real.log (b 1/a 1))*(-1))*boxEZInv a b+(-11/8)=bOldMean a b := by
    unfold bOldMean boxEX boxEY
    ring
  rw [heq] at h
  exact h

theorem roundedNew_encloses {a b : BoxPoint} {lx ly : IV}
    (hlx : Encloses lx (Real.log (b 0/a 0)))
    (hly : Encloses ly (Real.log (b 1/a 1)))
    (hpx : 0<lx.lo) (hpy : 0<ly.lo) :
    Encloses (roundedNew a b lx ly)
      ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1) := by
  exact sub_sound (mul_sound (sub_sound
    (sub_sound (ofReal_sound thirdPrefixTheta)
      (divide_sound (ofReal_sound (b 0-a 0)) hlx hpx))
    (divide_sound (ofReal_sound (b 1-a 1)) hly hpy))
    (ofReal_sound (boxEZInv a b))) (ofReal_sound 1)

/-- Derive the true OLD mean range from the actual B support, integrability,
and exact expectation; no rounded weight enclosure enters this proof. -/
theorem bOldMean_mem_range (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i)
    (hyx : b 1≤a 0) (hmu : b 0≤VariableEnvelope.mu) :
    bOldMean a b∈Icc (bOldLow b) (bOldHigh a) := by
  letI := boxProbability_isProbability a b ha hab
  have hr : ∀ᵐ t ∂boxProbability a b,
      bOldArgument t∈Icc (bOldLow b) (bOldHigh a) := by
    filter_upwards [boxProbability_ae_mem a b] with t ht
    exact below_mu_B_old_range a b ha hab hyx hmu ht
  have hm : Measurable bOldArgument := by
    unfold bOldArgument affineArgument
    fun_prop
  have hi : Integrable bOldArgument (boxProbability a b) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (|bOldLow b|+|bOldHigh a|)
    filter_upwards [hr] with t ht
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (bOldLow b),abs_nonneg (bOldHigh a),ht.1]
    · linarith [le_abs_self (bOldHigh a),abs_nonneg (bOldLow b),ht.2]
  have hl := integral_mono_ae (integrable_const (bOldLow b)) hi (hr.mono (fun _ h=>h.1))
  have hu := integral_mono_ae hi (integrable_const (bOldHigh a)) (hr.mono (fun _ h=>h.2))
  rw [below_mu_B_old_mean a b ha hab] at hl hu
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hl hu
  exact ⟨hl,hu⟩

def trueWeight (a b : BoxPoint) : ℝ :=
  (bOldMean a b-bOldLow b)/(bOldHigh a-bOldLow b)

theorem trueWeight_mem_unit (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i)
    (hyx : b 1≤a 0) (hmu : b 0≤VariableEnvelope.mu) :
    trueWeight a b∈Icc 0 1 := by
  have hr := bOldMean_mem_range a b ha hab hyx hmu
  have hs := sub_pos.mpr (below_mu_B_old_span a b ha hab hyx hmu)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hr.1) hs.le
  · apply (div_le_iff₀ hs).2
    linarith [hr.2]

/-- wt=(old-low)/(high-low), before the original [0,P] clipping. -/
def rawWeight (a b : Fin 3 → ℚ) (lx ly : IV) : IV :=
  divRat (sub (roundedOld (realBox a) (realBox b) lx ly) (ofReal (bLowQ b:ℝ)))
    (bHighQ a-bLowQ b)

theorem rawWeight_encloses (a b : Fin 3 → ℚ) (lx ly : IV)
    (ha : ∀i,0<realBox a i) (hab : ∀i,realBox a i<realBox b i)
    (hyx : realBox b 1≤realBox a 0) (hmu : realBox b 0≤VariableEnvelope.mu)
    (hlx : Encloses lx (Real.log (realBox b 0/realBox a 0)))
    (hly : Encloses ly (Real.log (realBox b 1/realBox a 1)))
    (hpx : 0<lx.lo) (hpy : 0<ly.lo) :
    Encloses (rawWeight a b lx ly) (trueWeight (realBox a) (realBox b)) := by
  have hs := below_mu_B_old_span (realBox a) (realBox b) ha hab hyx hmu
  have hq : (0:ℚ)<bHighQ a-bLowQ b := by
    have hr : (0:ℝ)<((bHighQ a-bLowQ b:ℚ):ℝ) := by
      simpa only [Rat.cast_sub,cast_bHighQ,cast_bLowQ] using sub_pos.mpr hs
    exact_mod_cast hr
  have h := divRat_sound (sub_sound (roundedOld_encloses hlx hly hpx hpy)
    (ofReal_sound (bLowQ b:ℝ))) hq
  simpa only [rawWeight,trueWeight,Rat.cast_sub,cast_bHighQ,cast_bLowQ] using h

/-- Exactly the original sieve.at(new.hi,P) argument. -/
def newQuery (a b : BoxPoint) (lx ly : IV) : ℚ :=
  ((roundedNew a b lx ly).hi:ℚ)/(P160:ℚ)

/-- A complete ordinary B candidate transport. Only primitive log facts,
original division guards, geometry, and the three factor-query inequalities
remain inputs. Both means, the raw weight and clipping are supplied here.
No half-mass factor: this is the original ordinary full box. -/
theorem original_below_mu_B_rounded_candidate
    (a b : Fin 3 → ℚ) (lx ly : IV) (fl fh out : ℤ)
    (ha : ∀i,0<realBox a i) (hab : ∀i,realBox a i<realBox b i)
    (hcut : (1:ℝ)/100≤realBox a 2)
    (hyx : realBox b 1≤realBox a 0) (hzy : realBox b 2≤realBox a 1)
    (hmu : realBox b 0≤VariableEnvelope.mu)
    (hfull : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta)
    (hlx : Encloses lx (Real.log (realBox b 0/realBox a 0)))
    (hly : Encloses ly (Real.log (realBox b 1/realBox a 1)))
    (hpx : 0<lx.lo) (hpy : 0<ly.lo)
    (hlo : 2≤bOldLow (realBox b))
    (hfl : value fl≤actualExtendedThirdLowerFactor (bOldLow (realBox b)))
    (hfh : value fh≤actualExtendedThirdLowerFactor (bOldHigh (realBox a)))
    (hquery : actualExtendedThirdLowerFactor
      (newQuery (realBox a) (realBox b) lx ly:ℝ)≤value out) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      4*boxMass (realBox a) (realBox b)*
        value (meanHigh (rawWeight a b lx ly).lo (rawWeight a b lx ly).hi fl fh out) := by
  have hw := rawWeight_encloses a b lx ly ha hab hyx hmu hlx hly hpx hpy
  have hu := trueWeight_mem_unit (realBox a) (realBox b) ha hab hyx hmu
  have hr := meanHigh_sound (fl:=fl) (fh:=fh) (out:=out) hu.1 hu.2 hw.1 hw.2
  have hc : max 0 (value out-bOldChord (realBox a) (realBox b) (value fl) (value fh))≤
      value (meanHigh (rawWeight a b lx ly).lo (rawWeight a b lx ly).hi fl fh out) := by
    simpa only [bOldChord,trueWeight] using hr
  have hnew : (thirdPrefixTheta-boxEX (realBox a) (realBox b)-
      boxEY (realBox a) (realBox b))*boxEZInv (realBox a) (realBox b)-1≤
      (newQuery (realBox a) (realBox b) lx ly:ℝ) := by
    simpa only [newQuery,Rat.cast_div,Rat.cast_intCast,value] using
      (roundedNew_encloses hlx hly hpx hpy).2
  have hout := actual_new_mean_upper_of_query (realBox a) (realBox b) _ _ hnew hquery
  have hleaf := original_below_mu_B_leaf_candidate (realBox a) (realBox b)
    ha hab hcut hyx hzy hmu hfull (value fl) (value fh) (value out) hlo
    (below_mu_B_old_span (realBox a) (realBox b) ha hab hyx hmu) hfl hfh hout
  have hm : 0≤4*boxMass (realBox a) (realBox b) :=
    mul_nonneg (by norm_num) (boxMass_pos (realBox a) (realBox b) ha hab).le
  exact hleaf.trans (mul_le_mul_of_nonneg_left hc hm)

/-- The original cutoff, ordering and below-mu upper corner place BOTH
ordinary ratios in the original positive ln range-reduction supplier domain. -/
theorem below_mu_B_log_ratios (a b : BoxPoint)
    (ha : ∀i,0<a i) (hab : ∀i,a i<b i) (hcut : (1:ℝ)/100≤a 2)
    (hyx : b 1≤a 0) (hzy : b 2≤a 1) (hmu : b 0≤VariableEnvelope.mu) :
    b 0/a 0∈Icc 1 32 ∧ b 1/a 1∈Icc 1 32 := by
  have ha1 : (1:ℝ)/100≤a 1 := hcut.trans ((hab 2).le.trans hzy)
  have ha0 : (1:ℝ)/100≤a 0 := ha1.trans ((hab 1).le.trans hyx)
  have hb1 : b 1≤VariableEnvelope.mu := hyx.trans ((hab 0).le.trans hmu)
  have hsmall0 : b 0≤32*a 0 := by
    dsimp [VariableEnvelope.mu] at hmu
    linarith
  have hsmall1 : b 1≤32*a 1 := by
    dsimp [VariableEnvelope.mu] at hb1
    linarith
  exact ⟨⟨(le_div_iff₀ (ha 0)).2 (by simpa using (hab 0).le),
    (div_le_iff₀ (ha 0)).2 hsmall0⟩,
    ⟨(le_div_iff₀ (ha 1)).2 (by simpa using (hab 1).le),
    (div_le_iff₀ (ha 1)).2 hsmall1⟩⟩

/-- Literal 256-term, at-most-four-range-reduction ln on both coordinates.
The semantic log premises of rounded_candidate are discharged internally.
The original two integer positivity guards are deliberately still explicit. -/
theorem original_below_mu_B_literal_candidate
    (a b : Fin 3 → ℚ) (fl fh out : ℤ)
    (ha : ∀i,0<realBox a i) (hab : ∀i,realBox a i<realBox b i)
    (hcut : (1:ℝ)/100≤realBox a 2)
    (hyx : realBox b 1≤realBox a 0) (hzy : realBox b 2≤realBox a 1)
    (hmu : realBox b 0≤VariableEnvelope.mu)
    (hfull : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta)
    (hpx : 0<(originalLn32 (realBox b 0/realBox a 0)).lo)
    (hpy : 0<(originalLn32 (realBox b 1/realBox a 1)).lo)
    (hlo : 2≤bOldLow (realBox b))
    (hfl : value fl≤actualExtendedThirdLowerFactor (bOldLow (realBox b)))
    (hfh : value fh≤actualExtendedThirdLowerFactor (bOldHigh (realBox a)))
    (hquery : actualExtendedThirdLowerFactor
      (newQuery (realBox a) (realBox b)
        (originalLn32 (realBox b 0/realBox a 0))
        (originalLn32 (realBox b 1/realBox a 1)):ℝ)≤value out) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      4*boxMass (realBox a) (realBox b)*value (meanHigh
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).lo
        (rawWeight a b (originalLn32 (realBox b 0/realBox a 0))
          (originalLn32 (realBox b 1/realBox a 1))).hi fl fh out) := by
  have hr := below_mu_B_log_ratios (realBox a) (realBox b) ha hab hcut hyx hzy hmu
  exact original_below_mu_B_rounded_candidate a b _ _ fl fh out
    ha hab hcut hyx hzy hmu hfull (originalLn32_sound hr.1.1 hr.1.2)
    (originalLn32_sound hr.2.1 hr.2.2) hpx hpy hlo hfl hfh hquery

end
end ImbalancedChen.OriginalThirdBelowMuBRoundedSourceOnly
