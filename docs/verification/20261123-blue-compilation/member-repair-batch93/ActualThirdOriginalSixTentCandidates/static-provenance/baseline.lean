import ImbalancedChen.ActualThirdOriginalOrdinaryOldChord

/-!
SOURCEONLY / HOLD_ELABORATION / MAIN OPEN30.
One common supplier for the original six A(S)/C(S) affine tent candidates.
Append once to the exact ordinary OLD chord parent. No new import is needed.
-/
namespace ImbalancedChen.OriginalThirdSixTentCandidatesSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdOldChordMeanSourceOnly
open OriginalThirdCompactPartitionSourceOnly

/-- Exactly the six coefficient triples enumerated by original minorant(). -/
inductive TentSum where
  | x | y | xy | xz | yz | xyz

inductive TentSide where
  | rise | fall

def sumX : TentSum → ℝ
  | .x => 1 | .y => 0 | .xy => 1 | .xz => 1 | .yz => 0 | .xyz => 1

def sumY : TentSum → ℝ
  | .x => 0 | .y => 1 | .xy => 1 | .xz => 0 | .yz => 1 | .xyz => 1

def sumZ : TentSum → ℝ
  | .x => 0 | .y => 0 | .xy => 0 | .xz => 1 | .yz => 1 | .xyz => 1

def tentSum (s : TentSum) (t : BoxPoint) : ℝ :=
  sumX s*t 0+sumY s*t 1+sumZ s*t 2

def planeConst : TentSide → ℝ
  | .rise => 1/2 | .fall => 57/64

def planeSlope : TentSide → ℝ
  | .rise => 1/2 | .fall => -3/2

def tentPlane (s : TentSum) (k : TentSide) (t : BoxPoint) : ℝ :=
  planeConst k+planeSlope k*tentSum s t

/-- The physical-coordinate version of the original cross-multiplied p-q.
The original integer plane_range value is D times this normalized value. -/
def sourceDelta (s : TentSum) (t : BoxPoint) : ℝ :=
  tentPlane s .rise t-tentPlane s .fall t

/-- Keep the original if/elif priority: the descending branch requires the
ascending test to have failed, as well as the nonnegative lower delta. -/
def sourceActive (s : TentSum) (k : TentSide) (a b : BoxPoint) : Prop :=
  match k with
  | .rise => sourceDelta s b≤0
  | .fall => ¬sourceDelta s b≤0 ∧ 0≤sourceDelta s a

/-- Exact source plane_range upper: A is increasing, C is decreasing. -/
def planeUpper (s : TentSum) (k : TentSide) (a b : BoxPoint) : ℝ :=
  match k with
  | .rise => tentPlane s .rise b
  | .fall => tentPlane s .fall a

def oldX (s : TentSum) (k : TentSide) : ℝ := planeSlope k*sumX s-1
def oldY (s : TentSum) (k : TentSide) : ℝ := planeSlope k*sumY s-1
def oldZ (s : TentSum) (k : TentSide) : ℝ := planeSlope k*sumZ s-1

def oldNumerator (s : TentSum) (k : TentSide) (t : BoxPoint) : ℝ :=
  planeConst k+oldX s k*t 0+oldY s k*t 1

def tentOldArgument (s : TentSum) (k : TentSide) (t : BoxPoint) : ℝ :=
  affineArgument (planeConst k) (oldX s k) (oldY s k) (oldZ s k) t

def tentOldLow (s : TentSum) (k : TentSide) (b : BoxPoint) : ℝ :=
  tentOldArgument s k b

def tentOldHigh (s : TentSum) (k : TentSide) (a : BoxPoint) : ℝ :=
  tentOldArgument s k a

def tentOldMean (s : TentSum) (k : TentSide) (a b : BoxPoint) : ℝ :=
  (planeConst k+oldX s k*boxEX a b+oldY s k*boxEY a b)*boxEZInv a b+oldZ s k

def tentOldChord (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (flo fhi : ℝ) : ℝ :=
  flo+(tentOldMean s k a b-tentOldLow s k b)/
    (tentOldHigh s k a-tentOldLow s k b)*(fhi-flo)

theorem tentSum_mono (s : TentSum) {t u : BoxPoint} (htu : t≤u) :
    tentSum s t≤tentSum s u := by
  cases s <;> simp only [tentSum,sumX,sumY,sumZ,one_mul,zero_mul,zero_add,add_zero]
    <;> linarith [htu 0,htu 1,htu 2]

/-- This identity pays the source branch test, rather than assuming that the
selected plane equals the tent. The middle branch of v was already removed. -/
theorem sourceDelta_eq (s : TentSum) (t : BoxPoint) :
    sourceDelta s t=2*(tentSum s t-VariableEnvelope.mu) := by
  unfold sourceDelta tentPlane planeConst planeSlope VariableEnvelope.mu
  ring

theorem sourceDelta_range (s : TentSum) (a b : BoxPoint)
    {t : BoxPoint} (ht : t∈Icc a b) :
    sourceDelta s t∈Icc (sourceDelta s a) (sourceDelta s b) := by
  rw [sourceDelta_eq,sourceDelta_eq,sourceDelta_eq]
  constructor <;> nlinarith [tentSum_mono s ht.1,tentSum_mono s ht.2]

theorem active_plane_eq_v (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (hactive : sourceActive s k a b) {t : BoxPoint} (ht : t∈Icc a b) :
    tentPlane s k t=VariableEnvelope.v (tentSum s t) := by
  cases k with
  | rise =>
      change sourceDelta s b≤0 at hactive
      rw [sourceDelta_eq] at hactive
      have hsmu : tentSum s t≤VariableEnvelope.mu := by
        linarith [tentSum_mono s ht.2]
      rw [VariableEnvelope.v_eq_A hsmu]
      unfold tentPlane planeConst planeSlope VariableEnvelope.A
      ring
  | fall =>
      change ¬sourceDelta s b≤0 ∧ 0≤sourceDelta s a at hactive
      have hd := hactive.2
      rw [sourceDelta_eq] at hd
      have hsmu : VariableEnvelope.mu≤tentSum s t := by
        linarith [tentSum_mono s ht.1]
      rw [VariableEnvelope.v_eq_C hsmu]
      unfold tentPlane planeConst planeSlope VariableEnvelope.C
      ring

/-- All six enumerated sums are legitimate on the actual ordered domain.
The extra listed y branch is absorbed by v(y)<=v(x) below mu. Pair gates
are supplied through the existing actual six-envelope identity. -/
theorem tent_v_le_six (s : TentSum) {t : BoxPoint}
    (hordered : VariableEnvelope.Ordered (t 0) (t 1) (t 2)) :
    VariableEnvelope.v (tentSum s t)≤VariableEnvelope.six (t 0) (t 1) (t 2) := by
  cases s with
  | x =>
      simpa only [tentSum,sumX,sumY,sumZ,one_mul,zero_mul,add_zero] using
        VariableEnvelope.v_le_six (t 0) (t 1) (t 2)
  | y =>
      have hymu : t 1≤VariableEnvelope.mu := hordered.2.2.1.trans hordered.2.2.2
      have hyx : VariableEnvelope.v (t 1)≤VariableEnvelope.v (t 0) := by
        rw [VariableEnvelope.v_eq_A hymu,VariableEnvelope.v_eq_A hordered.2.2.2]
        unfold VariableEnvelope.A
        linarith [hordered.2.2.1]
      simpa only [tentSum,sumX,sumY,sumZ,one_mul,zero_mul,zero_add,add_zero] using
        hyx.trans (VariableEnvelope.v_le_six (t 0) (t 1) (t 2))
  | xy =>
      simp only [tentSum,sumX,sumY,sumZ,one_mul,zero_mul,add_zero,VariableEnvelope.six]
      exact le_max_of_le_right (le_max_left _ _)
  | xz =>
      simp only [tentSum,sumX,sumY,sumZ,one_mul,zero_mul,add_zero,VariableEnvelope.six]
      exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _))))
  | yz =>
      simp only [tentSum,sumX,sumY,sumZ,one_mul,zero_mul,zero_add,VariableEnvelope.six]
      exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_right _ _))))
  | xyz =>
      simp only [tentSum,sumX,sumY,sumZ,one_mul,VariableEnvelope.six]
      exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

theorem tent_plane_le_upper (s : TentSum) (k : TentSide) (a b : BoxPoint)
    {t : BoxPoint} (ht : t∈Icc a b) :
    tentPlane s k t≤planeUpper s k a b := by
  have hlow := tentSum_mono s ht.1
  have hhigh := tentSum_mono s ht.2
  cases k <;> dsimp [planeUpper,tentPlane,planeConst,planeSlope] <;> linarith

/-- Original whole-box active test plus the original upper<=Theta filter
implies a minorant of the ACTUAL gated buffered cap. Neither the desired
minorant nor a universal pointwise plane/tent comparison is an input. -/
theorem original_tent_plane_le_actual_cap
    (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hactive : sourceActive s k a b)
    (hroot : planeUpper s k a b≤thirdPrefixTheta)
    {t : BoxPoint} (ht : t∈Icc a b) :
    tentPlane s k t≤actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
  have hordered : VariableEnvelope.Ordered (t 0) (t 1) (t 2) :=
    ⟨((ha 2).trans_le (ht.1 2)).le,
      (ht.2 2).trans (hzy.trans (ht.1 1)),
      (ht.2 1).trans (hyx.trans (ht.1 0)),(ht.2 0).trans hmu⟩
  unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  simp only [mul_zero,sub_zero]
  apply le_min
  · exact (tent_plane_le_upper s k a b ht).trans hroot
  · rw [actualExtendedThirdEnvelope_eq_six hordered,active_plane_eq_v s k a b hactive ht]
    exact tent_v_le_six s hordered

theorem old_xy_coefficients_neg (s : TentSum) (k : TentSide) :
    oldX s k<0 ∧ oldY s k<0 := by
  cases s <;> cases k <;> norm_num [oldX,oldY,planeSlope,sumX,sumY]

theorem tent_old_argument_identity (s : TentSum) (k : TentSide)
    (t : BoxPoint) (hz : t 2≠0) :
    tentOldArgument s k t=(tentPlane s k t-t 0-t 1-t 2)/t 2 := by
  unfold tentOldArgument affineArgument tentPlane tentSum oldX oldY oldZ
  field_simp [hz]
  <;> ring

/-- Original low_num>0 is retained explicitly as the producer's residual
gate. The negative x,y coefficients and positive z denominators then prove
the actual OLD support range, uniformly for all twelve affine branches. -/
theorem original_tent_old_range (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hres : 0<oldNumerator s k b)
    {t : BoxPoint} (ht : t∈Icc a b) :
    tentOldArgument s k t∈Icc (tentOldLow s k b) (tentOldHigh s k a) := by
  have hn := old_xy_coefficients_neg s k
  have hxl := mul_le_mul_of_nonpos_left (ht.2 0) hn.1.le
  have hyl := mul_le_mul_of_nonpos_left (ht.2 1) hn.2.le
  have hxh := mul_le_mul_of_nonpos_left (ht.1 0) hn.1.le
  have hyh := mul_le_mul_of_nonpos_left (ht.1 1) hn.2.le
  have hlow : oldNumerator s k b≤oldNumerator s k t := by
    unfold oldNumerator
    linarith
  have hhigh : oldNumerator s k t≤oldNumerator s k a := by
    unfold oldNumerator
    linarith
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hl := div_le_div₀ (hres.le.trans hlow) hlow hz (ht.2 2)
  have hh := div_le_div₀ ((hres.le.trans hlow).trans hhigh) hhigh (ha 2) (ht.1 2)
  constructor
  · simpa only [tentOldLow,tentOldArgument,affineArgument,oldNumerator] using
      add_le_add_right hl (oldZ s k)
  · simpa only [tentOldHigh,tentOldArgument,affineArgument,oldNumerator] using
      add_le_add_right hh (oldZ s k)

theorem original_tent_old_span (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) (hres : 0<oldNumerator s k b) :
    tentOldLow s k b<tentOldHigh s k a := by
  have hn := old_xy_coefficients_neg s k
  have hx := mul_lt_mul_of_neg_left (hab 0) hn.1
  have hy := mul_lt_mul_of_neg_left (hab 1) hn.2
  have hnumlt : oldNumerator s k b<oldNumerator s k a := by
    unfold oldNumerator
    linarith
  have hb2 : 0<b 2 := (ha 2).trans (hab 2)
  have hfirst := (div_lt_div_iff_of_pos_right hb2).2 hnumlt
  have hsecond := div_le_div₀ (hres.trans hnumlt).le
    (le_refl (oldNumerator s k a)) (ha 2) (hab 2).le
  simpa only [tentOldLow,tentOldHigh,tentOldArgument,affineArgument,oldNumerator] using
    add_lt_add_right (hfirst.trans_le hsecond) (oldZ s k)

theorem original_tent_old_minorant
    (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hactive : sourceActive s k a b) (hroot : planeUpper s k a b≤thirdPrefixTheta)
    {t : BoxPoint} (ht : t∈Icc a b) :
    tentOldArgument s k t≤actualOldArgument t := by
  have hz : 0<t 2 := (ha 2).trans_le (ht.1 2)
  have hc := original_tent_plane_le_actual_cap s k a b ha hyx hzy hmu hactive hroot ht
  rw [tent_old_argument_identity s k t hz.ne']
  unfold actualOldArgument
  exact (div_le_div_iff_of_pos_right hz).2 (by linarith)

/-- Exact ordinary affine OLD mean under the original reciprocal law. -/
theorem original_tent_old_mean (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i) :
    (∫ t, tentOldArgument s k t ∂boxProbability a b)=tentOldMean s k a b := by
  exact boxProbability_affine_mean a b ha hab (planeConst k)
    (oldX s k) (oldY s k) (oldZ s k)

/-- The two real endpoint query estimates give an actual lower bound for the
OLD factor integral. Whole-box minorant and support range are derived here. -/
theorem original_tent_chord_le_actual_integral
    (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hyx : b 1≤a 0) (hzy : b 2≤a 1) (hmu : b 0≤VariableEnvelope.mu)
    (hactive : sourceActive s k a b) (hroot : planeUpper s k a b≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k b) (hlo : 2≤tentOldLow s k b)
    (flo fhi : ℝ)
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k b))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k a)) :
    tentOldChord s k a b flo fhi≤
      ∫ t, actualExtendedThirdLowerFactor (actualOldArgument t) ∂boxProbability a b := by
  exact old_query_chord_le_integral_actual a b ha hab (planeConst k)
    (oldX s k) (oldY s k) (oldZ s k) (tentOldLow s k b) (tentOldHigh s k a) flo fhi
    hlo (original_tent_old_span s k a b ha hab hres)
    (fun t ht => original_tent_old_range s k a b ha hres ht)
    (fun t ht => original_tent_old_minorant s k a b ha hyx hzy hmu hactive hroot ht)
    hfl hfh

/-- Actual ordinary full-leaf mean_upper analytic bound for any original
eligible selected tent plane. No desired NEW mean bound, cap minorant,
OLD range/mean bound, or target integral inequality is an input. Stored
rounding and the selected-plane record remain distinct data obligations. -/
theorem original_tent_leaf_exact_candidate
    (s : TentSum) (k : TentSide) (a b : BoxPoint)
    (ha : ∀ i, 0<a i) (hab : ∀ i, a i<b i)
    (hcut : (1:ℝ)/100≤a 2) (hyx : b 1≤a 0) (hzy : b 2≤a 1)
    (hmu : b 0≤VariableEnvelope.mu)
    (hfull : b 0+b 1+3*b 2≤thirdPrefixTheta)
    (hactive : sourceActive s k a b) (hroot : planeUpper s k a b≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k b) (hlo : 2≤tentOldLow s k b)
    (flo fhi : ℝ)
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k b))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k a)) :
    (∫ t in compactRegion ∩ Icc a b, compactKernel t)≤
      4*boxMass a b*max 0
        (actualExtendedThirdLowerFactor
          ((thirdPrefixTheta-boxEX a b-boxEY a b)*boxEZInv a b-1)-
        tentOldChord s k a b flo fhi) := by
  have hrho : b 0≤thirdPrefixRho := hmu.trans (by
    norm_num [VariableEnvelope.mu,thirdPrefixRho])
  exact ordinary_full_leaf_old_chord_upper a b ha hab hcut hyx hzy hrho hfull
    (planeConst k) (oldX s k) (oldY s k) (oldZ s k)
    (tentOldLow s k b) (tentOldHigh s k a) flo fhi _ hlo
    (original_tent_old_span s k a b ha hab hres)
    (fun t ht => original_tent_old_range s k a b ha hres ht)
    (fun t ht => original_tent_old_minorant s k a b ha hyx hzy hmu hactive hroot ht)
    hfl hfh le_rfl

end
end ImbalancedChen.OriginalThirdSixTentCandidatesSourceOnly
