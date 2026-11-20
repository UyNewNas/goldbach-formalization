import ImbalancedChen.P4BOriginalPairMeanGeometry

/-! SOURCE ONLY / UNCOMPILED. Fixed profile prices and the numerical
E3 power reserves. No mean/discrepancy estimate is assumed here. -/
namespace ImbalancedChen.P4BOriginalE3LogPrices
noncomputable section
open Classical Filter
open scoped BigOperators SchwartzMap
open P4BOriginalPositiveLongEnvelope
open P4BOriginalEnvelopePolynomialPayment (p2Price p2Price_nonneg)
open P4BOriginalPairMeanNorm (densityLog densityLog_one_le)
open P4BOriginalRoughE3Assembly (polyMoment reciprocalMoment)
open Part3.TwoLongTransitionMellinN2
open Part3.TwoLongQuantitativeTransitionProfiles
open Part3.TwoLongHBMellinBrunProfiles (pairCost pairCost_nonneg)
open Part3.TwoLongNaturalInternalP2 (internalP2Constant internalP2Constant_pos)
open Part3.TwoLongInternalP2Modes (N2_nonneg)
open Part3.TwoLongMellinLogBudget
open Part3.TwoLongActualLowerCorePayment (moment_log_budget)
open P4BOriginalTwoLongActualScales (brunEpsilon)
open P4BOriginalHighRankLocalLevel (theta)

theorem envelopeCost_le : envelopeCost≤3*profileConstant := by
  have hD := D_nonneg
  have hB := B_nonneg 1
  unfold envelopeCost upperCost gapCost profileConstant firstCost secondCost
  linarith

theorem primary_price (fGap fLog gGap gLog : Bool) {delta U V H t1 t2 : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hH : 0≤H) (h1 : |t1|≤H) (h2 : |t2|≤H) :
    p2Price (profileSchwartz fGap fLog hd hs U t1) (profileSchwartz gGap gLog hd hs V t2)≤pairCost delta U V H := by
  have hF := profile_N2_cube fGap fLog hd hs hH h1 U
  have hG := profile_N2_cube gGap gLog hd hs hH h2 V
  have hC := internalP2Constant_pos.le
  have hP := costs_nonneg.2.2
  have hU := zero_le_one.trans (logSize_one_le U)
  have hV := zero_le_one.trans (logSize_one_le V)
  have hnF := N2_nonneg (profileSchwartz fGap fLog hd hs U t1 : ℝ→ℂ)
  have hnG := N2_nonneg (profileSchwartz gGap gLog hd hs V t2 : ℝ→ℂ)
  unfold p2Price
  calc
    _≤internalP2Constant*(profileConstant*logSize U*(1+H)^2/delta^2)*
        (profileConstant*logSize V*(1+H)^2/delta^2) := by gcongr
    _=pairCost delta U V H := by unfold pairCost; field_simp [hd.ne']; ring

theorem envelope_price_pair {delta U V H : ℝ} (hd : 0<delta) (hs : delta≤1/4) (hH : 0≤H) :
    p2Price (envelopeSchwartz hd hs U) (envelopeSchwartz hd hs V)≤9*pairCost delta U V H := by
  have hU := zero_le_one.trans (logSize_one_le U)
  have hV := zero_le_one.trans (logSize_one_le V)
  have hC := internalP2Constant_pos.le
  have hP := costs_nonneg.2.2
  have he := envelopeCost_nonneg
  have hnF := N2_nonneg (envelopeSchwartz hd hs U : ℝ→ℂ)
  have hnG := N2_nonneg (envelopeSchwartz hd hs V : ℝ→ℂ)
  have hfreq : 1≤(1+H)^4 := one_le_pow₀ (by linarith)
  have hcost : envelopeCost^2≤9*profileConstant^2 := by
    have h := mul_self_le_mul_self he envelopeCost_le
    nlinarith
  calc
    _≤internalP2Constant*(envelopeCost*logSize U/delta^2)*(envelopeCost*logSize V/delta^2) := by
      unfold p2Price
      gcongr <;> exact envelope_N2 hd hs _
    _=internalP2Constant*envelopeCost^2*logSize U*logSize V/delta^4 := by field_simp [hd.ne']; ring
    _≤internalP2Constant*(9*profileConstant^2)*logSize U*logSize V*(1+H)^4/delta^4 := by gcongr
    _=9*pairCost delta U V H := by unfold pairCost; ring

def meanLogConstant : ℝ := meanConstant^2*(4+|Real.log (4:ℝ)|)^2

theorem meanLogConstant_nonneg : 0≤meanLogConstant := by unfold meanLogConstant; positivity

theorem meanPrice_log (B : ℕ) {x U V : ℝ} (hx0 : 0<x) (hlog : 1≤Real.log x)
    (hU : 1≤U) (hV : 1≤V) (hUx : U≤4*x) (hVx : V≤4*x) :
    meanPrice ((Real.log x)^B)⁻¹ U*meanPrice ((Real.log x)^B)⁻¹ V≤
      meanLogConstant*(Real.log x)^(2+4*B) := by
  have h1 := logSize_le_scaled (by norm_num : (0:ℝ)<4) hx0 hlog hU hUx
  have h2 := logSize_le_scaled (by norm_num : (0:ℝ)<4) hx0 hlog hV hVx
  have hU0 := zero_le_one.trans (logSize_one_le U)
  have hV0 := zero_le_one.trans (logSize_one_le V)
  have hc : 0≤meanConstant := by
    have hD := envelopeCost_nonneg
    have hF := Part3.TwoLongN2FourierDecay.fourierDecayConstant_pos.le
    unfold meanConstant
    positivity
  unfold meanPrice
  calc
    _≤(meanConstant*((4+|Real.log (4:ℝ)|)*Real.log x)/(((Real.log x)^B)⁻¹)^2)*
        (meanConstant*((4+|Real.log (4:ℝ)|)*Real.log x)/(((Real.log x)^B)⁻¹)^2) := by gcongr
    _=_ := by
      unfold meanLogConstant
      simp only [inv_pow,div_inv_eq_mul,pow_add,pow_mul,mul_pow]
      ring

theorem reciprocalMoment_log {D : ℕ} {x : ℝ} (hD : 1≤D) (hlog : 1≤Real.log x) (hDx : (D:ℝ)≤x) :
    reciprocalMoment D≤8^16*(Real.log x)^16 := by
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD
  have H := Real.log_le_log (zero_lt_one.trans_le hD1) hDx
  unfold reciprocalMoment
  rw [max_eq_right hD1]
  calc
    _≤(8*Real.log x)^16 := pow_le_pow_left₀ (by positivity) (by linarith) 16
    _=_ := by rw [mul_pow]

def decay (x : ℝ) : ℝ := Real.exp (-(Real.log (Real.log x))^2)

theorem decay_bounds (x : ℝ) : 0≤decay x ∧ decay x≤1 := by
  refine ⟨(Real.exp_pos _).le,?_⟩
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

theorem eventually_superlog (C : ℝ) (hC : 0≤C) (E A : ℕ) :
    ∀ᶠ x : ℝ in atTop,C*(Real.log x)^E*decay x≤1/(Real.log x)^A := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 C),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (E+A+1:ℝ)]
    with x hlog hL
  have hl1 : 1≤Real.log x := (le_max_left _ _).trans hlog
  have hl0 : 0<Real.log x := zero_lt_one.trans_le hl1
  have hL0 : 0≤Real.log (Real.log x) := Real.log_nonneg hl1
  have he : decay x≤1/(Real.log x)^(E+A+1) := by
    have H := mul_le_mul_of_nonneg_right hL hL0
    unfold decay
    rw [one_div,←Real.exp_log (pow_pos hl0 (E+A+1)),Real.log_pow,←Real.exp_neg]
    apply Real.exp_le_exp.mpr
    push_cast at H ⊢
    nlinarith only [H]
  calc
    _≤C*(Real.log x)^E/(Real.log x)^(E+A+1) := by
      simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left he (mul_nonneg hC (pow_nonneg (zero_le_one.trans hl1) _))
    _=C/(Real.log x)* (1/(Real.log x)^A) := by
      rw [pow_add,pow_add,pow_one]
      field_simp [hl0.ne']
      ring
    _≤1*(1/(Real.log x)^A) := mul_le_mul_of_nonneg_right
      ((div_le_one hl0).mpr ((le_max_right _ _).trans hlog)) (by positivity)
    _=_ := one_mul _

theorem eventually_power_log (C : ℝ) (hC : 0≤C) (E A : ℕ) (a : ℝ) (ha : a<1) :
    ∀ᶠ x : ℝ in atTop,C*(Real.log x)^E*x^a≤x/(Real.log x)^A := by
  filter_upwards [eventually_fixed_log_le_power C hC (E+A) (sub_pos.mpr ha),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hpay hx hlog
  have hx0 := zero_lt_one.trans hx
  have hl0 := zero_lt_one.trans_le hlog
  apply (le_div_iff₀ (pow_pos hl0 A)).mpr
  calc
    _=(C*(Real.log x)^(E+A))*x^a := by rw [pow_add]; ring
    _≤x^(1-a)*x^a := mul_le_mul_of_nonneg_right hpay (Real.rpow_nonneg hx0.le _)
    _=x := by rw [←Real.rpow_add hx0,show (1-a)+a=1 by ring,Real.rpow_one]

end
end ImbalancedChen.P4BOriginalE3LogPrices
