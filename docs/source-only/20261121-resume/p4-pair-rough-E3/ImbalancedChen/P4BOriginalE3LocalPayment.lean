import ImbalancedChen.P4BOriginalE3LogPrices

/-! SOURCE ONLY / UNCOMPILED. The original polynomial and twice-mean
invoices are paid with fixed log prices and the actual small-M geometry.
All constants and requested accuracies precede the real x threshold. -/
namespace ImbalancedChen.P4BOriginalE3LocalPayment
noncomputable section
open Classical Filter
open scoped SchwartzMap
open P4BOriginalE3LogPrices
open P4BOriginalPositiveLongEnvelope
open P4BOriginalEnvelopePolynomialPayment (p2Price p2Price_nonneg)
open P4BOriginalRoughE3Assembly (polyMoment reciprocalMoment)
open P4BOriginalPairMeanNorm (densityLog densityLog_one_le)
open P4BOriginalPairMeanGeometry (mean_power_terms)
open P4BOriginalTwoLongActualScales (brunEpsilon fixed_margin)
open P4BOriginalHighRankLocalLevel (theta)
open Part3.TwoLongTransitionMellinN2
open Part3.TwoLongHBMellinBrunProfiles (pairCost pairCost_nonneg)
open Part3.TwoLongMellinLogBudget
open Part3.TwoLongActualLowerCorePayment (moment_log_budget)

def meanBill (delta U V x y mu : ℝ) (D : ℕ) : ℝ :=
  2*mu*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
    (2*U*V*decay x*densityLog x+2*densityLog x*(U+V)*y+2*y^2)
def meanBillConstant : ℝ := 2*4096*16*8^16*meanLogConstant
def meanBillExponent (B : ℕ) : ℕ := 31+4*B

theorem meanBillConstant_nonneg : 0≤meanBillConstant := by
  have h := meanLogConstant_nonneg
  unfold meanBillConstant
  positivity

theorem meanBill_log {x U V y M mu : ℝ} (B : ℕ) (D : ℕ)
    (hx : 1<x) (hlog : 1≤Real.log x) (hU : 1≤U) (hV : 1≤V) (hUx : U≤4*x) (hVx : V≤4*x)
    (hD : 1≤D) (hDx : (D:ℝ)≤x) (hy : 0≤y) (hM : 0≤M) (hmu : 0≤mu)
    (hmuBound : mu≤4096*M*(Real.log x)^12) :
    meanBill ((Real.log x)^B)⁻¹ U V x y mu D≤
      meanBillConstant*(Real.log x)^(meanBillExponent B)*
        (M*U*V*decay x+M*(U+V)*y+M*y^2) := by
  have hx0 := zero_lt_one.trans hx
  have hL0 := zero_le_one.trans hlog
  have hprice := meanPrice_log B hx0 hlog hU hV hUx hVx
  have hmoment := reciprocalMoment_log hD hlog hDx
  have hdl : densityLog x≤8*Real.log x := by unfold densityLog; linarith
  have he := (decay_bounds x).1
  have hbracket : 2*U*V*decay x*densityLog x+2*densityLog x*(U+V)*y+2*y^2≤
      16*Real.log x*(U*V*decay x+(U+V)*y+y^2) := by
    have H0 := mul_le_mul_of_nonneg_left hdl (by positivity : 0≤2*U*V*decay x)
    have H1 := mul_le_mul_of_nonneg_left hdl (by positivity : 0≤2*(U+V)*y)
    have H2 := mul_le_mul_of_nonneg_right (show (2:ℝ)≤16*Real.log x by linarith) (sq_nonneg y)
    nlinarith only [H0,H1,H2]
  have hc := meanLogConstant_nonneg
  have hp1 := meanPrice_nonneg ((Real.log x)^B)⁻¹ U
  have hp2 := meanPrice_nonneg ((Real.log x)^B)⁻¹ V
  have hm0 : 0≤reciprocalMoment D := by unfold reciprocalMoment; positivity
  have hb0 : 0≤2*U*V*decay x*densityLog x+2*densityLog x*(U+V)*y+2*y^2 := by
    have H := densityLog_one_le hx.le
    positivity
  calc
    _=2*mu*(meanPrice ((Real.log x)^B)⁻¹ U*meanPrice ((Real.log x)^B)⁻¹ V)*reciprocalMoment D*
        (2*U*V*decay x*densityLog x+2*densityLog x*(U+V)*y+2*y^2) := by unfold meanBill; ring
    _≤2*(4096*M*(Real.log x)^12)*(meanLogConstant*(Real.log x)^(2+4*B))*
        (8^16*(Real.log x)^16)*(16*Real.log x*(U*V*decay x+(U+V)*y+y^2)) := by gcongr
    _=_ := by unfold meanBillConstant meanBillExponent; simp only [pow_add,pow_mul]; ring

theorem eventually_meanBill_paid (B A : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ U V y M mu : ℝ,∀ D : ℕ,
      1≤U → 1≤V → U≤4*x → V≤4*x → 1≤D → (D:ℝ)≤x →
      0≤y → 0≤M → 0≤mu → mu≤4096*M*(Real.log x)^12 →
      M*U*V≤4*x → x^(1/3:ℝ)≤U → x^(1/3:ℝ)≤V →
      M≤x^(1/10:ℝ) → y≤x^brunEpsilon →
      meanBill ((Real.log x)^B)⁻¹ U V x y mu D≤x/(Real.log x)^A := by
  let C := meanBillConstant
  let E := meanBillExponent B
  have hC : 0≤C := meanBillConstant_nonneg
  filter_upwards [eventually_superlog (4*C) (by positivity) E (A+1),
    eventually_power_log (8*C) (by positivity) E (A+1) (2/3+brunEpsilon) (by norm_num [brunEpsilon]),
    eventually_power_log C hC E (A+1) (1/10+2*brunEpsilon) (by norm_num [brunEpsilon]),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (3:ℝ)]
    with x he h1 h2 hx hlog
  intro U V y M mu D hU hV hUx hVx hD hDx hy hM hmu hmub hprod hUmin hVmin hMp hyp
  have hl0 : 0<Real.log x := by linarith
  obtain ⟨hcross,hsquare⟩ := mean_power_terms hx hM (zero_le_one.trans hU) (zero_le_one.trans hV) hy hprod hUmin hVmin hMp hyp
  have hlead := mul_le_mul_of_nonneg_right hprod (decay_bounds x).1
  have H := meanBill_log B D hx (by linarith) hU hV hUx hVx hD hDx hy hM hmu hmub
  have hsum : M*U*V*decay x+M*(U+V)*y+M*y^2≤
      4*x*decay x+8*x^(2/3+brunEpsilon:ℝ)+x^(1/10+2*brunEpsilon:ℝ) := by linarith
  have Hlead : C*(Real.log x)^E*(4*x*decay x)≤x/(Real.log x)^(A+1) := by
    have hh := mul_le_mul_of_nonneg_right he (zero_lt_one.trans hx).le
    nlinarith only [hh]
  calc
    _≤C*(Real.log x)^E*(4*x*decay x+8*x^(2/3+brunEpsilon:ℝ)+x^(1/10+2*brunEpsilon:ℝ)) :=
      H.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (pow_nonneg hl0.le _)))
    _≤3*x/(Real.log x)^(A+1) := by nlinarith only [Hlead,h1,h2]
    _=(3/Real.log x)*(x/(Real.log x)^A) := by rw [pow_succ]; field_simp [hl0.ne']; ring
    _≤1*(x/(Real.log x)^A) := mul_le_mul_of_nonneg_right ((div_le_one hl0).mpr hlog) (by positivity)
    _=_ := one_mul _

theorem eventually_polynomialBill_paid (B K A : ℕ) (hB : 1≤B)
    {zeta : ℝ} (hz1 : zeta≤1/400) :
    ∀ᶠ x : ℝ in atTop,∀ (U V y M mu t1 t2 : ℝ) (D : ℕ),
      1≤U → 1≤V → U≤4*x → V≤4*x → 1≤D → (D:ℝ)≤x^theta →
      0≤M → M≤x^(40*zeta) → 0≤y → y≤x^brunEpsilon → 0≤mu →
      mu≤4096*M*(Real.log x)^12 → |t1|≤(Real.log x)^K → |t2|≤(Real.log x)^K →
      ∀ (fGap fLog gGap gLog : Bool) (hd : 0<((Real.log x)^B)⁻¹) (hs : ((Real.log x)^B)⁻¹≤1/4),
      let delta := ((Real.log x)^B)⁻¹
      let F := profileSchwartz fGap fLog hd hs U t1
      let G := profileSchwartz gGap gLog hd hs V t2
      let E := envelopeSchwartz hd hs U
      let J := envelopeSchwartz hd hs V
      (p2Price F G+2*p2Price E J)*(y^2*mu)*polyMoment D≤x/(Real.log x)^A := by
  obtain ⟨heps,htheta,_,hmargin⟩ := fixed_margin hz1
  filter_upwards [eventually_twoLong_E4_monomial B K 29 A 4 (by norm_num)
    zeta theta brunEpsilon heps hmargin,
    Real.tendsto_log_atTop.eventually_ge_atTop (19*8192*8^16:ℝ)] with x hpay hlarge
  intro U V y M mu t1 t2 D hU hV hUx hVx hD hDx hM hMp hy hyp hmu hmub ht1 ht2 fGap fLog gGap gLog hd hs
  have hx := hpay.1
  have hlog := hpay.2.1
  have hDx' : (D:ℝ)≤x := hDx.trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx htheta)
  have hH : 0≤(Real.log x)^K := pow_nonneg (zero_le_one.trans hlog) _
  have hp := primary_price fGap fLog gGap gLog hd hs hH ht1 ht2
  have he := envelope_price_pair (U:=U) (V:=V) hd hs hH
  have hprice : p2Price (profileSchwartz fGap fLog hd hs U t1) (profileSchwartz gGap gLog hd hs V t2)+
      2*p2Price (envelopeSchwartz hd hs U) (envelopeSchwartz hd hs V)≤19*pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K) := by linarith
  have hmoment := moment_log_budget hD hlog hDx'
  have hpc := pairCost_nonneg ((Real.log x)^B)⁻¹ U V ((Real.log x)^K)
  have hm0 : 0≤polyMoment D := by unfold polyMoment; positivity
  calc
    _≤(19*pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K))*(y^2*(4096*M*(Real.log x)^12))*
        ((2*8^16:ℝ)*(D:ℝ)^(3/2:ℝ)*(Real.log x)^16) := by gcongr
    _=pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K)*
        (M*y^2*(D:ℝ)^(3/2:ℝ))*((19*8192*8^16:ℝ)*(Real.log x)^28) := by ring
    _≤pairCost ((Real.log x)^B)⁻¹ U V ((Real.log x)^K)*
        (M*y^2*(D:ℝ)^(3/2:ℝ))*(Real.log x)^29 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have H := mul_le_mul_of_nonneg_right hlarge (pow_nonneg (zero_le_one.trans hlog) 28)
      nlinarith only [H]
    _≤_ := hpay.2.2 M y D U V hM hy (Nat.cast_nonneg _) hMp hyp hDx hU hV hUx hVx

end
end ImbalancedChen.P4BOriginalE3LocalPayment
