import ImbalancedChen.P4BOriginalSharpNativeRow

/-! SOURCE ONLY / UNCOMPILED. Choose delta's fixed log order AFTER
the required accuracy. Small strip mass pays the x*delta term; the
delta^-2/-4 errors keep their independent power reserves. -/
namespace ImbalancedChen.P4BOriginalSharpEndpointPrices
noncomputable section
open Classical Filter
open scoped SchwartzMap
open P4BOriginalSharpLongProfiles
open P4BOriginalSharpStripMean
open P4BOriginalEnvelopePolynomialPayment (p2Price p2Price_nonneg)
open P4BOriginalRoughE3Assembly (polyMoment reciprocalMoment)
open P4BOriginalPairMeanNorm (densityLog densityLog_one_le)
open P4BOriginalPairMeanGeometry (mean_power_terms)
open P4BOriginalE3LogPrices (eventually_power_log reciprocalMoment_log)
open P4BOriginalE3LocalPayment (eventually_polynomialBill_paid)
open P4BOriginalTwoLongActualScales (brunEpsilon)
open P4BOriginalHighRankLocalLevel (theta)
open Part3.TwoLongMellinLogBudget (logSize_le_scaled)
open Part3.TwoLongTransitionMellinN2 (logSize logSize_one_le profileSchwartz)

/-- The INNER long-endpoint smoothing order, chosen from local accuracy.
An outer mother amplitude may have its own fixed order B0. For a later
mother application, first fix B0 and its loss C(B0), then request local
accuracy A' = A + C(B0) + margin and use endpointOrder A'. No bound here
defines B by a loss depending on that same B. -/
def endpointOrder (A : ℕ) : ℕ := A+40
def sizeConstant : ℝ := (4+|Real.log (4:ℝ)|)^2
def stripBase : ℝ := 8192*8^16*sizeConstant
def stripRateConstant : ℝ := max (8192*stripBase)
  (max (256*stripPrice*stripBase) (2*stripPrice^2*stripBase))

theorem sizeConstant_nonneg : 0≤sizeConstant := by unfold sizeConstant; positivity
theorem stripBase_nonneg : 0≤stripBase := by have H:=sizeConstant_nonneg; unfold stripBase; positivity
theorem stripRateConstant_nonneg : 0≤stripRateConstant :=
  (mul_nonneg (by norm_num) stripBase_nonneg).trans (le_max_left _ _)

theorem log_product_bound {x U V : ℝ} (hx0 : 0<x) (hlog : 1≤Real.log x)
    (hU : 1≤U) (hV : 1≤V) (hUx : U≤4*x) (hVx : V≤4*x) :
    logSize U*logSize V≤sizeConstant*(Real.log x)^2 := by
  have H1 := logSize_le_scaled (by norm_num : (0:ℝ)<4) hx0 hlog hU hUx
  have H2 := logSize_le_scaled (by norm_num : (0:ℝ)<4) hx0 hlog hV hVx
  exact (mul_le_mul H1 H2 (zero_le_one.trans (logSize_one_le V)) (by positivity)).trans_eq
    (by unfold sizeConstant; ring)

theorem eventually_inverse_log (C : ℝ) (hC : 0≤C) (E A B : ℕ) (hB : E+A+1≤B) :
    ∀ᶠ x : ℝ in atTop,C*(Real.log x)^E*((Real.log x)^B)⁻¹≤1/(Real.log x)^A := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 C)] with x hlog
  have h1 := (le_max_left _ _).trans hlog
  have h0 : 0<Real.log x := zero_lt_one.trans_le h1
  calc
    _=C*(Real.log x)^E/(Real.log x)^B := by rw [div_eq_mul_inv]
    _≤C*(Real.log x)^E/(Real.log x)^(E+A+1) :=
      div_le_div_of_nonneg_left (mul_nonneg hC (pow_nonneg h0.le _)) (pow_pos h0 _) (pow_le_pow_right₀ h1 hB)
    _=(C/Real.log x)*(1/(Real.log x)^A) := by rw [pow_add,pow_add,pow_one]; field_simp [h0.ne']; ring
    _≤1*(1/(Real.log x)^A) := mul_le_mul_of_nonneg_right
      ((div_le_one h0).mpr ((le_max_right _ _).trans hlog)) (by positivity)
    _=_ := one_mul _

theorem stripMeanBill_log (B : ℕ) {x U V y M mu : ℝ} (D : ℕ)
    (hx : 1<x) (hlog : 1≤Real.log x) (hU : 1≤U) (hV : 1≤V) (hUx : U≤4*x) (hVx : V≤4*x)
    (hD : 1≤D) (hDx : (D:ℝ)≤x) (hy : 0≤y) (hM : 0≤M) (hmu : 0≤mu)
    (hmub : mu≤4096*M*(Real.log x)^12) (hprod : M*U*V≤4*x)
    (hUmin : x^(1/3:ℝ)≤U) (hVmin : x^(1/3:ℝ)≤V)
    (hMp : M≤x^(1/10:ℝ)) (hyp : y≤x^brunEpsilon) :
    logSize U*logSize V*stripMeanBill ((Real.log x)^B)⁻¹ U V x y mu D≤
      stripRateConstant*(x*((Real.log x)^B)⁻¹*(Real.log x)^32+
        x^(2/3+brunEpsilon:ℝ)*(Real.log x)^(31+B*2)+
        x^(1/10+2*brunEpsilon:ℝ)*(Real.log x)^(30+B*4)) := by
  let delta := ((Real.log x)^B)⁻¹
  have hl0 : 0<Real.log x := zero_lt_one.trans_le hlog
  have hd : 0<delta := inv_pos.mpr (pow_pos hl0 _)
  have hP := stripPrice_nonneg
  have hBase := stripBase_nonneg
  have hL := log_product_bound (zero_lt_one.trans hx) hlog hU hV hUx hVx
  have hR := reciprocalMoment_log hD hlog hDx
  have hdl : densityLog x≤8*Real.log x := by unfold densityLog; linarith
  have hdl0 := zero_le_one.trans (densityLog_one_le hx.le)
  have hbill0 : 0≤32*delta*U*V*(densityLog x)^2+4*stripPrice/delta^2*(U+V)*y*densityLog x+2*stripPrice^2/delta^4*y^2 := by positivity
  have hb : 32*delta*U*V*(densityLog x)^2+4*stripPrice/delta^2*(U+V)*y*densityLog x+2*stripPrice^2/delta^4*y^2≤
      2048*delta*U*V*(Real.log x)^2+32*stripPrice/delta^2*(U+V)*y*Real.log x+2*stripPrice^2/delta^4*y^2 := by
    have H0 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hdl0 hdl 2) (by positivity : 0≤32*delta*U*V)
    have H1 := mul_le_mul_of_nonneg_left hdl (by positivity : 0≤4*stripPrice/delta^2*(U+V)*y)
    nlinarith only [H0,H1]
  have hfactor : logSize U*logSize V*(2*mu*reciprocalMoment D)≤stripBase*M*(Real.log x)^30 := by
    have hLp0 := mul_nonneg (zero_le_one.trans (logSize_one_le U)) (zero_le_one.trans (logSize_one_le V))
    have hR0 : 0≤reciprocalMoment D := by unfold reciprocalMoment; positivity
    calc
      _≤(sizeConstant*(Real.log x)^2)*(2*(4096*M*(Real.log x)^12)*(8^16*(Real.log x)^16)) := by gcongr
      _=_ := by unfold stripBase; ring
  obtain ⟨hcross,hsquare⟩ := mean_power_terms hx hM (zero_le_one.trans hU) (zero_le_one.trans hV) hy hprod hUmin hVmin hMp hyp
  have hc0 : 8192*stripBase≤stripRateConstant := le_max_left _ _
  have hc1 : 256*stripPrice*stripBase≤stripRateConstant := (le_max_left _ _).trans (le_max_right _ _)
  have hc2 : 2*stripPrice^2*stripBase≤stripRateConstant := (le_max_right _ _).trans (le_max_right _ _)
  calc
    _=(logSize U*logSize V*(2*mu*reciprocalMoment D))*
        (32*delta*U*V*(densityLog x)^2+4*stripPrice/delta^2*(U+V)*y*densityLog x+2*stripPrice^2/delta^4*y^2) := by unfold stripMeanBill; ring
    _≤(stripBase*M*(Real.log x)^30)*
        (2048*delta*U*V*(Real.log x)^2+32*stripPrice/delta^2*(U+V)*y*Real.log x+2*stripPrice^2/delta^4*y^2) :=
      mul_le_mul hfactor hb hbill0 (by positivity)
    _=(2048*stripBase)*(M*U*V)*delta*(Real.log x)^32+
        (32*stripPrice*stripBase)*(M*(U+V)*y)*(Real.log x)^(31+B*2)+
        (2*stripPrice^2*stripBase)*(M*y^2)*(Real.log x)^(30+B*4) := by
      dsimp [delta]
      simp only [inv_pow,div_inv_eq_mul,pow_add,pow_mul]
      ring
    _≤(8192*stripBase)*x*delta*(Real.log x)^32+
        (256*stripPrice*stripBase)*x^(2/3+brunEpsilon:ℝ)*(Real.log x)^(31+B*2)+
        (2*stripPrice^2*stripBase)*x^(1/10+2*brunEpsilon:ℝ)*(Real.log x)^(30+B*4) := by gcongr
    _≤stripRateConstant*(x*delta*(Real.log x)^32)+
        stripRateConstant*(x^(2/3+brunEpsilon:ℝ)*(Real.log x)^(31+B*2))+
        stripRateConstant*(x^(1/10+2*brunEpsilon:ℝ)*(Real.log x)^(30+B*4)) := by gcongr
    _=_ := by dsimp [delta]; ring

theorem eventually_stripMean_paid (A : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ U V y M mu : ℝ,∀ D : ℕ,
      1≤U → 1≤V → U≤4*x → V≤4*x → 1≤D → (D:ℝ)≤x →
      0≤y → 0≤M → 0≤mu → mu≤4096*M*(Real.log x)^12 →
      M*U*V≤4*x → x^(1/3:ℝ)≤U → x^(1/3:ℝ)≤V →
      M≤x^(1/10:ℝ) → y≤x^brunEpsilon →
      logSize U*logSize V*stripMeanBill ((Real.log x)^(endpointOrder A))⁻¹ U V x y mu D≤x/(Real.log x)^(A+1) := by
  let B := endpointOrder A
  let C := stripRateConstant
  have hC : 0≤C := stripRateConstant_nonneg
  filter_upwards [eventually_inverse_log C hC 32 (A+2) B (by dsimp [B,endpointOrder]; omega),
    eventually_power_log C hC (31+B*2) (A+2) (2/3+brunEpsilon) (by norm_num [brunEpsilon]),
    eventually_power_log C hC (30+B*4) (A+2) (1/10+2*brunEpsilon) (by norm_num [brunEpsilon]),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (3:ℝ)] with x h0 h1 h2 hx hlog
  intro U V y M mu D hU hV hUx hVx hD hDx hy hM hmu hmub hprod hUmin hVmin hMp hyp
  have H := stripMeanBill_log B D hx (by linarith) hU hV hUx hVx hD hDx hy hM hmu hmub hprod hUmin hVmin hMp hyp
  have H0 := mul_le_mul_of_nonneg_right h0 (zero_lt_one.trans hx).le
  have hl0 : 0<Real.log x := by linarith
  calc
    _≤3*x/(Real.log x)^(A+2) := by nlinarith only [H,H0,h1,h2]
    _=(3/Real.log x)*(x/(Real.log x)^(A+1)) := by
      rw [show A+2=(A+1)+1 by omega,pow_succ]; field_simp [hl0.ne']; ring
    _≤1*(x/(Real.log x)^(A+1)) := mul_le_mul_of_nonneg_right ((div_le_one hl0).mpr hlog) (by positivity)
    _=_ := one_mul _

theorem eventually_endpoint_invoice_paid (A : ℕ) {zeta : ℝ} (hz1 : zeta≤1/400) :
    ∀ᶠ x : ℝ in atTop,∀ (U V y M mu : ℝ) (D : ℕ),
      1≤U → 1≤V → U≤4*x → V≤4*x → 1≤D → (D:ℝ)≤x^theta →
      0≤M → M≤x^(40*zeta) → 0≤y → y≤x^brunEpsilon → 0≤mu → mu≤4096*M*(Real.log x)^12 →
      M*U*V≤4*x → x^(1/3:ℝ)≤U → x^(1/3:ℝ)≤V →
      ∀ (hd : 0<((Real.log x)^(endpointOrder A))⁻¹) (hs : ((Real.log x)^(endpointOrder A))⁻¹≤1/4),
      let delta := ((Real.log x)^(endpointOrder A))⁻¹
      logSize U*logSize V*((p2Price (stripProfile true hd hs U) (stripProfile false hd hs V)+
        p2Price (stripProfile false hd hs U) (stripProfile true hd hs V))*(y^2*mu)*polyMoment D+
        stripMeanBill delta U V x y mu D)≤x/(Real.log x)^A := by
  let B := endpointOrder A
  have hB : 1≤B := by dsimp [B,endpointOrder]; omega
  filter_upwards [eventually_polynomialBill_paid B 0 (A+4) hB hz1,eventually_stripMean_paid A,
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (max 3 sizeConstant)]
    with x hpoly hmean hx hlog
  intro U V y M mu D hU hV hUx hVx hD hDx hM hMp hy hyp hmu hmub hprod hUmin hVmin hd hs
  have hl3 := (le_max_left _ _).trans hlog
  have hl0 : 0<Real.log x := by linarith
  have hMx : M≤x^(1/10:ℝ) := hMp.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  have hDx' : (D:ℝ)≤x := hDx.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx.le (show theta≤1 by norm_num [theta]))
  have Hmean := hmean U V y M mu D hU hV hUx hVx hD hDx' hy hM hmu hmub hprod hUmin hVmin hMx hyp
  have P1 := hpoly U V y M mu 0 0 D hU hV hUx hVx hD hDx hM hMp hy hyp hmu hmub (by simp) (by simp)
    true false false false hd hs
  have P2 := hpoly U V y M mu 0 0 D hU hV hUx hVx hD hDx hM hMp hy hyp hmu hmub (by simp) (by simp)
    false false true false hd hs
  have hfactor : 0≤(y^2*mu)*polyMoment D := by unfold polyMoment; positivity
  have hdrop := mul_nonneg (P4BOriginalEnvelopePolynomialPayment.p2Price_nonneg
    (P4BOriginalPositiveLongEnvelope.envelopeSchwartz hd hs U)
    (P4BOriginalPositiveLongEnvelope.envelopeSchwartz hd hs V)) hfactor
  have hsum : (p2Price (stripProfile true hd hs U) (stripProfile false hd hs V)+
      p2Price (stripProfile false hd hs U) (stripProfile true hd hs V))*(y^2*mu)*polyMoment D≤2*x/(Real.log x)^(A+4) := by
    dsimp only [stripProfile] at P1 P2 ⊢
    nlinarith only [P1,P2,hdrop]
  have hLp0 := mul_nonneg (zero_le_one.trans (logSize_one_le U)) (zero_le_one.trans (logSize_one_le V))
  have hLp : logSize U*logSize V≤(Real.log x)^3 :=
    (log_product_bound (zero_lt_one.trans hx) (by linarith) hU hV hUx hVx).trans (by
      have H := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hlog) (sq_nonneg (Real.log x))
      nlinarith only [H])
  have Hpoly : logSize U*logSize V*((p2Price (stripProfile true hd hs U) (stripProfile false hd hs V)+
      p2Price (stripProfile false hd hs U) (stripProfile true hd hs V))*(y^2*mu)*polyMoment D)≤2*x/(Real.log x)^(A+1) := by
    calc
      _≤logSize U*logSize V*(2*x/(Real.log x)^(A+4)) := mul_le_mul_of_nonneg_left hsum hLp0
      _≤(Real.log x)^3*(2*x/(Real.log x)^(A+4)) := mul_le_mul_of_nonneg_right hLp (by positivity)
      _=_ := by rw [show A+4=(A+1)+3 by omega,pow_add]; field_simp [hl0.ne']; ring
  calc
    _≤3*x/(Real.log x)^(A+1) := by nlinarith only [Hpoly,Hmean]
    _=(3/Real.log x)*(x/(Real.log x)^A) := by rw [pow_succ]; field_simp [hl0.ne']; ring
    _≤1*(x/(Real.log x)^A) := mul_le_mul_of_nonneg_right ((div_le_one hl0).mpr hl3) (by positivity)
    _=_ := one_mul _

end
end ImbalancedChen.P4BOriginalSharpEndpointPrices
