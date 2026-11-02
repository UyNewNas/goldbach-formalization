import ImbalancedChen.Part3ActualConductorWidthLower
import ImbalancedChen.Part3ActualRoughContourParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual delta=d/log(x^(1/(loglog x)^3)) eventually fits the literal
analytic conductorWidth at every associated primitive conductor<=q,
q<=log(x)^B. The moving height is T+abs(tau), with T=log(x)^C and
abs(tau)<=log(x)^L, L<=C. One threshold precedes q, the ORIGINAL character
and tau. All finite width branches from27 are paid by the genuine7ad
real-parameter lemma. No zero-free, norm or SW estimate is an assumption.
-/

namespace ImbalancedChen.Part3.ActualConductorWidthThreshold20261026b
noncomputable section
open Classical Complex Filter Topology
open RoughQuadraticLowRectangle20261026b ActualRoughContourHolomorphic20261026b
open ActualConductorWidthLower20261026b ActualRoughContourParameters20261026b

def shiftedHeightConstant (B C : ℝ) : ℝ:=2+|Real.log 4|+B+C

theorem shifted_heightLog_bound {B C L x : ℝ} (hB : 0≤B) (hC : 0≤C)
    (hLC : L≤C) (hlog : 1≤Real.log x) (hll : 0≤Real.log (Real.log x))
    (m : ℕ) [NeZero m] (hm : (m : ℝ)≤(Real.log x)^B)
    (τ : ℝ) (hτ : |τ|≤(Real.log x)^L) :
    rectangleLog m (contourT C x+|τ|)≤shiftedHeightConstant B C*(1+Real.log (Real.log x)) := by
  let T:=contourT C x
  have hlogpos : 0<Real.log x:=zero_lt_one.trans_le hlog
  have hT : 1≤T:=Real.one_le_rpow hlog hC
  have hτT : |τ|≤T:=hτ.trans (Real.rpow_le_rpow_of_exponent_le hlog hLC)
  have hH : 0≤T+|τ|+1:=by positivity
  have hfloor : ((Nat.floor (T+|τ|+1)+1 : ℕ) : ℝ)≤4*T:=by
    push_cast
    nlinarith [Nat.floor_le hH]
  have hprod : (rectangleCutoff m (T+|τ|) : ℝ)≤4*(Real.log x)^(B+C):=by
    calc
      _ = (m : ℝ)*((Nat.floor (T+|τ|+1)+1 : ℕ) : ℝ):=by simp [rectangleCutoff]
      _ ≤ (Real.log x)^B*(4*T):=
        mul_le_mul hm hfloor (by positivity) (Real.rpow_nonneg hlogpos.le _)
      _ = _:=by dsimp [T,contourT]; rw [Real.rpow_add hlogpos]; ring
  have hcutpos : 0<(rectangleCutoff m (T+|τ|) : ℝ):=by
    exact_mod_cast rectangleCutoff_pos m (T+|τ|)
  have hlg:=Real.log_le_log hcutpos hprod
  rw [Real.log_mul (by norm_num : (4 : ℝ)≠0)
    (Real.rpow_pos_of_pos hlogpos (B+C)).ne',Real.log_rpow hlogpos] at hlg
  have hconst : 1+Real.log 4≤shiftedHeightConstant B C:=by
    unfold shiftedHeightConstant
    linarith [le_abs_self (Real.log 4)]
  have hBC : B+C≤shiftedHeightConstant B C:=by
    unfold shiftedHeightConstant
    linarith [abs_nonneg (Real.log 4)]
  have hfirst : rectangleLog m (T+|τ|)≤1+Real.log 4+(B+C)*Real.log (Real.log x):=by
    unfold rectangleLog
    linarith
  exact hfirst.trans (by nlinarith [mul_le_mul_of_nonneg_right hBC hll])

/-- Exact actual width and original-q logarithmic disk gates at one real
threshold before all original characters and moving frequencies. The
literal cutoff is eventually >=2, so delta*log(max 2 roughZ)=d exactly. -/
theorem exists_actual_conductor_width_threshold
    (c A η d B C L : ℝ) (hc : 0<c) (hA : 0<A) (hη : 0<η) (hd : 0<d)
    (hB : 0≤B) (hC : 0≤C) (hLC : L≤C) (hgap : 14*B*η<1) :
    ∃ x0 : ℝ,1<x0 ∧ ∀ x : ℝ,x0≤x →
      0<roughDelta d x ∧ 2≤roughZ x ∧ roughDelta d x*Real.log (max 2 (roughZ x))=d ∧
      ∀ (q : ℕ) [NeZero q],(q : ℝ)≤(Real.log x)^B →
      ∀ (χ : DirichletCharacter ℂ q) (τ : ℝ),|τ|≤(Real.log x)^L →
      roughDelta d x≤conductorWidth c A η χ (contourT C x+|τ|) ∧
      roughDelta d x≤1/rectangleLog q (contourT C x+|τ|) := by
  let K:=shiftedHeightConstant B C
  let k:=widthConstant c A
  have hK : 0<K:=by dsimp [K,shiftedHeightConstant]; linarith [abs_nonneg (Real.log 4)]
  have hk : 0<k:=widthConstant_pos hc hA
  have hpay:=eventually_roughDelta_le_fourteenB_eta B η d (k/K^24) 24
    hd (div_pos hk (pow_pos hK 24)) hgap (by norm_num)
  have hdisk:=eventually_roughDelta_le_logPower_saving d (1/K) 0 1
    hd (one_div_pos.mpr hK) (by norm_num) (by norm_num)
  have hlog2 : 0<Real.log (2 : ℝ):=Real.log_pos (by norm_num)
  have hcut:=eventually_roughDelta_le_logPower_saving d (d/Real.log 2) 0 0
    hd (div_pos hd hlog2) (by norm_num) (by norm_num)
  have hll : ∀ᶠ x : ℝ in atTop,1≤Real.log (Real.log x):=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop 1)
  have hlog : ∀ᶠ x : ℝ in atTop,1≤Real.log x:=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  obtain ⟨x1,hx1⟩:=eventually_atTop.mp (hpay.and (hdisk.and (hcut.and (hll.and hlog))))
  refine ⟨max x1 2,lt_of_lt_of_le (by norm_num : (1 : ℝ)<2) (le_max_right _ _),?_⟩
  intro x hx
  have hh:=hx1 x ((le_max_left _ _).trans hx)
  have hxpos : 1<x:=lt_of_lt_of_le (by norm_num : (1 : ℝ)<2) ((le_max_right _ _).trans hx)
  have hell : 0<Real.log (Real.log x):=zero_lt_one.trans_le hh.2.2.2.1
  have hlogx : 1≤Real.log x:=hh.2.2.2.2
  have hlogxpos : 0<Real.log x:=zero_lt_one.trans_le hlogx
  have hz : 1<roughZ x:=Real.one_lt_rpow hxpos (one_div_pos.mpr (pow_pos hell 3))
  have hδ : 0<roughDelta d x:=div_pos hd (Real.log_pos hz)
  have hδcut : roughDelta d x≤d/Real.log 2:=by simpa using hh.2.2.1
  have hlogz : Real.log 2≤Real.log (roughZ x):=by
    have hmul: d*Real.log 2≤d*Real.log (roughZ x):=
      (div_le_div_iff₀ (Real.log_pos hz) hlog2).mp hδcut
    exact (mul_le_mul_iff_left₀ hd).mp hmul
  have hz2 : 2≤roughZ x:=
    (Real.log_le_log_iff (by norm_num : (0 : ℝ)<2) (zero_lt_one.trans hz)).mp hlogz
  have hcap : roughDelta d x*Real.log (max 2 (roughZ x))=d:=by
    rw [max_eq_right hz2,roughDelta,div_mul_cancel₀ _ (Real.log_pos hz).ne']
  refine ⟨hδ,hz2,hcap,?_⟩
  intro q _ hq χ τ hτ
  let m:=χ.conductor
  let H:=contourT C x+|τ|
  letI : NeZero m:=⟨χ.conductor_ne_zero⟩
  have hmpos : 0<(m : ℝ):=by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmq : m≤q:=Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hmcap : (m : ℝ)≤(Real.log x)^B:=(by exact_mod_cast hmq).trans hq
  have hD:=shifted_heightLog_bound hB hC hLC hlogx hell.le m hmcap τ hτ
  have hDq:=shifted_heightLog_bound hB hC hLC hlogx hell.le q hq τ hτ
  have hDpos : 0<rectangleLog m H:=lt_of_lt_of_le zero_lt_one (one_le_rectangleLog m H)
  have hQpos : 0<rectangleLog q H:=lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q H)
  have hllpos : 0<1+Real.log (Real.log x):=by linarith
  have hdm : (Real.log x)^(-(14*B*η))≤(m : ℝ)^(-14*η):=by
    have hp:=Real.rpow_le_rpow_of_nonpos hmpos hmcap (by linarith : -14*η≤0)
    rw [← Real.rpow_mul hlogxpos.le] at hp
    convert hp using 1 <;> congr 1 <;> ring
  have hDpow : (rectangleLog m H)^24≤K^24*(1+Real.log (Real.log x))^24:=by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hDpos.le hD 24
  have hpayx : roughDelta d x≤(k/K^24)*(Real.log x)^(-(14*B*η))/(1+Real.log (Real.log x))^24:=by
    simpa only [Real.rpow_natCast] using hh.1
  constructor
  · apply hpayx.trans
    apply le_trans _ (conductorWidth_lower hc hA hη χ (by dsimp [H,contourT]; positivity))
    calc
      _ = k*(Real.log x)^(-(14*B*η))/(K^24*(1+Real.log (Real.log x))^24):=by ring
      _ ≤ k*(m : ℝ)^(-14*η)/(rectangleLog m H)^24:=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hdm hk.le)
          (pow_pos hDpos 24) hDpow
  · have hdx : roughDelta d x≤(1/K)/(1+Real.log (Real.log x)):=by
      simpa using hh.2.1
    apply hdx.trans
    calc
      _ = 1/(K*(1+Real.log (Real.log x))):=by ring
      _ ≤ 1/rectangleLog q H:=one_div_le_one_div_of_le hQpos hDq

end
end ImbalancedChen.Part3.ActualConductorWidthThreshold20261026b
