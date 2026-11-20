import ImbalancedChen.P4BOriginalNoMediumPairRows
import ImbalancedChen.P5ActualHBRoughBrunRates
import ImbalancedChen.P4BOriginalHighRankPostModulusRow

/-! SOURCE ONLY / UNCOMPILED. Transport the actual pair chart cutoff and
the original .599 physical modulus bound to the SAME live local x.
The short product below is the block-lower product, never its integer owner. -/
namespace ImbalancedChen.P4BOriginalTwoLongActualScales
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalNoMediumPairRows
open P4BOriginalHighRankMotherScale (completeScale live_geometry)
open P4BOriginalHighRankLocalLevel (theta)
open P4BOriginalRankTwoChartScales (eventually_power)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos scales beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.OriginalChartRoughCutoff (roughF roughF_mono roughF_upper)
open P5Z.ActualHBRoughBrunRates (halfOrder nextOrder supportSize eventually_support_le_power)
open Part3.ActualRoughContourParameters20261026b (roughZ)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P4BOuterRampRoughness (baseline)

def brunEpsilon : ℝ := 1/16000

theorem fixed_margin {zeta : ℝ} (hz : zeta≤1/400) :
    0<brunEpsilon ∧ theta≤1 ∧
      40*zeta+2*brunEpsilon+3*theta/2≤1599/1600 ∧
      40*zeta+2*brunEpsilon+3*theta/2<1 := by
  refine ⟨by norm_num [brunEpsilon],by norm_num [theta],?_,?_⟩ <;>
    dsimp [brunEpsilon,theta] <;> linarith

theorem actual_cutoff_formula (K cj ck : ℕ) :
    beforeHBCutoff K [cj,ck]=roughF ((2:ℝ)^(6*K+2)*(4*(R cj*R ck))) := by
  have H : P5Z.OriginalChartRoughCutoff.argument K (scales [cj,ck])=
      (2:ℝ)^(6*K+2)*(4*(R cj*R ck)) := by
    norm_num [P5Z.OriginalChartRoughCutoff.argument,scales]
  simp only [beforeHBCutoff,P5Z.OriginalChartRoughCutoff.chartCutoff,H]

/-- Reuse the real-x small-y theorem at half the requested exponent.
The actual chart Z is at most roughZ(x)^2, so the original growing
integer Brun order is preserved without changing the prime alphabet. -/
theorem eventually_chart_brun (K : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠ x : ℝ in atTop,∀ X : ℝ,0<X → X≤16*x → x≤4*X →
      let Z := roughF ((2:ℝ)^(6*K+2)*(4*X))
      1≤Z ∧ Z^(2*halfOrder x+1)≤x^eps := by
  let C : ℝ := (2:ℝ)^(6*K+2)
  have hC : 1≤C := one_le_pow₀ (by norm_num)
  filter_upwards [eventually_support_le_power (eps/2) (half_pos heps),
    eventually_ge_atTop (Real.exp (Real.exp 3)),eventually_ge_atTop (64*C)]
    with x hsmall hlarge hconst
  intro X hX hXx hxX
  have hx : 1<x := hsmall.1
  have hxp := zero_lt_one.trans hx
  have hxv : x≤C*(4*X) := hxX.trans (by nlinarith)
  have hvx : C*(4*X)≤x^2 := by
    have H := mul_le_mul_of_nonneg_left hXx (show 0≤4*C by linarith)
    have J := mul_le_mul_of_nonneg_right hconst hxp.le
    nlinarith only [H,J]
  have hl3 : Real.exp 3≤Real.log x := (Real.le_log_iff_exp_le hxp).mpr hlarge
  have hll3 : 3≤Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (Real.log_pos hx)).mpr hl3
  have hlow := roughF_mono hx hll3 hxv
  have hupper := roughF_upper hx hll3 hxv hvx
  have hsq : x^(2/(Real.log (Real.log x))^3)=(roughZ x)^2 := by
    unfold roughZ
    rw [←Real.rpow_natCast,←Real.rpow_mul hxp.le]
    congr 1
    ring
  have hlow' : roughZ x≤roughF (C*(4*X)) := hlow
  refine ⟨hsmall.2.1.trans hlow',?_⟩
  calc
    _ ≤ ((roughZ x)^2)^(2*halfOrder x+1) :=
      pow_le_pow_left₀ (by dsimp [roughF]; positivity) (hupper.trans_eq hsq) _
    _ = (supportSize x)^2 := by simp only [supportSize,nextOrder,pow_mul]; congr 1; omega
    _ ≤ (x^(eps/2))^2 :=
      pow_le_pow_left₀ (by unfold supportSize; positivity) hsmall.2.2 2
    _ = x^eps := by rw [←Real.rpow_natCast,←Real.rpow_mul hxp.le]; congr 1; ring

theorem eventually_short_transport {zeta : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400) :
    ∀ᶠ x : ℝ in atTop,∀ X M : ℝ,0<X → X≤16*x → M≤X^(30*zeta) →
      M≤x^(40*zeta) ∧ ∀ U : ℝ,U≤X^(3*zeta) → 2*U≤x := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (Real.tendsto_rpow_atTop (by linarith : 0<10*zeta)).eventually_ge_atTop ((16:ℝ)^(30*zeta)),
    (Real.tendsto_rpow_atTop (by linarith : 0<1-3*zeta)).eventually_ge_atTop (2*(16:ℝ)^(3*zeta))]
    with x hx hMconst hUconst
  intro X M hX hXx hM
  have hxp := zero_lt_one.trans hx
  constructor
  · calc
      M≤X^(30*zeta) := hM
      _≤(16*x)^(30*zeta) := Real.rpow_le_rpow hX.le hXx (by linarith)
      _=(16:ℝ)^(30*zeta)*x^(30*zeta) := Real.mul_rpow (by norm_num) hxp.le
      _≤x^(10*zeta)*x^(30*zeta) := mul_le_mul_of_nonneg_right hMconst (by positivity)
      _=x^(40*zeta) := by rw [←Real.rpow_add hxp]; congr 1; ring
  · intro U hU
    have H := Real.rpow_le_rpow hX.le hXx (show 0≤3*zeta by linarith)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤16) hxp.le] at H
    have J := mul_le_mul_of_nonneg_right hUconst (Real.rpow_nonneg hxp.le (3*zeta))
    rw [←Real.rpow_add hxp,show (1-3*zeta)+3*zeta=1 by ring,Real.rpow_one] at J
    nlinarith only [hU,H,J]

theorem eventually_X_gates {zeta : ℝ} (hz : 0<zeta) :
    ∀ᶠ X : ℝ in atTop,4<X^(3*zeta/4) ∧
      ∀ cj ck : ℕ,X=R cj*R ck →
        hbCutoff cj≤X^(1/3+zeta/4:ℝ) ∧ hbCutoff ck≤X^(1/3+zeta/4:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (Real.tendsto_rpow_atTop (by linarith : 0<3*zeta/4)).eventually_gt_atTop 4,
    (Real.tendsto_rpow_atTop (by linarith : 0<zeta/4)).eventually_ge_atTop ((2:ℝ)^(1/3:ℝ))]
    with X hx hthree hcut
  refine ⟨hthree,?_⟩
  intro cj ck hX
  have hj : 1≤R cj := one_le_pow₀ (by norm_num)
  have hk : 1≤R ck := one_le_pow₀ (by norm_num)
  have cut (v : ℕ) (hv : R v≤X) : hbCutoff v≤X^(1/3+zeta/4:ℝ) := by
    calc
      _≤(2*X)^(1/3:ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _=(2:ℝ)^(1/3:ℝ)*X^(1/3:ℝ) := Real.mul_rpow (by norm_num) (by linarith)
      _≤X^(zeta/4)*X^(1/3:ℝ) := mul_le_mul_of_nonneg_right hcut (by positivity)
      _=X^(1/3+zeta/4:ℝ) := by rw [←Real.rpow_add (by linarith : 0<X)]; congr 1; ring
  exact ⟨cut cj (by rw [hX]; nlinarith),cut ck (by rw [hX]; nlinarith)⟩

/-- Fixed scalar thresholds are transported before choosing a row,
its source point, or its selected coordinate. -/
theorem eventually_live_large {kap0 : ℝ} (ht : kap0<1) (T : ℝ) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (y : Fin (u+v)→ℕ) (i : Fin (u+v)),
      y∈rectangle bs → integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0 →
      T≤completeScale bs y i ∧ T≤R cj*R ck := by
  filter_upwards [eventually_power (16*max 0 T) (1-kap0) (by linarith),
    eventually_ge_atTop (1:ℕ)] with N hsize hN
  intro b kap s hb hk hs hg u v cj ck bs y i hy hw
  obtain ⟨hlo,hhi,hX,hxX⟩ := live_geometry (by omega) hb hk hs hg cj ck bs y i hy hw
  have hT := le_max_right (0:ℝ) T
  have h0 := le_max_left (0:ℝ) T
  constructor <;> nlinarith

theorem eventually_mother_short_gap {zeta kap0 : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (y : Fin (u+v)→ℕ) (i : Fin (u+v)),
      y∈rectangle bs → integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0 →
      64*(R cj*R ck)^(18*zeta)<(N:ℝ)^(19/96:ℝ) := by
  let C : ℝ := 16*Real.exp 1
  have hC : 0<C := by dsimp [C]; positivity
  have hgap : 0<(19/96:ℝ)-18*zeta := by linarith
  filter_upwards [eventually_power (64*C^(18*zeta)) ((19/96:ℝ)-18*zeta) hgap,
    eventually_ge_atTop (1:ℕ)] with N hlarge hN
  intro b kap s hb hk hs hg u v cj ck bs y i hy hw
  obtain ⟨_,hhi,hX,_⟩ := live_geometry (by omega) hb hk hs hg cj ck bs y i hy hw
  have hNX : R cj*R ck≤C*N := by dsimp [C]; linarith
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  calc
    _≤64*(C*N)^(18*zeta) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hNX (by linarith)) (by norm_num)
    _=(64*C^(18*zeta))*(N:ℝ)^(18*zeta) := by rw [Real.mul_rpow hC.le hNp.le]; ring
    _<(N:ℝ)^((19/96:ℝ)-18*zeta)*(N:ℝ)^(18*zeta) :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hNp _)
    _=(N:ℝ)^(19/96:ℝ) := by rw [←Real.rpow_add hNp]; congr 1; ring

end
end ImbalancedChen.P4BOriginalTwoLongActualScales
