import ImbalancedChen.Part3OriginalPositiveOrbitCharts

/-! Exact remaining product and log-product substitutions at fixed q>0. The
argument left for the ratio window is 4π√(k−p), with k=(q/(4π))². -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open RadialSchrodingerL2Form20261025a (RadialTest)
open OriginalAbelGaussian (productAt dilation)
open OriginalAbelOrbit (heights)
open OriginalPositiveHeightTest20261112 (height)
open private height_integral from ImbalancedChen.Part3OriginalAbelOrbit
open private slopeOf jac p_slope slope_range slope_deriv slope_root from ImbalancedChen.Part3OriginalPrescribedAbelOrbit

def energy (q : ℝ) := (q/(4*Real.pi))^2
def rest (k p : ℝ) := 4*Real.pi*Real.sqrt (k-p)
def sample (H : RadialTest) (R q l : ℝ) : ℂ :=
  let p := Real.exp (l-R)
  let k := energy q
  if p<k then ((q/rest k p:ℝ):ℂ)*response H (rest k p) else 0

private theorem compensate {q p : ℝ} (hq : 0<q) (hp : p∈Ioo 0 (energy q)) :
    4*Real.pi/q*(2*(jac (energy q) p*Real.sqrt p))=p⁻¹*(q/rest (energy q) p) := by
  have sa := (Real.sqrt_pos.mpr hp.1).ne'
  have sb := (Real.sqrt_pos.mpr (sub_pos.mpr hp.2)).ne'
  rw [jac,rest]
  field_simp [hq.ne',Real.pi_ne_zero,hp.1.ne',sa,sb]
  dsimp [energy]; field_simp [Real.pi_ne_zero] <;> ring

private theorem log_product (η H : RadialTest) (R : ℝ) {q : ℝ} (hq : 0<q) :
    (∫ p in Ioo (0:ℝ) (energy q),
      (p⁻¹:ℝ) • (η.function (Real.log p+R)*((q/rest (energy q) p:ℝ):ℂ)*response H (rest (energy q) p))) =
      ∫ l : ℝ,η.function l*sample H R q l := by
  let k := energy q
  let F := fun p : ℝ => p⁻¹ • (η.function (Real.log p+R)*((q/rest k p:ℝ):ℂ)*response H (rest k p))
  let G := (Iio k).indicator F
  have cut : (∫ p,G p ∂heights)=∫ p in Ioo (0:ℝ) k,F p := by
    change (∫ p in Ioi (0:ℝ),(Iio k).indicator F p)=_
    rw [setIntegral_indicator measurableSet_Iio]; rfl
  have h := height_integral (p:=1) (by norm_num) G
  change (∫ p in Ioo (0:ℝ) k,F p)=_
  rw [←cut,h,←integral_add_right_eq_self (fun l : ℝ => η.function l*sample H R q l) R]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    dsimp only [G,dilation,Real.sqrt_one,one_mul]
    rw [sample,show w+R-R=w by ring]
    by_cases e : Real.exp w<k
    · rw [indicator_of_mem e,if_pos e]
      dsimp only [F]; rw [smul_smul,mul_inv_cancel₀ (Real.exp_pos w).ne',one_smul,Real.log_exp]; ring
    · rw [indicator_of_notMem e,if_neg e,smul_zero,mul_zero]

theorem induced_formula (η H : RadialTest) (R : ℝ) {q : ℝ} (hq : 0<q) :
    induced (height η H R) q=∫ l : ℝ,η.function l*sample H R q l := by
  let k := energy q
  have hk : 0<k := by dsimp [k,energy]; positivity
  let Z := fun s : ℝ => amp η R k s*response H (4*Real.pi*Real.sqrt (productAt k s)*s)
  have J := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun p hp => (slope_deriv hp).hasDerivWithinAt)
    (fun a ha b hb he => (p_slope ha).symm.trans ((congrArg (productAt k) he).trans (p_slope hb))) Z
  rw [slope_range hk] at J
  rw [induced,positive_slopes η H R hk]
  change (4*Real.pi/q:ℝ) • (2*(∫ s in Ioi (0:ℝ),Z s))=_
  rw [J,←log_product η H R hq,←integral_const_mul,←integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro p hp
  have e := sub_pos.mpr hp.2
  have sa := Real.sqrt_pos.mpr hp.1
  have arg : 4*Real.pi*Real.sqrt p*slopeOf k p=rest k p := by
    rw [slope_root hp,rest]; field_simp [sa.ne']
  have jacp : 0<jac k p := by dsimp [jac]; positivity
  dsimp only [Z,amp]
  rw [p_slope hp,arg,abs_neg,abs_of_pos jacp]
  simp only [Complex.real_smul]
  have S := congrArg Complex.ofReal (compensate hq hp)
  push_cast at S ⊢
  linear_combination (η.function (Real.log p+R)*response H (rest k p))*S

theorem sample_measurable (H : RadialTest) (R q : ℝ) : Measurable (sample H R q) := by
  dsimp [sample,rest]
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) _ measurable_const
  exact (by fun_prop).mul ((response_continuous H).measurable.comp (by fun_prop))

theorem sample_price (H : RadialTest) {A : ℝ} (price : ∀ v>0,‖response H v‖≤A*v)
    (R : ℝ) {q : ℝ} (hq : 0<q) (l : ℝ) (a0 : 0≤A) : ‖sample H R q l‖≤A*q := by
  dsimp only [sample]
  split_ifs with cut
  · have vp : 0<rest (energy q) (Real.exp (l-R)) :=
      mul_pos (by positivity) (Real.sqrt_pos.mpr (sub_pos.mpr cut))
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (div_nonneg hq.le vp.le)]
    calc
      _ ≤ q/rest (energy q) (Real.exp (l-R))*(A*rest (energy q) (Real.exp (l-R))) :=
        mul_le_mul_of_nonneg_left (price _ vp) (div_nonneg hq.le vp.le)
      _ = _ := by field_simp [vp.ne']
  · simpa only [norm_zero] using mul_nonneg a0 hq.le

theorem sample_limit (H : RadialTest) {q : ℝ} (hq : 0<q) (l : ℝ) :
    Tendsto (fun R : ℝ => sample H R q l) atTop (𝓝 (response H q)) := by
  let k := energy q
  have hk : 0<k := by dsimp [k,energy]; positivity
  have p : Tendsto (fun R : ℝ => Real.exp (l-R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (by simpa only [sub_eq_add_neg] using
      tendsto_atBot_add_const_left atTop l ((tendsto_neg_atTop_atBot : Tendsto (fun R : ℝ => -R) atTop atBot)))
  have root : rest k 0=q := by
    rw [rest,sub_zero,show k=(q/(4*Real.pi))^2 from rfl,Real.sqrt_sq (by positivity)]
    field_simp [Real.pi_ne_zero]
  have v : Tendsto (fun R : ℝ => rest k (Real.exp (l-R))) atTop (𝓝 q) := by
    rw [←root]
    exact ((by unfold rest; fun_prop : Continuous (rest k)).continuousAt.tendsto.comp p)
  have c : Tendsto (fun _ : ℝ => q) atTop (𝓝 q) := tendsto_const_nhds
  have T := ((Complex.continuous_ofReal.tendsto _).comp
    (c.div v hq.ne')).mul ((response_continuous H).continuousAt.tendsto.comp v)
  apply (by simpa only [div_self hq.ne',Complex.ofReal_one,one_mul] using T).congr'
  filter_upwards [p.eventually_lt_const hk] with R hR
  simp only [sample,if_pos hR,k]
end ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
end
