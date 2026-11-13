import ImbalancedChen.Part3OriginalExceptionalHeightWindow
import ImbalancedChen.Part3ComplexOrderKQCalculus

/-! A lower bound for the actual order probe, uniform down to order zero.
The two integrations are over ordinary Lebesgue measure. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalExceptionalProbeFloor20261113
open Set Filter MeasureTheory Complex
open RealOrderKExceptionalSourceOnly ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus
open OriginalContinuousPoincarePackets20261110 OriginalExceptionalHeightWindow20261112

def kernelConstant : ℝ := Real.exp (-(4*Real.pi*Real.exp 1))/2
def probeConstant : ℝ := kernelConstant/2

theorem kernelConstant_pos : 0 < kernelConstant := half_pos (Real.exp_pos _)
theorem probeConstant_pos : 0 < probeConstant := half_pos kernelConstant_pos

private theorem all_order_integrable (α : ℝ) {q : ℝ} (hq : 0<q) :
    IntegrableOn (realOrderIntegrand α q) (Ioi 0) := by
  have e (s : ℝ) : (qMomentIntegrand 0 (α:ℂ) q s).re=realOrderIntegrand α q s := by
    simp only [qMomentIntegrand,pow_zero,one_mul,← Complex.ofReal_mul,
      ← Complex.ofReal_cosh,← Complex.ofReal_mul,Complex.ofReal_re,realOrderIntegrand]
  exact ((qMomentIntegrand_integrable 0 (α:ℂ) hq).re).congr (ae_of_all _ e)

private theorem realK_nonneg (α q : ℝ) : 0 ≤ realOrderK α q :=
  integral_nonneg (fun s => mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)

private theorem unit_interval_mass (a : ℝ) :
    (volume : Measure ℝ).real (Ioc a (a+1))=1 := by
  rw [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (by linarith)]
  ring

/-- Restrict the positive Macdonald integral to log H < s ≤ log H + 1. -/
theorem macdonald_floor {H α q : ℝ} (hH : 1≤H) (hα : 0≤α) (hq : 0<q)
    (hqH : q*H≤4*Real.pi) : kernelConstant * H^α ≤ realOrderK α q := by
  let a := Real.log H
  let S := Ioc a (a+1)
  have hp : 0<H := zero_lt_one.trans_le hH
  have ha : 0≤a := Real.log_nonneg hH
  have sub : S ⊆ Ioi (0:ℝ) := fun s hs => ha.trans_lt hs.1
  have hi := all_order_integrable α hq
  have point (s : ℝ) (hs : s∈S) : kernelConstant*H^α ≤ realOrderIntegrand α q s := by
    have hc : Real.cosh s ≤ Real.exp s := by
      simpa using (cosh_le_exp_abs_mul 1 (ha.trans hs.1.le))
    have es : Real.exp s ≤ H*Real.exp 1 := by
      simpa only [a,Real.exp_add,Real.exp_log hp] using Real.exp_le_exp.mpr hs.2
    have damp : Real.exp (-(4*Real.pi*Real.exp 1)) ≤ Real.exp (-q*Real.cosh s) := by
      apply Real.exp_le_exp.mpr
      have b : q*Real.cosh s ≤ 4*Real.pi*Real.exp 1 := calc
        _ ≤ q*(H*Real.exp 1) := mul_le_mul_of_nonneg_left (hc.trans es) hq.le
        _ = (q*H)*Real.exp 1 := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hqH (Real.exp_pos 1).le
      linarith
    have grow : H^α/2 ≤ Real.cosh (α*s) := by
      rw [Real.rpow_def_of_pos hp,Real.cosh_eq]
      have e := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.1.le hα)
      dsimp only [a] at e
      rw [mul_comm α (Real.log H)] at e
      linarith [Real.exp_pos (-(α*s))]
    calc
      _ = Real.exp (-(4*Real.pi*Real.exp 1))*(H^α/2) := by unfold kernelConstant; ring
      _ ≤ _ := mul_le_mul damp grow (half_nonneg (Real.rpow_nonneg hp.le _)) (Real.exp_pos _).le
  have floor := setIntegral_ge_of_const_le_real (μ:=volume) (s:=S) measurableSet_Ioc
    (by simp [S,Real.volume_Ioc]) point (hi.mono_set sub)
  rw [show (volume : Measure ℝ).real S=1 from unit_interval_mass a,mul_one] at floor
  exact floor.trans (setIntegral_mono_set hi
    (ae_of_all _ (fun s => mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le))
    (Eventually.of_forall sub))

def density (H α u : ℝ) : ℝ := 2*(bump u/u)*realOrderK α (2*Real.pi*(u/H))

private theorem density_nonneg {u : ℝ} (hu : 0<u) (H α : ℝ) : 0≤density H α u :=
  mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (bump_bounds u).1 hu.le)) (realK_nonneg _ _)

private theorem density_integrable {H : ℝ} (hH : 0<H) (α : ℝ) : Integrable (density H α) := by
  have sub : Function.support (density H α) ⊆ Icc (1:ℝ) 2 := by
    intro u hu
    have h := bump_inside (show bump u≠0 from fun e => hu (by simp [density,e]))
    exact ⟨h.1.le,h.2.le⟩
  apply (integrableOn_iff_integrable_of_support_subset sub).mp
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  intro u hu
  have hu' : 0<u := zero_lt_one.trans_le hu.1
  have hq : 0<2*Real.pi*(u/H) := by positivity
  have hk : ContinuousAt (fun v : ℝ => realOrderK α (2*Real.pi*(v/H))) u := by
    have z := Complex.continuous_re.continuousAt.comp
      ((complexOrderK_hasDerivAt_q (α:ℂ) hq).continuousAt.comp
        (by fun_prop : ContinuousAt (fun v : ℝ => 2*Real.pi*(v/H)) u))
    simpa only [Function.comp_def,complexOrderK_real,Complex.ofReal_re] using z
  exact ((continuousAt_const.mul (bump_smooth.continuous.continuousAt.div continuousAt_id hu'.ne')).mul
    hk).continuousWithinAt

/-- The physical Fourier convention supplies exactly twice the du/u integral. -/
theorem original_probe_integral {H : ℝ} (hH : 0<H) (α : ℝ) :
    orderProbe 1 (seed H).toFun (α:ℂ) =
      ((∫ u in Ioi (0:ℝ),density H α u):ℝ) := by
  let f := fun u : ℝ => (density H α u : ℂ)
  have changeVariable := integral_comp_mul_left_Ioi' f 0 hH
  rw [mul_zero,← integral_smul] at changeVariable
  rw [← integral_complex_ofReal,← changeVariable]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have sq := Real.sq_sqrt hy.le
  have scalar : (y⁻¹)^2*(Real.sqrt y*bump (H*y))*(2*Real.sqrt y)=
      H*(2*(bump (H*y)/(H*y))) := by
    calc
      _ = (2*bump (H*y))*(Real.sqrt y)^2/y^2 := by field_simp [hy.ne'] <;> ring
      _ = _ := by rw [sq]; field_simp [hH.ne',hy.ne'] <;> ring
  have arg : H*y/H=y := by field_simp [hH.ne']
  change ((y⁻¹)^2:ℝ) • (star ((seed H).toFun y)*orderRadial 1 (α:ℂ) y)=H • f (H*y)
  rw [seed_pos_height H hy]
  simp only [orderRadial,f,density,Int.cast_one,abs_one,mul_one,
    arg,complexOrderK_real,Complex.star_def,Complex.conj_ofReal,
    Complex.real_smul]
  push_cast
  have eqc := congrArg Complex.ofReal scalar
  push_cast at eqc
  linear_combination (realOrderK α (2*Real.pi*y):ℂ)*eqc

/-- Absolute constant, independent of level, sign, spectral multiplicity and order. -/
theorem original_probe_floor {H α : ℝ} (hH : 1≤H) (hα : 0≤α) :
    probeConstant*H^α ≤ ‖orderProbe 1 (seed H).toFun (α:ℂ)‖ := by
  have hp : 0<H := zero_lt_one.trans_le hH
  let U := Ioc (5/4:ℝ) (7/4)
  have sub : U⊆Ioi (0:ℝ) := fun u hu => (by norm_num : (0:ℝ)<5/4).trans hu.1
  have point (u : ℝ) (hu : u∈U) : kernelConstant*H^α ≤ density H α u := by
    have up := sub hu
    have hq : (2*Real.pi*(u/H))*H≤4*Real.pi := by
      rw [mul_assoc,div_mul_cancel₀ _ hp.ne']
      nlinarith only [mul_le_mul_of_nonneg_left hu.2 Real.pi_pos.le,Real.pi_pos]
    have f := macdonald_floor hH hα (by positivity : 0<2*Real.pi*(u/H)) hq
    rw [density,bump_plateau hu.1.le hu.2]
    exact f.trans (le_mul_of_one_le_left (realK_nonneg _ _) (by
      rw [← mul_div_assoc,mul_one,le_div_iff₀ up]; linarith [hu.2]))
  have hi := density_integrable hp α
  have floor := setIntegral_ge_of_const_le_real (μ:=volume) (s:=U) measurableSet_Ioc
    (by simp [U,Real.volume_Ioc]) point hi.integrableOn
  have mass : (volume : Measure ℝ).real U=1/2 := by
    norm_num [U,Measure.real,Real.volume_Ioc]
  rw [mass] at floor
  have nn := (ae_restrict_mem (μ:=volume) measurableSet_Ioi).mono
    (fun y hy => density_nonneg hy H α)
  rw [original_probe_integral hp α,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg_of_ae nn)]
  calc
    _ = (kernelConstant*H^α)*(1/2) := by unfold probeConstant; ring
    _ ≤ _ := floor.trans (setIntegral_mono_set hi.integrableOn nn (Eventually.of_forall sub))

end ImbalancedChen.Part3.OriginalExceptionalProbeFloor20261113
end
