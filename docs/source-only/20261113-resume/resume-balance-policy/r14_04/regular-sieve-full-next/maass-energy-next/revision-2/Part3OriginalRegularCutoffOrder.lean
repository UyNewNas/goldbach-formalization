import ImbalancedChen.Part3OriginalRegularCompactCoordinates
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Jointly measurable cutoff Whittaker coordinate with its genuine
uniform K_0 bound. This is the domination needed for the two continuous
integrals before taking the energy limit. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCutoffOrder20261113
open Set Filter MeasureTheory Complex
open scoped Topology
open ComplexOrderKBridgeSourceOnly (complexOrderK complexOrderIntegrand complexOrderIntegrand_integrable
  complexOrderIntegrand_norm_le_real complexOrderK_real)
open RealOrderKExceptionalSourceOnly (realOrderK realOrderIntegrand)
open OriginalRegularPreKuznetsovProbe20261113 (density probe integrable_density)
open OriginalRegularPreKuznetsovSeed20261113 (seed cutoff_probe)
open OriginalRegularCutoffPlane20261113 (compact)
open OriginalCuspidalPoincareTrace20261110
open OriginalContinuousPoincarePackets20261110 (orderProbe)
open ActualUnitBandHeightSeeds20261112 (rate window_bounds window)

def coordinate (j : ℕ) (r t : ℝ) := orderProbe 1 (compact r j).toFun ((t:ℂ)*I)
def floorLimit (r t : ℝ) := 2*probe r ((t:ℂ)*I)
def cap := 2*∫ x in Ioi (0:ℝ),‖density 0 0 x‖

private theorem rate_one : rate 1=2*Real.pi := by simp [rate]

theorem coordinate_formula (j : ℕ) (r t : ℝ) :
    coordinate j r t=2*∫ x in Ioi (0:ℝ),(window j (Real.log x):ℂ)*density r ((t:ℂ)*I) x := by
  simpa only [coordinate,compact,rate_one] using cutoff_probe 1 (by norm_num) r j ((t:ℂ)*I)

theorem coordinate_limit (r t : ℝ) : Tendsto (fun j : ℕ => coordinate j r t) atTop (𝓝 (floorLimit r t)) := by
  have strip : |((t:ℂ)*I).re|<1/2 := by norm_num [Complex.mul_re]
  simpa only [rate_one,coordinate,compact,floorLimit] using
    OriginalRegularPreKuznetsovSeed20261113.cutoff_limit 1 (by norm_num) r strip

private theorem order_measurable : Measurable (fun z : ℂ×ℝ => complexOrderK z.1 z.2) := by
  let f := fun w : (ℂ×ℝ)×ℝ => complexOrderIntegrand w.1.1 w.1.2 w.2
  have h : Measurable f := by unfold f complexOrderIntegrand;fun_prop
  exact (h.stronglyMeasurable.integral_prod_right' (ν:=volume.restrict (Ioi (0:ℝ)))).measurable

theorem coordinate_measurable (j : ℕ) : Measurable (Function.uncurry (coordinate j)) := by
  let f := fun z : (ℝ×ℝ)×ℝ => (window j (Real.log z.2):ℂ)*density z.1.1 ((z.1.2:ℂ)*I) z.2
  have m : Measurable f := by
    have k1 := order_measurable.comp (show Measurable (fun z : (ℝ×ℝ)×ℝ => ((1/2:ℂ),z.2)) by fun_prop)
    have k2 := order_measurable.comp (show Measurable (fun z : (ℝ×ℝ)×ℝ => (((z.1.2:ℂ)*I),z.2)) by fun_prop)
    dsimp only [Function.comp_def] at k1 k2
    dsimp only [f,density]
    apply Measurable.mul
    · unfold window;fun_prop
    · exact ((by fun_prop : Measurable (fun z : (ℝ×ℝ)×ℝ => (z.2:ℂ)^(-((z.1.1:ℂ)*I)))).mul k1).mul k2
  have base := (m.stronglyMeasurable.integral_prod_right' (ν:=volume.restrict (Ioi (0:ℝ)))).measurable
  simpa only [Function.uncurry,coordinate_formula,f] using
    (show Measurable (fun z : ℝ×ℝ => (2:ℂ)*∫ x in Ioi (0:ℝ),f (z,x)) from measurable_const.mul base)

theorem limit_measurable : Measurable (Function.uncurry floorLimit) :=
  measurable_of_tendsto_metrizable (f:=fun j => Function.uncurry (coordinate j))
    coordinate_measurable (tendsto_pi_nhds.mpr (fun z => coordinate_limit z.1 z.2))

private theorem order_bound {x : ℝ} (hx : 0<x) (t : ℝ) :
    ‖complexOrderK ((t:ℂ)*I) x‖≤‖complexOrderK 0 x‖ := by
  have iv := complexOrderIntegrand_integrable ((t:ℂ)*I) hx (le_refl _) (by norm_num [Complex.mul_re])
  have z := complexOrderIntegrand_integrable 0 hx (le_refl _) (by norm_num)
  have eq (u : ℝ) : ‖complexOrderIntegrand 0 x u‖=realOrderIntegrand 0 x u := by
    simp only [complexOrderIntegrand,zero_mul,Complex.cosh_zero,mul_one,Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le,realOrderIntegrand,Real.cosh_zero,mul_one]
  have H := integral_mono iv.norm z.norm (fun u => (by
    simpa only [eq,Complex.mul_re,Complex.ofReal_re,Complex.I_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero]
      using complexOrderIntegrand_norm_le_real ((t:ℂ)*I) x u))
  rw [show (∫ u in Ioi 0,‖complexOrderIntegrand 0 x u‖)=realOrderK 0 x by simp_rw [eq] <;> rfl] at H
  have z' : 0≤realOrderK 0 x := integral_nonneg (fun u => by dsimp only [realOrderIntegrand];positivity)
  have E : complexOrderK 0 x=(realOrderK 0 x:ℝ) := by simpa only [Complex.ofReal_zero] using complexOrderK_real 0 x
  rw [E,Complex.norm_real,Real.norm_of_nonneg z']
  exact (norm_integral_le_integral_norm _).trans H

theorem cap_nonnegative : 0≤cap := mul_nonneg (by norm_num) (integral_nonneg (fun x => norm_nonneg _))

theorem coordinate_bound (j : ℕ) (r t : ℝ) : ‖coordinate j r t‖≤cap := by
  have h0 : IntegrableOn (density 0 0) (Ioi (0:ℝ)) := integrable_density 0 (by norm_num)
  let F := fun x : ℝ => (window j (Real.log x):ℂ)*density r ((t:ℂ)*I) x
  have me : Measurable F := by
    have k1 := order_measurable.comp (show Measurable (fun x : ℝ => ((1/2:ℂ),x)) by fun_prop)
    have k2 := order_measurable.comp (show Measurable (fun x : ℝ => (((t:ℂ)*I),x)) by fun_prop)
    dsimp only [Function.comp_def] at k1 k2
    unfold F density
    exact (show Measurable (fun x : ℝ => (window j (Real.log x):ℂ)) by unfold window;fun_prop).mul
      (((by fun_prop : Measurable (fun x : ℝ => (x:ℂ)^(-((r:ℂ)*I)))).mul k1).mul k2)
  have bound : ∀ᵐ x ∂volume.restrict (Ioi (0:ℝ)),‖F x‖≤‖density 0 0 x‖ := by
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))] with x hx
    have phase : ‖(x:ℂ)^(-((r:ℂ)*I))‖=1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx];norm_num [Complex.mul_re]
    have w := window_bounds j (Real.log x)
    have u := mul_le_mul w.2 (order_bound hx t) (norm_nonneg _) zero_le_one
    have v := mul_le_mul_of_nonneg_left u (norm_nonneg (complexOrderK (1/2:ℂ) x))
    dsimp only [F,density]
    simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg w.1,phase,one_mul,
      Complex.ofReal_zero,zero_mul,neg_zero,Complex.cpow_zero,norm_one]
    nlinarith only [v]
  have fi := h0.norm.mono' me.aestronglyMeasurable bound
  have norm := (norm_integral_le_integral_norm F).trans (integral_mono_ae fi.norm h0.norm bound)
  rw [coordinate_formula,norm_mul,Complex.norm_two]
  exact mul_le_mul_of_nonneg_left norm (by norm_num)

theorem limit_bound (r t : ℝ) : ‖floorLimit r t‖≤cap :=
  le_of_tendsto (coordinate_limit r t).norm (Eventually.of_forall (fun j => coordinate_bound j r t))

def value (j : Option ℕ) (r t : ℝ) := match j with
  | none => floorLimit r t
  | some k => coordinate k r t

theorem value_measurable (j : Option ℕ) : Measurable (Function.uncurry (value j)) := by
  cases j with
  | none => exact limit_measurable
  | some k => exact coordinate_measurable k

theorem value_bound (j : Option ℕ) (r t : ℝ) : ‖value j r t‖≤cap := by
  cases j with
  | none => exact limit_bound r t
  | some k => exact coordinate_bound k r t

end ImbalancedChen.Part3.OriginalRegularCutoffOrder20261113
end

