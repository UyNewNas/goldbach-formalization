import ImbalancedChen.Part3ComplexOrderKSmallArgument
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! SOURCE ONLY / UNCOMPILED. Actual regularized Gamma kernel on
0 < Re nu < 1, including absolute convergence and its exact integral. -/

namespace ImbalancedChen.Part3.RegularizedNegativeGamma20261025a
noncomputable section
open Set MeasureTheory Filter intervalIntegral
open scoped Topology

def regularizedKernel (ν : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-u) : ℂ) - 1) * (u : ℂ) ^ (-ν - 1)

def boundaryProduct (ν : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-u) : ℂ) - 1) * (u : ℂ) ^ (-ν)

theorem exp_defect_bounds {u : ℝ} (hu : 0 ≤ u) :
    |Real.exp (-u) - 1| ≤ u ∧ |Real.exp (-u) - 1| ≤ 1 := by
  have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  rw [abs_of_nonpos (sub_nonpos.mpr he)]
  constructor
  · linarith only [Real.add_one_le_exp (-u)]
  · linarith only [Real.exp_pos (-u)]

theorem regularizedKernel_norm_bounds (ν : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖regularizedKernel ν u‖ ≤ u ^ (-ν.re) ∧
      ‖regularizedKernel ν u‖ ≤ u ^ (-ν.re - 1) := by
  have he := exp_defect_bounds hu.le
  have hn : ‖regularizedKernel ν u‖ =
      |Real.exp (-u) - 1| * u ^ (-ν.re - 1) := by
    simp only [regularizedKernel, norm_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.neg_re,
      Complex.one_re, Complex.ofReal_re]
  have hp : u * u ^ (-ν.re - 1) = u ^ (-ν.re) := by
    calc
      _ = u ^ (1 : ℝ) * u ^ (-ν.re - 1) := by rw [Real.rpow_one]
      _ = u ^ ((1 : ℝ) + (-ν.re - 1)) := (Real.rpow_add hu _ _).symm
      _ = _ := by congr 1; ring
  rw [hn]
  exact ⟨by simpa only [hp] using mul_le_mul_of_nonneg_right he.1 (Real.rpow_nonneg hu.le _),
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right he.2 (Real.rpow_nonneg hu.le _)⟩

theorem regularizedKernel_continuousOn (ν : ℂ) :
    ContinuousOn (regularizedKernel ν) (Ioi 0) := by
  apply ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).continuousOn.sub
    continuousOn_const).mul
  apply continuousOn_of_forall_continuousAt
  intro u hu
  exact (Complex.continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hu)).comp
    Complex.continuous_ofReal.continuousAt

theorem regularizedKernel_integrable {ν : ℂ} (hν : 0 < ν.re) (hν1 : ν.re < 1) :
    IntegrableOn (regularizedKernel ν) (Ioi 0) := by
  have hc := (regularizedKernel_continuousOn ν).aestronglyMeasurable measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · have hp : IntegrableOn (fun u : ℝ => u ^ (-ν.re)) (Ioc 0 1) :=
      (intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < -ν.re)).integrableOn_Ioc
    apply hp.mono' (hc.mono_set Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (regularizedKernel_norm_bounds ν hu.1).1
  · have hp : IntegrableOn (fun u : ℝ => u ^ (-ν.re - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -ν.re - 1 < -1) (by norm_num)
    apply hp.mono' (hc.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (regularizedKernel_norm_bounds ν (zero_lt_one.trans hu)).2

theorem boundaryProduct_norm_bounds (ν : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖boundaryProduct ν u‖ ≤ u ^ (1 - ν.re) ∧
      ‖boundaryProduct ν u‖ ≤ u ^ (-ν.re) := by
  have he := exp_defect_bounds hu.le
  have hn : ‖boundaryProduct ν u‖ = |Real.exp (-u) - 1| * u ^ (-ν.re) := by
    simp only [boundaryProduct, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu,
      Complex.neg_re, Complex.ofReal_re]
  have hp : u * u ^ (-ν.re) = u ^ (1 - ν.re) := by
    rw [← Real.rpow_one u, ← Real.rpow_add hu]
    congr 1
    ring
  rw [hn]
  exact ⟨by simpa only [hp] using mul_le_mul_of_nonneg_right he.1 (Real.rpow_nonneg hu.le _),
    by simpa only [one_mul] using mul_le_mul_of_nonneg_right he.2 (Real.rpow_nonneg hu.le _)⟩

theorem boundaryProduct_tendsto_zero {ν : ℂ} (hν1 : ν.re < 1) :
    Tendsto (boundaryProduct ν) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hp : Tendsto (fun u : ℝ => u ^ (1 - ν.re)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const (by linarith : 0 ≤ 1 - ν.re)).tendsto 0
    simpa only [Real.zero_rpow (by linarith : 1 - ν.re ≠ 0)] using
      hc.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun u => norm_nonneg _)) ?_ hp
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (boundaryProduct_norm_bounds ν hu).1

theorem boundaryProduct_tendsto_atTop {ν : ℂ} (hν : 0 < ν.re) :
    Tendsto (boundaryProduct ν) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun u => norm_nonneg _)) ?_
    (Real.tendsto_rpow_neg_atTop hν)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  exact (boundaryProduct_norm_bounds ν hu).2

/-- Integration by parts computes the actual regularized Gamma integral. -/
theorem regularizedKernel_integral {ν : ℂ} (hν : 0 < ν.re) (hν1 : ν.re < 1) :
    (∫ u in Ioi (0 : ℝ), regularizedKernel ν u) = Complex.Gamma (-ν) := by
  have hne : ν ≠ 0 := by intro h; simp [h] at hν
  have hneg : -ν ≠ 0 := neg_ne_zero.mpr hne
  let f : ℝ → ℂ := fun u => (Real.exp (-u) : ℂ) - 1
  let f' : ℝ → ℂ := fun u => -(Real.exp (-u) : ℂ)
  let g : ℝ → ℂ := fun u => (u : ℂ) ^ (-ν)
  let g' : ℝ → ℂ := fun u => (-ν) * (u : ℂ) ^ (-ν - 1)
  have hf : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt f (f' u) u := by
    intro u _
    simpa only [f, f', Complex.ofReal_neg] using
      (((hasDerivAt_neg u).exp).ofReal_comp.sub_const (1 : ℂ))
  have hg : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt g (g' u) u := by
    intro u hu
    exact Complex.hasDerivAt_ofReal_cpow_const hu.ne' hneg
  have hreg := regularizedKernel_integrable hν hν1
  have hgamma : IntegrableOn (fun u : ℝ =>
      (Real.exp (-u) : ℂ) * (u : ℂ) ^ (-ν)) (Ioi 0) := by
    have hh := Complex.GammaIntegral_convergent
      (show 0 < ((1 : ℂ) - ν).re by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have he : (1 : ℂ) - ν - 1 = -ν := by ring
    simpa only [he] using hh
  have hfg : IntegrableOn (f * g') (Ioi 0) := by
    convert hreg.const_mul (-ν) using 1
    funext u
    dsimp [f, g', regularizedKernel]
    ring
  have hfg2 : IntegrableOn (f' * g) (Ioi 0) := by
    simpa only [f', g, Pi.mul_def, neg_mul] using hgamma.neg
  have hzero : Tendsto (f * g) (𝓝[>] (0 : ℝ)) (𝓝 0) := boundaryProduct_tendsto_zero hν1
  have hinfty : Tendsto (f * g) atTop (𝓝 0) := boundaryProduct_tendsto_atTop hν
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hf hg hfg hfg2 hzero hinfty
  have hleft : (∫ u in Ioi (0 : ℝ), f u * g' u) =
      (-ν) * ∫ u in Ioi (0 : ℝ), regularizedKernel ν u := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun u => by dsimp [f, g', regularizedKernel]; ring)
  have hright : (∫ u in Ioi (0 : ℝ), f' u * g u) = -Complex.Gamma (1 - ν) := by
    rw [Complex.Gamma_eq_integral
      (show 0 < ((1 : ℂ) - ν).re by simp only [Complex.sub_re, Complex.one_re]; linarith)]
    unfold Complex.GammaIntegral
    rw [← integral_neg]
    apply integral_congr_ae
    have he : (1 : ℂ) - ν - 1 = -ν := by ring
    exact Eventually.of_forall (fun u => by simp only [f', g, he, neg_mul])
  rw [hleft, hright] at hibp
  have hrec := Complex.Gamma_add_one (-ν) hneg
  have hexp : -ν + 1 = (1 : ℂ) - ν := by ring
  rw [hexp] at hrec
  apply (mul_left_cancel₀ hneg)
  rw [← hrec]
  simpa only [sub_zero, zero_sub, neg_neg] using hibp

def dampedRegularizedKernel (ν : ℂ) (q u : ℝ) : ℂ :=
  (Real.exp (-(q ^ 2 / (4 * u))) : ℂ) * regularizedKernel ν u

theorem dampedRegularizedKernel_norm_le (ν : ℂ) (q : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖dampedRegularizedKernel ν q u‖ ≤ ‖regularizedKernel ν u‖ := by
  have hd : 0 ≤ q ^ 2 / (4 * u) := div_nonneg (sq_nonneg q) (by positivity)
  have he : Real.exp (-(q ^ 2 / (4 * u))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd)
  rw [dampedRegularizedKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg _)

theorem dampedRegularizedKernel_integrable {ν : ℂ}
    (hν : 0 < ν.re) (hν1 : ν.re < 1) (q : ℝ) :
    IntegrableOn (dampedRegularizedKernel ν q) (Ioi 0) := by
  have hg := regularizedKernel_integrable hν hν1
  have hm : Measurable (fun u : ℝ => (Real.exp (-(q ^ 2 / (4 * u))) : ℂ)) := by fun_prop
  apply hg.norm.mono' (hm.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact dampedRegularizedKernel_norm_le ν q hu

/-- The actual inverted defect converges to its negative-order Gamma value. -/
theorem dampedRegularizedKernel_integral_tendsto {ν : ℂ}
    (hν : 0 < ν.re) (hν1 : ν.re < 1) :
    Tendsto (fun q : ℝ => ∫ u in Ioi (0 : ℝ), dampedRegularizedKernel ν q u)
      (𝓝 (0 : ℝ)) (𝓝 (Complex.Gamma (-ν))) := by
  rw [← regularizedKernel_integral hν hν1]
  have hg := regularizedKernel_integrable hν hν1
  apply tendsto_integral_filter_of_dominated_convergence (fun u => ‖regularizedKernel ν u‖)
  · exact Eventually.of_forall (fun q => (dampedRegularizedKernel_integrable hν hν1 q).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro q
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact dampedRegularizedKernel_norm_le ν q hu
  · exact hg.norm
  · apply Eventually.of_forall
    intro u
    have hc : Continuous (fun q : ℝ => dampedRegularizedKernel ν q u) := by
      unfold dampedRegularizedKernel
      fun_prop
    have ht : Tendsto (fun q : ℝ => dampedRegularizedKernel ν q u)
        (𝓝 (0 : ℝ)) (𝓝 (dampedRegularizedKernel ν 0 u)) := hc.continuousAt
    simpa only [dampedRegularizedKernel, zero_pow (by decide : 2 ≠ 0), zero_div,
      neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using ht

end
end ImbalancedChen.Part3.RegularizedNegativeGamma20261025a
