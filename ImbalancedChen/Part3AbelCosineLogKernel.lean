import ImbalancedChen.Part3AbelLogWeightVariation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual Abel-damped cosine integral is absolutely convergent. A sine
primitive and the proved exact derivative mass give its uniform tail
bound. Splitting at max(1,1/|delta|) yields an ABSOLUTE logarithmic bound,
uniform in positive damping. Delta zero is explicitly excluded from the
bound. No ratio-phase energy, Mellin inversion, or spectral assertion is
assumed or claimed in this module.
-/

namespace ImbalancedChen.Part3.AbelCosineLogKernel20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open AbelLogWeightVariation20261026b

def abelCosineIntegrand (ε δ t : ℝ) : ℝ := abelWeight ε t * Real.cos (δ*t)

/-- Ioi and Ici give the same Lebesgue integral; the lower endpoint is 1. -/
def abelCosineKernel (ε δ : ℝ) : ℝ := ∫ t in Ioi (1 : ℝ), abelCosineIntegrand ε δ t

def sinePrimitive (δ t : ℝ) : ℝ := Real.sin (δ*t)/δ

theorem sinePrimitive_continuous (δ : ℝ) : Continuous (sinePrimitive δ) := by
  unfold sinePrimitive
  fun_prop

theorem sinePrimitive_hasDerivAt {δ : ℝ} (hδ : δ ≠ 0) (t : ℝ) :
    HasDerivAt (sinePrimitive δ) (Real.cos (δ*t)) t := by
  convert (((hasDerivAt_id t).const_mul δ).sin).div_const δ using 1 <;>
    dsimp [sinePrimitive] <;> field_simp [hδ] <;> ring

theorem sinePrimitive_norm_le (δ t : ℝ) : ‖sinePrimitive δ t‖ ≤ 1/|δ| := by
  rw [sinePrimitive,Real.norm_eq_abs,abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)

theorem abelCosineIntegrand_integrable {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) (δ : ℝ) :
    IntegrableOn (abelCosineIntegrand ε δ) (Ioi R) := by
  apply (abelWeight_integrable hε hR).mul_bdd
    (show AEStronglyMeasurable (fun t : ℝ => Real.cos (δ*t))
      ((volume : Measure ℝ).restrict (Ioi R)) from by fun_prop)
  exact Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (δ*t))

theorem abelCosineIntegrand_norm_le_inv {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) (δ : ℝ) :
    ‖abelCosineIntegrand ε δ t‖ ≤ t⁻¹ := by
  rw [abelCosineIntegrand,norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (abelWeight_nonneg ε ht)]
  calc
    abelWeight ε t * ‖Real.cos (δ*t)‖ ≤ abelWeight ε t * 1 :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (δ*t))
        (abelWeight_nonneg ε ht)
    _ ≤ t⁻¹ := by simpa only [mul_one] using abelWeight_le_inv hε ht

theorem abel_sine_boundary_tendsto_zero {ε : ℝ} (hε : 0 ≤ ε) (δ : ℝ) :
    Tendsto (fun t => abelWeight ε t*sinePrimitive δ t) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) ?_
    (show Tendsto (fun t => abelWeight ε t*(1/|δ|)) atTop (𝓝 0) from by
      simpa only [zero_mul] using (abelWeight_tendsto_zero hε).mul_const (1/|δ|))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (abelWeight_nonneg ε ht)]
  exact mul_le_mul_of_nonneg_left (sinePrimitive_norm_le δ t) (abelWeight_nonneg ε ht)

/-- The oscillatory tail is bounded by twice its actual endpoint weight,
divided by the nonzero frequency. The variation budget is derived. -/
theorem abelCosine_tail_weight_bound {ε R δ : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hδ : δ ≠ 0) :
    ‖∫ t in Ioi R, abelCosineIntegrand ε δ t‖ ≤ 2*(abelWeight ε R*(1/|δ|)) := by
  have hi := abelCosineIntegrand_integrable hε hR δ
  have hj : IntegrableOn (fun t => (-abelLoss ε t)*sinePrimitive δ t) (Ioi R) :=
    (abelLoss_integrable hε hR).neg.mul_bdd
      (sinePrimitive_continuous δ).aestronglyMeasurable
      (Eventually.of_forall (sinePrimitive_norm_le δ))
  have hz : Tendsto (fun t => abelWeight ε t*sinePrimitive δ t) (𝓝[>] R)
      (𝓝 (abelWeight ε R*sinePrimitive δ R)) :=
    ((abelWeight_continuousAt ε hR.ne').mul
      (sinePrimitive_continuous δ).continuousAt).mono_left nhdsWithin_le_nhds
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := abelWeight ε) (u' := fun t => -abelLoss ε t)
    (v := sinePrimitive δ) (v' := fun t => Real.cos (δ*t))
    (a := R) (a' := abelWeight ε R*sinePrimitive δ R) (b' := (0 : ℝ))
    (fun t ht => abelWeight_hasDerivAt ε (hR.trans ht).ne')
    (fun t _ => sinePrimitive_hasDerivAt hδ t) hi hj hz
    (abel_sine_boundary_tendsto_zero hε.le δ)
  have hJ : ‖∫ t in Ioi R, (-abelLoss ε t)*sinePrimitive δ t‖ ≤
      abelWeight ε R*(1/|δ|) := by
    calc
      _ ≤ ∫ t in Ioi R, abelLoss ε t*(1/|δ|) := by
        apply norm_integral_le_of_norm_le ((abelLoss_integrable hε hR).mul_const (1/|δ|))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [norm_mul,norm_neg,Real.norm_eq_abs,
          abs_of_nonneg (abelLoss_nonneg hε.le (hR.trans ht))]
        exact mul_le_mul_of_nonneg_left (sinePrimitive_norm_le δ t)
          (abelLoss_nonneg hε.le (hR.trans ht))
      _ = _ := by rw [integral_mul_const,integral_abelLoss hε hR]
  have hB : ‖abelWeight ε R*sinePrimitive δ R‖ ≤ abelWeight ε R*(1/|δ|) := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (abelWeight_nonneg ε hR)]
    exact mul_le_mul_of_nonneg_left (sinePrimitive_norm_le δ R) (abelWeight_nonneg ε hR)
  change (∫ t in Ioi R, abelCosineIntegrand ε δ t) = _ at hparts
  rw [hparts,zero_sub]
  calc
    _ ≤ ‖-(abelWeight ε R*sinePrimitive δ R)‖+
        ‖∫ t in Ioi R, (-abelLoss ε t)*sinePrimitive δ t‖ := norm_sub_le _ _
    _ ≤ 2*(abelWeight ε R*(1/|δ|)) := by rw [norm_neg]; linarith

theorem abelCosine_tail_bound {ε R δ : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hδ : δ ≠ 0) :
    ‖∫ t in Ioi R, abelCosineIntegrand ε δ t‖ ≤ 2/(|δ|*R) := by
  calc
    _ ≤ 2*(abelWeight ε R*(1/|δ|)) := abelCosine_tail_weight_bound hε hR hδ
    _ ≤ 2*(R⁻¹*(1/|δ|)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (abelWeight_le_inv hε.le hR) (by positivity)) (by norm_num)
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem abelCosine_low_interval_bound {ε R : ℝ} (hε : 0 ≤ ε) (hR : 1 ≤ R) (δ : ℝ) :
    ‖∫ t in (1 : ℝ)..R, abelCosineIntegrand ε δ t‖ ≤ Real.log R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 R :=
    ContinuousOn.intervalIntegrable_of_Icc hR
      (continuousOn_id.inv₀ (fun t ht => ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  have hb := intervalIntegral.norm_integral_le_of_norm_le hR
    (Eventually.of_forall (fun t ht => abelCosineIntegrand_norm_le_inv hε
      (zero_lt_one.trans ht.1) δ)) hi
  simpa only [integral_inv_of_pos zero_lt_one hR0,div_one] using hb

/-- Uniform absolute logarithmic bound for the actual damped kernel.
There is no assertion at delta zero. In particular no log(0) convention
is used to hide the nonuniform resonance. -/
theorem abelCosineKernel_log_bound {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ≠ 0) :
    |abelCosineKernel ε δ| ≤ 2+Real.log (max 1 (1/|δ|)) := by
  let R : ℝ := max 1 (1/|δ|)
  have hR : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hd : 0 < |δ| := abs_pos.mpr hδ
  have hprod : 1 ≤ |δ|*R := by
    have h := mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) (1/|δ|)) hd.le
    simpa only [mul_one_div_cancel hd.ne'] using h
  have ht : ‖∫ t in Ioi R, abelCosineIntegrand ε δ t‖ ≤ 2 := by
    apply (abelCosine_tail_bound hε hR0 hδ).trans
    apply (div_le_iff₀ (mul_pos hd hR0)).mpr
    nlinarith
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (abelCosineIntegrand_integrable hε zero_lt_one δ)
    (abelCosineIntegrand_integrable hε hR0 δ)
  have hn : ‖abelCosineKernel ε δ‖ ≤ Real.log R+2 := by
    rw [abelCosineKernel,← hsplit]
    exact (norm_add_le _ _).trans (add_le_add (abelCosine_low_interval_bound hε.le hR δ) ht)
  simpa only [Real.norm_eq_abs,add_comm] using hn

end
end ImbalancedChen.Part3.AbelCosineLogKernel20261026b
