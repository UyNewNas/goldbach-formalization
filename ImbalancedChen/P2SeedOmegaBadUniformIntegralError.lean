import ImbalancedChen.P2SeedOmegaBadSpatialModulus

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original actual bad Gamma5 integral: a uniform analytic approximation
error and integral limit. Inputs concern sample coordinates, mesh distance
and genuine integrability; NO integral error, final coefficient, checker
pass, or desired saving is an input. The actual kernel's oscillation is
proved in the preceding module and is uniform on ALL alpha>=2.
This does not assert a concrete finite passing mesh or the20249/10^6 gain.
-/

namespace ImbalancedChen.P2SeedOmegaBadUniformIntegralError
noncomputable section
open Set MeasureTheory Filter
open scoped Interval Topology
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadGlobalCost
open P2SeedOmegaBadParameterModulus
open P2SeedOmegaBadSpatialModulus
open P2SeedOmegaBadCellSemantics (actualBadKernel)

def sampledKernel (alpha : ℝ) (sample : ℝ×ℝ → ℝ×ℝ) (u v : ℝ) : ℝ :=
  actualBadKernel alpha (sample (u,v)).1 (sample (u,v)).2
def sampledCost (alpha : ℝ) (sample : ℝ×ℝ → ℝ×ℝ) : ℝ :=
  ∫ u in corner..a2,∫ v in badLower u..a2,sampledKernel alpha sample u v

/-- These are analytic/coordinate obligations, not a certificate or an
assumed estimate for either original integral. Measurable finite cell
samples may supply integrability without being continuous at cell edges. -/
structure AdmissibleSample (alpha delta : ℝ) (sample : ℝ×ℝ → ℝ×ℝ) : Prop where
  nonnegative : 0≤delta
  coordinates : ∀ u ∈ Icc corner a2,∀ v ∈ Icc (badLower u) a2,
    sample (u,v) ∈ primeRectangle ∧ coordinateDistance (u,v) (sample (u,v))≤delta
  inner : ∀ u ∈ Icc corner a2,
    IntervalIntegrable (sampledKernel alpha sample u) volume (badLower u) a2
  outer : IntervalIntegrable
    (fun u => ∫ v in badLower u..a2,sampledKernel alpha sample u v) volume corner a2

theorem bad_support_in_primeRectangle {u v : ℝ}
    (hu : u ∈ Icc corner a2) (hv : v ∈ Icc (badLower u) a2) :
    (u,v) ∈ primeRectangle := by
  have huv : u≤v := (le_max_left u (1-2*u)).trans hv.1
  exact ⟨⟨hu.1,hu.1.trans huv⟩,⟨hu.2,hv.2⟩⟩

/-- Actual integral error, with a fixed constant independent of alpha,
the sample cardinality, any alpha upper bound, and the desired gain. -/
theorem actual_bad_cost_sample_error {alpha delta : ℝ} {sample : ℝ×ℝ → ℝ×ℝ}
    (ha : 2≤alpha) (hs : AdmissibleSample alpha delta sample) :
    |actualBadCost alpha-sampledCost alpha sample|≤4096*delta := by
  have hC : 0≤4096*delta := mul_nonneg (by norm_num) hs.nonnegative
  have huLR : corner≤a2 := by norm_num [corner,a2]
  have hpoint : ∀ u ∈ Icc corner a2,∀ v ∈ Icc (badLower u) a2,
      |actualBadKernel alpha u v-sampledKernel alpha sample u v|≤4096*delta := by
    intro u hu v hv
    have hp := hs.coordinates u hu v hv
    have h := actual_bad_kernel_spatial_modulus ha (bad_support_in_primeRectangle hu hv) hp.1
    exact h.trans (mul_le_mul_of_nonneg_left hp.2 (by norm_num))
  have hinner : ∀ u ∈ Icc corner a2,
      |(∫ v in badLower u..a2,actualBadKernel alpha u v)-
        (∫ v in badLower u..a2,sampledKernel alpha sample u v)|≤4096*delta := by
    intro u hu
    have hg := bad_fibre_geometry hu
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=badLower u) (b:=a2) (C:=4096*delta)
      (f:=fun v => actualBadKernel alpha u v-sampledKernel alpha sample u v)
      (fun v hv => by
        rw [uIoc_of_le hg.2.2.1] at hv
        simpa only [Real.norm_eq_abs] using hpoint u hu v ⟨hv.1.le,hv.2⟩)
    rw [intervalIntegral.integral_sub (actual_bad_inner_intervalIntegrable alpha hu)
      (hs.inner u hu),Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hg.2.2.1)] at h
    have hw : a2-badLower u≤1 := by
      have hl := hg.2.1
      dsimp [a2]
      linarith only [hl]
    exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw hC)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=corner) (b:=a2) (C:=4096*delta)
    (f:=fun u => (∫ v in badLower u..a2,actualBadKernel alpha u v)-
      (∫ v in badLower u..a2,sampledKernel alpha sample u v))
    (fun u hu => by
      rw [uIoc_of_le huLR] at hu
      simpa only [Real.norm_eq_abs] using hinner u ⟨hu.1.le,hu.2⟩)
  rw [intervalIntegral.integral_sub (actual_bad_outer_intervalIntegrable alpha) hs.outer,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr huLR)] at h
  have hw : a2-corner≤1 := by norm_num [a2,corner]
  exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw hC)

/-- The exact original sign and division by five preserve the paid
error budget, rather than permitting its silent deletion. -/
theorem original_normalized_bad_contribution_error {alpha delta : ℝ}
    {sample : ℝ×ℝ → ℝ×ℝ} (ha : 2≤alpha) (hs : AdmissibleSample alpha delta sample) :
    |(-actualBadCost alpha/5)-(-sampledCost alpha sample/5)|≤4096*delta/5 := by
  have h := div_le_div_of_nonneg_right (actual_bad_cost_sample_error ha hs)
    (by norm_num : (0:ℝ)≤5)
  have he : (-actualBadCost alpha/5)-(-sampledCost alpha sample/5)=
      -(actualBadCost alpha-sampledCost alpha sample)/5 := by ring
  rw [he,abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<5)]
  exact h

/-- Genuine UNIFORM integral consistency, even for unbounded varying
alpha_i. No convergence or boundedness of alpha_i is required here. -/
theorem uniform_actual_bad_sample_error_tendsto_zero {ι : Type*} {l : Filter ι}
    {A delta : ι → ℝ} {sample : ι → ℝ×ℝ → ℝ×ℝ}
    (ha : ∀ᶠ i in l,2≤A i)
    (hs : ∀ᶠ i in l,AdmissibleSample (A i) (delta i) (sample i))
    (hd : Tendsto delta l (𝓝 0)) :
    Tendsto (fun i => sampledCost (A i) (sample i)-actualBadCost (A i)) l (𝓝 0) := by
  have hmajor : Tendsto (fun i => 4096*delta i) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hd
  apply squeeze_zero_norm' ?_ hmajor
  filter_upwards [ha,hs] with i hi hsi
  simpa only [Real.norm_eq_abs,abs_sub_comm] using actual_bad_cost_sample_error hi hsi

/-- A sampled actual integral tends to the actual original integral
when both coordinate mesh error and inherited parameter error vanish. -/
theorem sampled_bad_cost_tendsto {ι : Type*} {l : Filter ι}
    {A delta : ι → ℝ} {sample : ι → ℝ×ℝ → ℝ×ℝ} {alpha : ℝ}
    (ha0 : 2≤alpha) (ha : ∀ᶠ i in l,2≤A i)
    (hs : ∀ᶠ i in l,AdmissibleSample (A i) (delta i) (sample i))
    (hd : Tendsto delta l (𝓝 0)) (hA : Tendsto A l (𝓝 alpha)) :
    Tendsto (fun i => sampledCost (A i) (sample i)) l (𝓝 (actualBadCost alpha)) := by
  have he := uniform_actual_bad_sample_error_tendsto_zero ha hs hd
  have hc := actual_bad_cost_tendsto ha0 ha hA
  simpa only [sub_add_cancel,zero_add] using he.add hc

end
end ImbalancedChen.P2SeedOmegaBadUniformIntegralError
