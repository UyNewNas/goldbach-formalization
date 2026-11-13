import ImbalancedChen.Part3OriginalExceptionalBandKernel
import ImbalancedChen.Part3OriginalSwitchedExceptionalTransform

/-! Lower bound for the actual fixed positive bump, uniformly all
the way down to strict complementary orders approaching zero. -/
namespace ImbalancedChen.Part3.OriginalExceptionalTestFloor20261113
noncomputable section
open Set MeasureTheory Complex Filter
open CommonSmoothCutoff
open OriginalExceptionalBandKernel20261113 (band_kernel)
open ActualPositiveJRotationPair20261112 (complementaryKernel)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)
open private kernelDensity kernel_integrable from ImbalancedChen.Part3OriginalSwitchedExceptionalTransform

theorem tested_floor {T : ℝ} (t0 : 0≤T) (t1 : T<1) :
    ∃ c Y₀ : ℝ,0<c ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ s : ℝ,0<s → s≤T →
      c*Y^s≤(exceptionalWeight (fun x => (dyadicCutoff (Y*x):ℂ)) (s/2)).re := by
  obtain ⟨c,K,δ,cp,_,dp,d1,h⟩ := band_kernel t0 t1
  refine ⟨c/2,3/δ,by positivity,(le_div_iff₀ dp).mpr (by linarith),fun Y hy s sp st => ?_⟩
  have yp : 0<Y := (by positivity : 0<3/δ).trans_le hy
  have supp : 3/Y≤δ := (div_le_iff₀ yp).mpr (by simpa only [mul_comm Y δ] using (div_le_iff₀ dp).mp hy)
  let F := fun x => (kernelDensity Y (s/2) x).re
  have I := kernel_integrable yp (by positivity : 0<s/2) (by linarith : s/2<1/2)
  have eq (x : ℝ) : F x=(complementaryKernel x (s/2)).re*dyadicCutoff (Y*x)/x := by
    simp only [F,kernelDensity,Complex.div_ofReal_re,Complex.re_mul_ofReal]
  have nn : 0≤ᵐ[volume.restrict (Ioi 0)] F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [eq]
    by_cases z : dyadicCutoff (Y*x)=0
    · simp [z]
    · have upper := (dyadicCutoff_tsupport_subset (subset_tsupport _ z)).2
      have lx : x≤δ := ((le_div_iff₀ yp).mpr (by simpa only [mul_comm x Y] using upper)).trans supp
      have flo := (h s x sp st hx lx).1
      exact div_nonneg (mul_nonneg ((mul_nonneg cp.le (Real.rpow_nonneg (by positivity) _)).trans flo)
        (dyadicCutoff_nonneg _)) hx.le
  let S := Icc (1/Y) (2/Y)
  have inc : S⊆Ioi (0:ℝ) := fun x hx => (one_div_pos.mpr yp).trans_le hx.1
  have le (x : ℝ) (hx : x∈S) : c*Y^s*(Y/2)≤F x := by
    have xp := inc hx
    have H := (h s x sp st xp (hx.2.trans ((div_le_div_of_nonneg_right (by norm_num : (2:ℝ)≤3) yp.le).trans supp))).1
    have mx : Y*x∈Icc (1:ℝ) 2 := ⟨by simpa only [mul_comm x Y] using (div_le_iff₀ yp).mp hx.1,
      by simpa only [mul_comm x Y] using (le_div_iff₀ yp).mp hx.2⟩
    have ratio : Y≤(x/2)⁻¹ := (le_inv_comm₀ yp (by positivity)).mpr (by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ yp).mpr (by nlinarith only [mx.2]))
    have pow : Y^s≤(x/2)^(-s) := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_le_rpow yp.le ratio sp.le
    have gy : c*Y^s≤(complementaryKernel x (s/2)).re := (mul_le_mul_of_nonneg_left pow cp.le).trans H
    rw [eq,dyadicCutoff_eq_one mx,mul_one,le_div_iff₀ xp]
    have pos : 0≤c*Y^s := mul_nonneg cp.le (Real.rpow_nonneg yp.le _)
    exact (by nlinarith only [mul_le_mul_of_nonneg_left mx.2 pos] : c*Y^s*(Y/2)*x≤c*Y^s).trans gy
  have R := setIntegral_ge_of_const_le_real measurableSet_Icc isCompact_Icc.measure_lt_top.ne le
    (I.re.mono_set inc)
  have U := setIntegral_mono_set I.re nn (ae_of_all _ (fun _ hx => inc hx))
  have H := R.trans U
  rw [show volume.real S=2/Y-1/Y from Real.volume_real_Icc_of_le (div_le_div_of_nonneg_right (by norm_num) yp.le)] at H
  have val : (c*Y^s*(Y/2))*(2/Y-1/Y)=(c/2)*Y^s := by field_simp [yp.ne'] <;> ring
  rw [val] at H
  simpa only [F,integral_re I,exceptionalWeight,kernelDensity] using H

end
end ImbalancedChen.Part3.OriginalExceptionalTestFloor20261113
