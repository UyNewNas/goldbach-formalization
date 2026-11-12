import ImbalancedChen.Part3ActualPositiveJRotationPair
import ImbalancedChen.Part3ActualPositiveCosineProfile
import ImbalancedChen.Part3ComplexOrderKBridge
import Mathlib.MeasureTheory.Integral.Prod

/-! The tested boundary of K at both imaginary arguments. The positive
real shift is independent of q, so its damping factor remains outside
the compact q Fourier integral. -/
namespace ImbalancedChen.Part3.ActualPositiveTestedKBoundary20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open ActualCutPlaneKOrderZeroRemovable20261026b ActualComplexArgumentKLaplace20261026b
open ActualPositiveJRotationPair20261112 ActualPositiveCosineProfile20261112
open OriginalFullModulusTestJets20261102 ComplexOrderKBridgeSourceOnly

private abbrev μ : Measure ℝ := volume.restrict (Ioi 0)

/-- Exactly the order classes supplied by the genuine principal-slit
continuation of the Laplace integral. -/
private def physicalOrder (ν : ℂ) : Prop :=
  ν=0 ∨ (0<ν.re ∧ ν.re<1) ∨ (ν.re=0 ∧ ν.im≠0)

private theorem limits {ν : ℂ} (h : physicalOrder ν) : 0≤ν.re ∧ ν.re<1 := by
  rcases h with rfl | ⟨h,l⟩ | ⟨h,_⟩
  · norm_num
  · exact ⟨h.le,l⟩
  · rw [h]; norm_num

private def shifts (ν : ℂ) (e q : ℝ) : ℂ :=
  cutPlaneKWithZero ν ((e:ℂ)+I*(q:ℂ))+cutPlaneKWithZero ν ((e:ℂ)-I*(q:ℂ))

private theorem shifts_zero (ν : ℂ) (q : ℝ) : shifts ν 0 q=rotated ν q := by
  simp only [shifts,rotated,Complex.ofReal_zero,zero_add,zero_sub,neg_mul]

private theorem shifts_cont {ν : ℂ} (h : physicalOrder ν) {e q : ℝ} (hq : 0<q) :
    ContinuousAt (fun p : ℝ×ℝ => shifts ν p.1 p.2) (e,q) := by
  have R := limits h
  have A := cutPlaneKWithZero_analyticOnNhd (ν:=ν) (show -1<ν.re by linarith [R.1]) R.2
  have l : ((e:ℂ)+I*(q:ℂ))∈slitPlane := by
    right; simpa [Complex.mul_im] using hq.ne'
  have r : ((e:ℂ)-I*(q:ℂ))∈slitPlane := by
    right; simpa [Complex.mul_im] using hq.ne'
  exact ((A _ l).continuousAt.comp (by fun_prop)).add ((A _ r).continuousAt.comp (by fun_prop))

private def D (ν : ℂ) (e u : ℝ) : ℂ :=
  (Real.exp (-e*Real.cosh u):ℂ)*Complex.cosh (ν*(u:ℂ))

private theorem damp_L1 (ν : ℂ) {e : ℝ} (he : 0<e) : Integrable (D ν e) μ := by
  have h := argumentMoment_integrable 0 ν (z:=(e:ℂ)) he
  simpa only [D,argumentMomentIntegrand,pow_zero,one_mul,← Complex.ofReal_neg,← Complex.ofReal_mul,
    ← Complex.ofReal_exp] using h

private theorem damped_row {ν : ℂ} (hν : physicalOrder ν) {e : ℝ} (he : 0<e) (q : ℝ) :
    shifts ν e q = ∫ u,(2:ℂ)*D ν e u*(Real.cos (q*Real.cosh u):ℂ) ∂μ := by
  let z := (e:ℂ)+I*(q:ℂ)
  let w := (e:ℂ)-I*(q:ℂ)
  have hz : 0<z.re := by simpa [z,Complex.mul_re] using he
  have hw : 0<w.re := by simpa [w,Complex.mul_re] using he
  have L := argumentMoment_integrable 0 ν hz
  have R := argumentMoment_integrable 0 ν hw
  simp only [argumentMomentIntegrand,pow_zero,one_mul] at L R
  change cutPlaneKWithZero ν z+cutPlaneKWithZero ν w=_
  rw [cutPlaneKWithZero_eq_actual hν hz,cutPlaneKWithZero_eq_actual hν hw,
    complexArgumentK_eq_integral,complexArgumentK_eq_integral,← integral_add L R]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    let v : ℂ := (Real.cosh u:ℂ)
    have a : -z*v=((-e*Real.cosh u:ℝ):ℂ)+(-((q*Real.cosh u:ℝ):ℂ))*I := by dsimp [z,v]; push_cast; ring
    have b : -w*v=((-e*Real.cosh u:ℝ):ℂ)+((q*Real.cosh u:ℝ):ℂ)*I := by dsimp [w,v]; push_cast; ring
    change Complex.exp (-z*v)*_+Complex.exp (-w*v)*_=_
    rw [a,b,Complex.exp_add,Complex.exp_add,D,Complex.ofReal_exp,Complex.ofReal_cos]
    linear_combination -Complex.exp (((-e*Real.cosh u:ℝ):ℂ))*Complex.cosh (ν*(u:ℂ))*Complex.two_cos (((q*Real.cosh u:ℝ):ℂ))

private theorem damped_test {ν : ℂ} (hν : physicalOrder ν) {e : ℝ} (he : 0<e)
    (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    (∫ q,shifts ν e q*testDiv ell Y q ∂μ)=2*∫ u,D ν e u*profile ell hY u ∂μ := by
  let f := testDiv ell Y
  let F := fun q u : ℝ => ((2:ℂ)*D ν e u*(Real.cos (q*Real.cosh u):ℂ))*f q
  have hf : Integrable f μ := (spectralTest_div_q_integrable ell hY).integrableOn
  have mf : StronglyMeasurable f := (spectralTest_contDiff ell Y).continuous.stronglyMeasurable.div Complex.continuous_ofReal.stronglyMeasurable
  have hd := damp_L1 ν he
  have hi : Integrable (Function.uncurry F) (μ.prod μ) := by
    apply ((hf.norm.mul_prod ((hd.norm).const_mul 2))).mono'
    · exact ((by dsimp [F,D,Function.uncurry]; fun_prop : StronglyMeasurable (fun p : ℝ×ℝ =>
          (2:ℂ)*D ν e p.2*(Real.cos (p.1*Real.cosh p.2):ℂ))).mul (mf.comp_measurable measurable_fst)).aestronglyMeasurable
    · apply ae_of_all
      intro p
      simp only [Function.uncurry_apply_pair,F,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs]
      have hc := Real.abs_cos_le_one (p.1*Real.cosh p.2)
      nlinarith only [mul_le_mul_of_nonneg_left hc (mul_nonneg
        (mul_nonneg (by norm_num : (0:ℝ)≤2) (norm_nonneg (D ν e p.2))) (norm_nonneg (f p.1)))]
  calc
    _ = ∫ q,∫ u,F q u ∂μ ∂μ := by
      simp_rw [damped_row hν he,← integral_mul_const]
      rfl
    _ = ∫ u,∫ q,F q u ∂μ ∂μ := integral_integral_swap hi
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        rw [profile_apply,cosineTest_apply,← mul_assoc,← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun q => by dsimp [F,f]; ring

private def step (n : ℕ) : ℝ := 1/((n:ℝ)+1)
private theorem step_mem (n : ℕ) : step n∈Ioc (0:ℝ) 1 :=
  ⟨by dsimp [step]; positivity,by dsimp [step]; rw [div_le_one (by positivity)]; linarith only [Nat.cast_nonneg (R:=ℝ) n]⟩

private theorem test_bound {ν : ℂ} (hν : physicalOrder ν) (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ B : ℝ, 0≤B ∧ ∀ e∈Icc (0:ℝ) 1,∀ q : ℝ,‖shifts ν e q*testDiv ell Y q‖≤B*‖testDiv ell Y q‖ := by
  let K := Icc (0:ℝ) 1 ×ˢ Icc (Y/16) (16*Y)
  have S : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have C : ContinuousOn (fun p : ℝ×ℝ => shifts ν p.1 p.2) K := fun p hp =>
    (shifts_cont hν ((div_pos hY (by norm_num)).trans_le hp.2.1)).continuousWithinAt
  obtain ⟨B,H⟩ := S.exists_bound_of_continuousOn C
  refine ⟨max B 0,le_max_right _ _,fun e he q => ?_⟩
  by_cases z : spectralTest ell Y q=0
  · simp [testDiv,z]
  · have hq := spectralTest_tsupport_strict ell hY (subset_tsupport _ z)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((H (e,q) ⟨he,hq.1.le,hq.2.le⟩).trans (le_max_left _ _)) (norm_nonneg _)

private theorem damp_bound {ν : ℂ} (hν : physicalOrder ν) {e u : ℝ} (he : 0≤e) (hu : 0≤u) :
    ‖D ν e u‖≤Real.cosh u := by
  have H := norm_complex_cosh_le_real_cosh (ν*(u:ℂ))
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at H
  have R := limits hν
  have L : Real.cosh (ν.re*u)≤Real.cosh u := Real.cosh_le_cosh.mpr (by
    rw [abs_of_nonneg (mul_nonneg R.1 hu),abs_of_nonneg hu]; simpa using mul_le_mul_of_nonneg_right R.2.le hu)
  rw [D,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg he (Real.cosh_pos u).le]))
    (H.trans L) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem boundary (ν : ℂ)
    (hν : ν=0 ∨ (0<ν.re ∧ ν.re<1) ∨ (ν.re=0 ∧ ν.im≠0))
    (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    Integrable (fun q => rotated ν q*testDiv ell Y q) μ ∧
    (∫ q,rotated ν q*testDiv ell Y q ∂μ)=
      2*∫ u,Complex.cosh (ν*(u:ℂ))*profile ell hY u ∂μ := by
  obtain ⟨B,hB,b⟩ := test_bound hν ell hY
  have hf := (spectralTest_div_q_integrable ell hY).norm.integrableOn (s:=Ioi (0:ℝ))
  have m (e : ℝ) : AEStronglyMeasurable (fun q => shifts ν e q*testDiv ell Y q) μ := by
    have sh : ContinuousOn (shifts ν e) (Ioi (0:ℝ)) := fun q h =>
      ((shifts_cont (e:=e) hν h).comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    exact (sh.aestronglyMeasurable measurableSet_Ioi).mul
      ((spectralTest_contDiff ell Y).continuous.stronglyMeasurable.div Complex.continuous_ofReal.stronglyMeasurable).aestronglyMeasurable
  have hs : Tendsto step atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have Q : Tendsto (fun n => ∫ q,shifts ν (step n) q*testDiv ell Y q ∂μ) atTop
      (𝓝 (∫ q,shifts ν 0 q*testDiv ell Y q ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun q => B*‖testDiv ell Y q‖)
    · exact fun n => m _
    · exact hf.const_mul B
    · exact fun n => ae_of_all _ (b _ ⟨(step_mem n).1.le,(step_mem n).2⟩)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact ((shifts_cont hν hq).tendsto.comp (hs.prodMk_nhds tendsto_const_nhds)).mul_const _
  have Q0 := (hf.const_mul B).mono' (m 0) (ae_of_all _ (b 0 ⟨le_rfl,zero_le_one⟩))
  have U : Tendsto (fun n => ∫ u,D ν (step n) u*profile ell hY u ∂μ) atTop
      (𝓝 (∫ u,Complex.cosh (ν*(u:ℂ))*profile ell hY u ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun u => Real.cosh u*‖profile ell hY u‖)
    · exact fun n => (by dsimp [D]; fun_prop : Continuous (D ν (step n))).stronglyMeasurable.aestronglyMeasurable.mul (profile ell hY).continuous.aestronglyMeasurable
    · exact (weighted_profile_L1 ell hY).integrableOn
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (damp_bound hν (step_mem n).1.le hu.le) (norm_nonneg _)
    · apply ae_of_all
      intro u
      have hd : Continuous (fun e : ℝ => D ν e u*profile ell hY u) := by unfold D; fun_prop
      simpa only [D,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul] using hd.continuousAt.tendsto.comp hs
  refine ⟨by simpa only [shifts_zero] using Q0,?_⟩
  simpa only [shifts_zero] using tendsto_nhds_unique Q ((U.const_mul 2).congr' (Eventually.of_forall
    fun n => (damped_test hν (step_mem n).1 ell hY).symm))

end
end ImbalancedChen.Part3.ActualPositiveTestedKBoundary20261112

