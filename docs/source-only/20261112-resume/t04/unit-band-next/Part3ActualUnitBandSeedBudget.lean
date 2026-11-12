import ImbalancedChen.Part3ActualUnitBandHeightSeeds
import ImbalancedChen.Part3ComplexOrderKMellinReduction
import Batteries.Tactic.OpenPrivate

/-! Both moments of the fixed positive spatial envelope. -/
namespace ImbalancedChen.Part3.ActualUnitBandSeedBudget20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology Distributions ContDiff MatrixGroups UpperHalfPlane
open ActualUnitBandHeightSeeds20261112 ActualSignedPoincareEnvelope20261112
open ActualHorocycleSynthesisBound20261112 ActualLogHorocycleAdjoint20261112
open ComplexOrderKBridgeSourceOnly ComplexOrderKMellinReduction20261025a
open ActualComplexTwoKMellin20261025a ActualIncompleteEisensteinTransform20261110
open ActualResidualVolumeNormalization20261110 AngularFourierUnitary20261026b
open private exp_substitution from ImbalancedChen.Part3ActualIncompleteMellinFactors

private theorem exp_mass (F : ℝ → ℝ) (h : IntegrableOn F (Ioi 0)) :
    Integrable (fun u : ℝ => Real.exp u*F (Real.exp u)) := by
  have J := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) (fun _ _ _ _ E => Real.exp_injective E) F
  simpa only [image_univ,Real.range_exp,integrableOn_univ,abs_of_pos (Real.exp_pos _),smul_eq_mul] using
    J.mp (by simpa only [image_univ,Real.range_exp] using h)

theorem carrier_L2 : MemLp carrier 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm smooth_carrier.continuous.aestronglyMeasurable).mpr
  have H := (actualTwoKMellinDensity_integrable (nu := 0) (mu := 0) (s := 2) (by norm_num)).norm
  have h : IntegrableOn (fun q : ℝ => q*‖complexOrderK 0 q‖^2) (Ioi 0) := H.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    simp only [actualTwoKMellinDensity,show (2:ℂ)-1=1 by norm_num,Complex.cpow_one,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg hq.le]
    ring)
  apply (exp_mass _ h).congr
  exact ae_of_all _ (fun u => by simp [carrier,norm_mul,Real.norm_of_nonneg (Real.exp_pos u).le]; ring)

theorem carrier_L1_moment : Integrable (fun u : ℝ => Real.exp (-u/2)*‖carrier u‖) := by
  have H := (complexOrderK_mellin_integrable (ν := 0) (s := 1/2) (by norm_num)).norm
  have h : IntegrableOn (fun q : ℝ => q^(-(1/2:ℝ))*‖complexOrderK 0 q‖) (Ioi 0) := H.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hq]
    norm_num)
  apply (exp_mass _ h).congr
  exact ae_of_all _ (fun u => by
    simp only [carrier,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos u).le,← Real.exp_mul]
    rw [show u*(-(1/2:ℝ))= -u/2 by ring]
    ring)

private theorem translated_L1 (C : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-u/2)*‖carrier (u+Real.log C)‖) := by
  have J := (measurePreserving_add_right (volume : Measure ℝ) (Real.log C)).integrable_comp_of_integrable carrier_L1_moment
  apply (J.const_mul (Real.exp (Real.log C/2))).congr
  apply ae_of_all
  intro u
  change Real.exp _*(Real.exp _*‖carrier _‖)=_
  rw [← mul_assoc,← Real.exp_add,show Real.log C/2+ -(u+Real.log C)/2= -u/2 by ring]

private theorem moment_from_log (f : LogTest) :
    moment (fromLog f).toHeightSeed 0=∫ u : ℝ,(Real.exp (-u/2) : ℂ)*star (f u) := by
  rw [moment,exp_substitution]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  have E : Real.exp u*((Real.exp u)⁻¹)^2*Real.exp (u/2)=Real.exp (-u/2) := by
    rw [← Real.exp_neg,sq,← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  have Ec := congrArg (fun x : ℝ => (x:ℂ)) E
  push_cast at Ec
  simp only [fromLog_exp,Complex.real_smul,Complex.cpow_zero,mul_one,star_mul',Complex.star_def,
    Complex.conj_ofReal,Complex.ofReal_pow,Complex.ofReal_inv]
  linear_combination Ec*conj (f u)

/-- The bound is independent of the spectral modulation, both cutoff
endpoints and the normalized observation frame. -/
theorem uniform_seed_budget (N : ℕ) [NeZero N] (m : ℤ) :
    ∃ B : ℝ,0≤B ∧ ∀ (g : SL(2,ℤ)) (T : ℝ) (k : ℕ),
      let f := seed (rate m) T k
      ‖framedVector N g m f.toFun f.continuous f.compact f.positive‖^2≤B := by
  let C := rate m
  let L := fun u : ℝ => carrier (u+Real.log C)
  have hL : MemLp L 2 volume := carrier_L2.comp_measurePreserving (measurePreserving_add_right volume (Real.log C))
  let M := ∫ u : ℝ,Real.exp (-u/2)*‖L u‖
  have hM : 0≤M := integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  refine ⟨2*‖hL.toLp L‖^2+|actualVolume N|⁻¹*M^2,by positivity,?_⟩
  intro g T k
  let f := seed C T k
  let η := seed C 0 k
  have H := signed_envelope_norm_sq N g m f.toFun f.continuous f.compact f.positive η
    (seed_real C k) (fun y => (seed_norm C T k y).le)
  have test_le (u : ℝ) : ‖logSeed C 0 k u‖≤‖L u‖ := by
    change ‖(window k (u+Real.log C):ℂ)*L u*modulation 0 (u+Real.log C)‖≤_
    rw [norm_mul,norm_mul,modulation_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg (window_bounds _ _).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (window_bounds _ _).2
  have hnorm : ‖logVector η‖≤‖hL.toLp L‖ := by
    change ‖logVector (fromLog _)‖≤_
    rw [logVector_fromLog]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [test_ae (logSeed C 0 k),hL.coeFn_toLp] with u hu hv
    rw [hu,hv]
    exact test_le u
  have hmom : ‖moment η.toHeightSeed 0‖≤M := by
    change ‖moment (fromLog _).toHeightSeed 0‖≤M
    rw [moment_from_log]
    have a : ∀ u : ℝ, ‖(Real.exp (-u/2):ℂ)*star (logSeed C 0 k u)‖≤Real.exp (-u/2)*‖L u‖ := fun u => by
      rw [norm_mul,norm_star,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (test_le u) (Real.exp_pos _).le
    have I : Integrable (fun u : ℝ => (Real.exp (-u/2):ℂ)*star (logSeed C 0 k u)) :=
      (translated_L1 C).mono' (by
        exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul (logSeed C 0 k).continuous.star).aestronglyMeasurable)
        (ae_of_all _ a)
    exact (norm_integral_le_integral_norm _).trans (integral_mono I.norm (translated_L1 C) a)
  exact H.trans (add_le_add (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm) (by norm_num))
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hM).mpr hmom) (inv_nonneg.mpr (abs_nonneg _))))

end
end ImbalancedChen.Part3.ActualUnitBandSeedBudget20261112
