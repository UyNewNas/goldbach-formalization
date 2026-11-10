import ImbalancedChen.Part3ActualIncompleteEisensteinGram
import ImbalancedChen.Part3FiniteMeasureCauchyParameterIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Entire Mellin factors in the physical Gram. The exponent 1-s in
the scattering term and the dy/y² Jacobian fix the conjugation, tilt
and ordinary pole contribution. -/
namespace ImbalancedChen.Part3.ActualIncompleteMellinFactors20261110

noncomputable section
open Set Filter Topology MeasureTheory Complex UpperHalfPlane Metric
open scoped BigOperators UpperHalfPlane MatrixGroups FourierTransform SchwartzMap
open ActualInfinityCuspAnnihilator20261026b SmoothZeroHeightSeedProfiles20261026b
open CompactHeightMellinInversion20261027 NativeCuspCompactMellinSynthesis20261027
open ActualIncompleteEisensteinTransform20261110 ActualIncompleteEisensteinGram20261110
open FiniteMeasureCauchyParameterIntegral20261026b

def heightMellin (ψ : HeightSeed) (s : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-s*(u : ℂ))*ψ.toFun (Real.exp u)

private def conjugateSeed (ψ : HeightSeed) : HeightSeed where
  toFun := fun y => star (ψ.toFun y)
  continuous := ψ.continuous.star
  compact := ψ.compact.comp_left (by simp)
  positive := (tsupport_comp_subset (g := fun c : ℂ => star c) (by simp) ψ.toFun).trans ψ.positive

theorem heightMellin_entire (ψ : HeightSeed) : Differentiable ℂ (heightMellin ψ) := by
  let K := Real.log '' tsupport ψ.toFun
  let F (v : ℂ) (u : ℝ) := Complex.exp (-v*(u : ℂ))*ψ.toFun (Real.exp u)
  have hK : IsCompact K := ψ.compact.image_of_continuousOn
    (fun y hy => (Real.continuousAt_log (ψ.positive hy).ne').continuousWithinAt)
  have H : Continuous (Function.uncurry F) := by
    unfold F Function.uncurry
    exact ((continuous_fst.neg.mul (Complex.continuous_ofReal.comp continuous_snd)).cexp).mul
      (ψ.continuous.comp (Real.continuous_exp.comp continuous_snd))
  have R : heightMellin ψ = fun v => ∫ u in K,F v u := by
    funext v
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have e : ψ.toFun (Real.exp u) = 0 := by
      by_contra hn
      exact hu ⟨Real.exp u,subset_tsupport _ hn,Real.log_exp u⟩
    simp [F,e]
  rw [R]
  letI : IsFiniteMeasure ((volume : Measure ℝ).restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  intro s
  obtain ⟨B,hB⟩ := ((isCompact_closedBall s 1).prod hK).exists_bound_of_continuousOn H.continuousOn
  apply (hasDerivAt_original_integral_of_disk_bound F s (R := 1) (C := max B 1) zero_lt_one
    (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _ _ _).2.differentiableAt
  · intro v
    exact (H.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · apply ae_of_all
    intro u v _
    unfold F
    fun_prop
  · filter_upwards [ae_restrict_mem hK.measurableSet] with u hu
    intro v hv
    exact (hB (v,u) ⟨ball_subset_closedBall hv,hu⟩).trans (le_max_left _ _)

theorem heightMellin_angular (ψ : SmoothHeightSeed) (σ t : ℝ) :
    heightMellin ψ.toHeightSeed (verticalParameter σ t) = mellinAngular ψ σ t := by
  rw [mellinAngular,mellinFrequency_literal]
  have H : 2*Real.pi*((2*Real.pi)⁻¹*t) = t := mul_inv_cancel_left₀ (by positivity) _
  simp only [H,heightMellin,verticalParameter]

private theorem exp_substitution (f : ℝ → ℂ) :
    (∫ y in Ioi (0 : ℝ), f y) = ∫ u : ℝ,Real.exp u • f (Real.exp u) := by
  simpa only [image_univ,Real.range_exp,setIntegral_univ,abs_of_pos (Real.exp_pos _)] using
    integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp) measurableSet_univ
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn f

private theorem jacobian_power (u : ℝ) (s : ℂ) :
    ((Real.exp u : ℝ) : ℂ)*(((Real.exp u : ℝ) : ℂ)⁻¹)^2*((Real.exp u : ℝ) : ℂ)^s =
      Complex.exp (-(1-s)*(u : ℂ)) := by
  have hn : ((Real.exp u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'
  rw [Complex.cpow_def_of_ne_zero hn,← Complex.ofReal_log (Real.exp_pos u).le,Real.log_exp,
    show ((Real.exp u : ℝ) : ℂ)*(((Real.exp u : ℝ) : ℂ)⁻¹)^2 = ((Real.exp u : ℝ) : ℂ)⁻¹ by
      field_simp]
  rw [Complex.ofReal_exp,← Complex.exp_neg,← Complex.exp_add]
  congr 1
  ring

private theorem moment_eq_laplace (ψ : HeightSeed) (s : ℂ) :
    moment ψ s = heightMellin (conjugateSeed ψ) (1-s) := by
  rw [moment,exp_substitution,heightMellin]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  change Real.exp u • (((Real.exp u)⁻¹^2 : ℝ) • (star (ψ.toFun (Real.exp u))*((Real.exp u : ℝ) : ℂ)^s)) = _
  simp only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv,conjugateSeed]
  rw [← jacobian_power]
  ring

theorem moment_entire (ψ : HeightSeed) : Differentiable ℂ (moment ψ) := by
  rw [show moment ψ = fun s => heightMellin (conjugateSeed ψ) (1-s) from funext (moment_eq_laplace ψ)]
  exact (heightMellin_entire _).comp (differentiable_const _ |>.sub differentiable_id)

theorem moment_conjugated (ψ : HeightSeed) (s : ℂ) :
    moment ψ s = star (heightMellin ψ (1-star s)) := by
  rw [moment_eq_laplace,heightMellin,heightMellin,Complex.star_def,← integral_conj]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  simp [conjugateSeed,Complex.star_def,← Complex.exp_conj]

end
end ImbalancedChen.Part3.ActualIncompleteMellinFactors20261110
