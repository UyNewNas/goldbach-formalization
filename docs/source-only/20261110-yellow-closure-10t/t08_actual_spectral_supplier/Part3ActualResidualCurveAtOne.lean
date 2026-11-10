import ImbalancedChen.Part3ActualCriticalScatteringUnitarity
import ImbalancedChen.Part3CompletedParameterDiskHeightValues
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! The residue at 1 after genuine compact spatial observation. The
completed level-one polar part is regularized before integration. This
allows the actual original Young transformation to pass the residue to
every cusp without assuming a bound across the pole. -/
namespace ImbalancedChen.Part3.ActualResidualCurveAtOne20261110

noncomputable section
open Filter Set Topology Complex Metric MeasureTheory UpperHalfPlane
open scoped UpperHalfPlane BigOperators
open ActualCharacterScatteringReflection20261110 ActualCompletedCurveMeans20261110
open ActualYoungCriticalD20261110 ActualCharacterCriticalFamily20261110
open CompletedActualEisensteinIdentity20261025a CompletedEisensteinMeromorphic20261025a
open CompletedEisensteinReflection20261025a CompletedCompactParameterHeightValues20261026b
open FiniteMeasureCauchyParameterIntegral20261026b

def reg (s : ℂ) (z : ℍ) : ℂ :=
  (s-1)*(completedFourierEntirePart z.im z.re s-(z.im : ℂ)^s/(2*s))+(z.im : ℂ)^(1-s)/2

@[simp] theorem reg_one (z : ℍ) : reg 1 z = 1/2 := by simp [reg]

theorem reg_punctured {s : ℂ} (h : s ≠ 1) (z : ℍ) :
    reg s z = (s-1)*completedActualEisenstein s z := by
  rw [completedActualEisenstein,completedEisensteinFourier_polar_decomposition,mul_sub]
  have hpol : (s-1)*((z.im : ℂ)^(1-s)/(2*(1-s))) = -((z.im : ℂ)^(1-s))/2 := by
    field_simp [sub_ne_zero.mpr h.symm]
    ring
  rw [hpol]
  unfold reg
  ring

private theorem reg_diff {s : ℂ} (hs : s ≠ 0) (z : ℍ) :
    DifferentiableAt ℂ (fun w => reg w z) s := by
  have hp := heightPower_differentiable z.im_pos s
  have hq := reflectedHeightPower_differentiable z.im_pos s
  exact (((differentiableAt_id.sub_const (1 : ℂ)).mul
    ((completedFourierEntirePart_differentiable z.im_pos z.re s).sub
      (hp.div (differentiableAt_id.const_mul 2) (mul_ne_zero (by norm_num) hs)))).add (hq.div_const 2)

private theorem reg_spatial (s : ℂ) : Continuous (reg s) := by
  by_cases hs : s = 1
  · subst s
    simpa only [show reg 1 = fun _ : ℍ => (1/2 : ℂ) from funext reg_one] using
      (continuous_const (y := (1/2 : ℂ)) : Continuous (fun _ : ℍ => (1/2 : ℂ)))
  · simpa only [show reg s = fun z => (s-1)*completedActualEisenstein s z from funext (reg_punctured hs)] using
      (completed_principal_spatial s).const_mul (s-1)

private theorem reg_disk_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ closedBall (1 : ℂ) (1/4 : ℝ), ∀ z : ℍ,
      z.im ∈ Icc a b → ‖reg s z‖ ≤ C := by
  let K := sphere (1 : ℂ) (1/4 : ℝ)
  have hreg : ∀ w ∈ K, w ≠ 0 ∧ w ≠ 1 ∧ w ≠ 1/2 := by
    intro w hw
    have H : ‖w-1‖ = (1/4 : ℝ) := by simpa [K,mem_sphere,dist_eq_norm] using hw
    refine ⟨?_,?_,?_⟩ <;> intro e <;> subst w <;> norm_num at H
  obtain ⟨B,hB⟩ := (isCompact_sphere (1 : ℂ) (1/4 : ℝ)).isBounded.exists_norm_le
  obtain ⟨C,hC,HC⟩ := exists_completedFourier_compact_height_bound K (isCompact_sphere _ _)
    (Nat.ceil B) (fun w hw => (Complex.abs_re_le_norm w).trans ((hB w hw).trans (Nat.le_ceil B))) ha hab hreg
  refine ⟨C,hC,?_⟩
  intro s hs z hz
  have hd : DifferentiableOn ℂ (fun w => reg w z) (closedBall (1 : ℂ) (1/4 : ℝ)) := by
    intro w hw
    apply (reg_diff _ z).differentiableWithinAt
    intro e
    subst w
    norm_num [mem_closedBall,dist_eq_norm] at hw
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hd.diffContOnCl_ball Subset.rfl)
  · intro w hw
    rw [frontier_ball _ (by norm_num : (1/4 : ℝ) ≠ 0)] at hw
    rw [reg_punctured (hreg w hw).2.1,norm_mul]
    have hw' : ‖w-1‖ = (1/4 : ℝ) := by simpa [mem_sphere,dist_eq_norm] using hw
    calc
      _ ≤ (1/4 : ℝ)*C := by rw [hw']; exact mul_le_mul_of_nonneg_left (HC w hw z.im hz z.re) (by norm_num)
      _ ≤ C := by linarith
  · rwa [closure_ball _ (by norm_num : (1/4 : ℝ) ≠ 0)]

private def segment : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
private instance : IsFiniteMeasure segment := ⟨by simp [segment]⟩

/-- The original completed pole has residue 1/2 after integrating over
any continuous unit-parameter observation path, including a dilated
normalized cusp horocycle. -/
theorem principal_curve_residue (Z : ℝ → ℍ) (hZ : Continuous Z) :
    Tendsto (fun s : ℂ => (s-1)*curveMean Z completedActualEisenstein s)
      (𝓝[≠] 1) (𝓝 (1/2 : ℂ)) := by
  have hc := (UpperHalfPlane.continuous_im.comp hZ).continuousOn
  obtain ⟨u,hu,HU⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hc
  obtain ⟨v,hv,HV⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (zero_le_one : (0 : ℝ) ≤ 1)) hc
  obtain ⟨C,hC,HB⟩ := reg_disk_bound (Z u).im_pos (isMinOn_iff.mp HU v hv)
  have H := hasDerivAt_original_integral_of_disk_bound (μ := segment) (fun w x => reg w (Z x))
    (1 : ℂ) (R := 1/4) (by norm_num) hC (fun w => ((reg_spatial w).comp hZ).aestronglyMeasurable)
    (Eventually.of_forall (fun x w hw => reg_diff (by intro e; subst w; norm_num [mem_ball,dist_eq_norm] at hw) _))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      intro w hw
      exact HB w (ball_subset_closedBall hw) (Z x) ⟨isMinOn_iff.mp HU x ⟨hx.1.le,hx.2⟩,
        isMaxOn_iff.mp HV x ⟨hx.1.le,hx.2⟩⟩)
  have HL : Tendsto (curveMean Z reg) (𝓝[≠] 1) (𝓝 (1/2 : ℂ)) := by
    have h₁ : curveMean Z reg 1 = (1/2 : ℂ) := by simp [curveMean]
    rw [← h₁]
    simpa only [curveMean,intervalIntegral.integral_of_le zero_le_one,segment] using
      H.2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply HL.congr'
  filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 1)
  simp only [curveMean,reg_punctured hw,intervalIntegral.integral_const_mul]

private theorem scale_cont_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousAt (ordinaryScale χ) 1 := by
  have hp : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ)^w) 1 :=
    differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hq : DifferentiableAt ℂ (fun w : ℂ => (q : ℂ)^w) 1 :=
    differentiableAt_id.const_cpow (.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hL {k : ℕ} [NeZero k] (η : DirichletCharacter ℂ k) :
      DifferentiableAt ℂ (fun w : ℂ => reciprocalL η (2*w)) 1 :=
    (reciprocalL_differentiableAt η _ (by norm_num)).comp 1 (differentiableAt_id.const_mul 2)
  have HΓ := Complex.differentiable_one_div_Gamma (1 : ℂ)
  by_cases e : q = 1
  · simpa only [ordinaryScale,if_pos e,div_eq_mul_inv,one_mul] using
      ((hp.mul HΓ).mul (hL (1 : DirichletCharacter ℂ 1))).continuousAt
  · have hq1 : (q : ℂ)^(1 : ℂ) ≠ 0 := by simp [NeZero.ne q]
    simpa only [ordinaryScale,if_neg e,uncompletionFactor,div_eq_mul_inv,one_mul] using
      ((((hp.div hq hq1).mul_const (ActualCharacterPoissonRows20261110.gauss χ)).mul HΓ).mul (hL (χ^2))).continuousAt

private theorem scale_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : q = 1) :
    ordinaryScale χ 1*(1/2 : ℂ) = 3/(Real.pi : ℂ) := by
  have hπ := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have L : reciprocalL (1 : DirichletCharacter ℂ 1) 2 = (((Real.pi : ℂ)^2)/6)⁻¹ := by
    rw [reciprocalL,if_pos rfl,DirichletCharacter.LFunctionTrivChar₁,
      Function.update_of_ne (by norm_num : (2 : ℂ) ≠ 1),DirichletCharacter.LFunction_modOne_eq,riemannZeta_two]
    norm_num
  rw [ordinaryScale,if_pos hq,mul_one,L,Complex.cpow_one,Complex.Gamma_one]
  field_simp [hπ] <;> ring

def dilationResidue (q : ℕ) : ℂ := if q = 1 then 3/(Real.pi : ℂ) else 0

/-- The ordinary physical residue of every genuine primitive dilation
is 3/π for conductor one and zero for higher conductor. The observation
path may be constant, hence this includes the pointwise assertion. -/
theorem ordinary_curve_residue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (Z : ℝ → ℍ) (hZ : Continuous Z) :
    Tendsto (fun s : ℂ => (s-1)*curveMean Z (ordinary χ) s) (𝓝[≠] 1) (𝓝 (dilationResidue q)) := by
  have hS : Tendsto (ordinaryScale χ) (𝓝[≠] (1 : ℂ)) (𝓝 (ordinaryScale χ 1)) :=
    (scale_cont_one χ).tendsto.mono_left nhdsWithin_le_nhds
  by_cases e : q = 1
  · have H := hS.mul (principal_curve_residue Z hZ)
    simp only [scale_at_one χ e] at H
    simpa only [dilationResidue,if_pos e,curveMean,ordinary_factors,completedPart,
      intervalIntegral.integral_const_mul,mul_left_comm] using H
  · have hx : Tendsto (fun w : ℂ => w-1) (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
      simpa using ((continuous_id.sub (continuous_const (y := (1 : ℂ)))).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (1 : ℂ) ≤ 𝓝 1))
    have H := hx.mul
      (hS.mul ((character_curve_entire χ Z hZ 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
    simpa only [dilationResidue,if_neg e,curveMean,ordinary_factors,completedPart,
      intervalIntegral.integral_const_mul,sub_self,zero_mul] using H

end
end ImbalancedChen.Part3.ActualResidualCurveAtOne20261110
