import ImbalancedChen.Part3ActualContinuousSpatialProfiles
import ImbalancedChen.Part3CompletedAllLevelCompactParameterValues
import ImbalancedChen.Part3FiniteMeasureCauchyParameterIntegral

/-! Parameter regularity of the physical character and conductor-one
Eisenstein means on compact observation paths. A normalized cusp
horocycle and each of its oldform dilations are such paths. -/
namespace ImbalancedChen.Part3.ActualCompletedCurveMeans20261110

noncomputable section
open Complex Set Filter Topology Metric MeasureTheory UpperHalfPlane
open scoped UpperHalfPlane BigOperators
open ActualCharacterCompletedFourier20261110 ActualCharacterCriticalFamily20261110
open ComplexOrderKQCalculus ComplexOrderKBridgeSourceOnly ComplexOrderKUniformStripDecay20261025a
open ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open CompletedActualEisensteinIdentity20261025a CompletedEisensteinSpatialMaass
open FiniteMeasureCauchyParameterIntegral20261026b CompletedParameterDiskHeightValues20261026b
open CompletedAllLevelCompactParameterValues20261026b FiniteLevelEisensteinOldforms20261025a
open AllLevelContinuedMaass20261026a

def curveMean (Z : ℝ → ℍ) (F : ℂ → ℍ → ℂ) (s : ℂ) : ℂ := ∫ x in (0 : ℝ)..1, F s (Z x)

private def segment : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
private instance : IsFiniteMeasure segment := ⟨by simp [segment]⟩

private theorem curve_height {Z : ℝ → ℍ} (hZ : Continuous Z) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ x ∈ Icc (0 : ℝ) 1, (Z x).im ∈ Icc a b := by
  have hc := (UpperHalfPlane.continuous_im.comp hZ).continuousOn
  obtain ⟨u,hu,H⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr zero_le_one) hc
  obtain ⟨v,hv,J⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) hc
  exact ⟨(Z u).im,(Z v).im,(Z u).im_pos,isMinOn_iff.mp H v hv,fun x hx =>
    ⟨isMinOn_iff.mp H x hx,isMaxOn_iff.mp J x hx⟩⟩

private theorem amplitude_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {n : ℤ} (hn : n ≠ 0)
    {M : ℕ} {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) :
    ‖amplitude χ n s‖ ≤ (n.natAbs : ℝ)^(3*M+2) := by
  let N := n.natAbs
  have hN := Int.natAbs_pos.mpr hn
  let W := ∑ c ∈ N.divisors, (c : ℝ)^(1-2*s.re)
  have hw : 0 ≤ W := Finset.sum_nonneg (fun c _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hd : divisorFactor N (2*(s.re : ℂ)) = (W : ℂ) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat,W] using divisorFactor_ofReal N (2*s.re)
  have hdiv : ‖weightedDivisor χ n s‖ ≤ (N : ℝ)^(2*M+2) := by
    calc
      _ ≤ ∑ c ∈ N.divisors, ‖χ (c : ZMod q)*star (χ ((n/(c : ℤ) : ℤ) : ZMod q))*(c : ℂ)^(1-2*s)‖ :=
        norm_sum_le _ _
      _ ≤ W := by
        apply Finset.sum_le_sum
        intro c hc
        have hb := mul_le_mul (χ.norm_le_one (c : ZMod q))
          (χ.norm_le_one ((n/(c : ℤ) : ℤ) : ZMod q)) (norm_nonneg _) zero_le_one
        simp only [norm_mul,norm_star,Complex.norm_natCast_cpow_of_pos (Nat.pos_of_mem_divisors hc)]
        rw [show (1-2*s).re = 1-2*s.re by simp [Complex.mul_re]]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by simpa using hb)
      _ = ‖divisorFactor N (2*(s.re : ℂ))‖ := by rw [hd,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
      _ ≤ _ := divisorFactor_polynomial_bound hN M (by simpa using hs)
  have hAbs : (N : ℝ) = |(n : ℝ)| := by simp [N]
  rw [amplitude,norm_mul,← hAbs,Complex.ofReal_natCast]
  calc
    _ ≤ (N : ℝ)^M*(N : ℝ)^(2*M+2) :=
      mul_le_mul (power_prefactor_bound hN M hs) hdiv (norm_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; omega

private def envelope (M : ℕ) (a b : ℝ) (n : ℤ) : ℝ :=
  (2*Real.sqrt b*decayConstant M a)*((n.natAbs : ℝ)^(3*M+2)*
    Real.exp (-(Real.pi*a)*(n.natAbs : ℝ)))

private theorem envelope_summable (M : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) : Summable (envelope M a b) := by
  have H : Summable (fun n : ℕ => envelope M a b (n : ℤ)) := by
    simpa only [envelope,Int.natAbs_natCast] using
      (Real.summable_pow_mul_exp_neg_nat_mul (3*M+2) (mul_pos Real.pi_pos ha)).const_mul
        (2*Real.sqrt b*decayConstant M a)
  apply Summable.of_nat_of_neg_add_one H
  simpa [envelope,Int.natAbs_negSucc] using (summable_nat_add_iff 1).mpr H

private theorem term_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) {M : ℕ} {s : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) {a b : ℝ} (ha : 0 < a) (z : ℍ) (hz : z.im ∈ Icc a b) :
    ‖continuedCoefficient χ n z.im s*fourier n (z.re : UnitAddCircle)‖ ≤ envelope M a b n := by
  by_cases hn : n = 0
  · simp [continuedCoefficient,hn,envelope]
  have hN : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hn
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by simp
  have hqy : a ≤ (n.natAbs : ℝ)*z.im := hz.1.trans (le_mul_of_one_le_left z.im_pos.le hN)
  have harg : 2*Real.pi*a ≤ 2*Real.pi*(n.natAbs : ℝ)*z.im := by
    nlinarith [mul_le_mul_of_nonneg_left hqy (show 0 ≤ 2*Real.pi by positivity)]
  have hν : |(s-1/2).re| ≤ (M : ℝ)+1 := by
    obtain ⟨hl,hh⟩ := abs_le.mp hs
    apply abs_le.mpr
    norm_num [Complex.sub_re] <;> constructor <;> linarith
  have HK := complexOrderK_uniform_exp_bound (show 0 < 2*Real.pi*a by positivity) harg hν
  have he : Real.exp (-(2*Real.pi*(n.natAbs : ℝ)*z.im/2)) ≤ Real.exp (-(Real.pi*a)*(n.natAbs : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hz.1 (show 0 ≤ Real.pi*(n.natAbs : ℝ) by positivity)]
  have hk := HK.trans (mul_le_mul_of_nonneg_left he (stripDecayConstant_pos _ _ _).le)
  have hA := mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hz.2)
    (by norm_num : 0 ≤ (2 : ℝ))) (amplitude_bound χ hn hs) (norm_nonneg _) (by positivity)
  simp only [continuedCoefficient,if_neg hn,← habs,norm_mul,fourier_apply,Circle.norm_coe,mul_one,
    Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul hA hk (norm_nonneg _) (by positivity)).trans_eq (by unfold envelope decayConstant; ring)

private theorem signed_cont {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) (s : ℂ) :
    Continuous (fun z : ℍ => continuedCoefficient χ n z.im s*fourier n (z.re : UnitAddCircle)) := by
  by_cases hn : n = 0
  · simp [continuedCoefficient,hn]
  have hp : 0 < 2*Real.pi*|(n : ℝ)| := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    positivity
  have hK : Continuous (fun z : ℍ => complexOrderK (s-1/2) (2*Real.pi*|(n : ℝ)|*z.im)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (complexOrderK_hasDerivAt_q _ (mul_pos hp z.im_pos)).continuousAt.comp
      (continuous_const.mul UpperHalfPlane.continuous_im).continuousAt
  simp only [continuedCoefficient,if_neg hn]
  exact (((continuous_const.mul (Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp UpperHalfPlane.continuous_im))).mul continuous_const).mul hK).mul
      ((fourier n).continuous.comp (show Continuous (fun z : ℍ => (z.re : UnitAddCircle)) by fun_prop))

theorem completed_character_spatial_all {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    Continuous (completedFamily χ s) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let a := z.im/2
  let b := z.im+1
  have ha : 0 < a := half_pos z.im_pos
  have hc : ContinuousOn (completedFamily χ s) (UpperHalfPlane.im ⁻¹' Icc a b) :=
    continuousOn_tsum (fun n => (signed_cont χ n s).continuousOn)
      (envelope_summable (Nat.ceil |s.re|) ha b)
      (fun n w hw => term_bound χ n (Nat.le_ceil _) ha w hw)
  exact hc.continuousAt (UpperHalfPlane.continuous_im.continuousAt
    (Icc_mem_nhds (half_lt_self z.im_pos) (lt_add_one _)))

/-- Actual parameter differentiation under compact observation, proved by
the original Cauchy/DCT supplier and a simultaneous height/parameter
majorant of the full character Fourier series. -/
theorem character_curve_entire {q : ℕ} (χ : DirichletCharacter ℂ q)
    (Z : ℝ → ℍ) (hZ : Continuous Z) : Differentiable ℂ (curveMean Z (completedFamily χ)) := by
  intro u
  obtain ⟨a,b,ha,hab,hband⟩ := curve_height hZ
  let M := Nat.ceil (‖u‖+1)
  let C := max (∑' n : ℤ, envelope M a b n) 0 + 1
  have hc : 0 < C := by unfold C; positivity
  have H := hasDerivAt_original_integral_of_disk_bound (μ := segment)
    (fun v x => completedFamily χ v (Z x)) u (R := 1) zero_lt_one hc
    (fun v => ((completed_character_spatial_all χ v).comp hZ).aestronglyMeasurable)
    (Eventually.of_forall (fun x v _ => completedFamily_entire χ (Z x) v)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      intro v hv
      have hvu : ‖v-u‖ < 1 := by simpa [Metric.mem_ball,dist_eq_norm] using hv
      have htri : ‖v‖ ≤ ‖v-u‖+‖u‖ := by simpa using norm_add_le (v-u) u
      have hvM : |v.re| ≤ (M : ℝ) := (Complex.abs_re_le_norm v).trans
        ((by linarith : ‖v‖ ≤ ‖u‖+1).trans (Nat.le_ceil _))
      exact (tsum_of_norm_bounded (envelope_summable M ha b).hasSum
        (fun n => term_bound χ n hvM ha (Z x) (hband x ⟨hx.1.le,hx.2⟩))).trans
          (by dsimp [C]; linarith [le_max_left (∑' n : ℤ, envelope M a b n) 0]))
  simpa only [curveMean,intervalIntegral.integral_of_le zero_le_one,segment] using H.2.differentiableAt

theorem completed_principal_spatial (s : ℂ) : Continuous (completedActualEisenstein s) :=
  (completedEisensteinFourier_contDiffOn_two s).continuousOn.comp_continuous
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im) (fun z : ℍ => z.im_pos)

/-- The full-level physical mean retains the regularized central Fourier
constant and both actual poles of the completed family. -/
theorem principal_curve_analytic (Z : ℝ → ℍ) (hZ : Continuous Z) :
    AnalyticOnNhd ℂ (curveMean Z completedActualEisenstein) ({0,1} : Set ℂ)ᶜ := by
  have ho : IsOpen (({0,1} : Set ℂ)ᶜ) := (Set.finite_pair _ _).isClosed.isOpen_compl
  apply DifferentiableOn.analyticOnNhd _ ho
  intro u hu
  have hp : u ≠ 0 ∧ u ≠ 1 := by simpa using hu
  have hreg : u ∈ completedRegularDomain 1 := by
    simp [completedRegularDomain,canonicalPrimeList,oldformNormalization,hp.1,hp.2]
  obtain ⟨R,hR,hsub,hsphere⟩ := exists_regular_parameter_disk 1 u hreg
  obtain ⟨a,b,ha,hab,hband⟩ := curve_height hZ
  obtain ⟨C,hC,H⟩ := exists_completedFourier_disk_height_bound u hR ha hab
    (fun v hv => ⟨(hsub hv).1,(hsub hv).2.1⟩) hsphere
  have HD := hasDerivAt_original_integral_of_disk_bound (μ := segment)
    (fun v x => completedActualEisenstein v (Z x)) u hR hC
    (fun v => ((completed_principal_spatial v).comp hZ).aestronglyMeasurable)
    (Eventually.of_forall (fun x v hv =>
      (completedActualEisenstein_analyticOnNhd (Z x) v (by
        have hr := hsub (ball_subset_closedBall hv)
        simpa using And.intro hr.1 hr.2.1)).differentiableAt)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      intro v hv
      exact H v (ball_subset_closedBall hv) (Z x).im (hband x ⟨hx.1.le,hx.2⟩) (Z x).re)
  simpa only [curveMean,intervalIntegral.integral_of_le zero_le_one,segment] using
    HD.2.differentiableAt.differentiableWithinAt

end
end ImbalancedChen.Part3.ActualCompletedCurveMeans20261110
