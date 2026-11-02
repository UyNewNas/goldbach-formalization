import ImbalancedChen.Part3ActualJCriticalLogBound
import ImbalancedChen.Part3ActualJCompactRealOrderContinuity
import ImbalancedChen.Part3ActualJFirstMixedDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# Positive-sign exceptional J: actual real-order cancellation

K source-only candidate, uncompiled. The normalization is Pascadi (3.18),
with doubled exceptional order alpha and r=i*alpha/2. The removable value
is 2*d_order J_0, not zero and not the opposite-sign K kernel.

The main analytic theorem proves one constant, selected before alpha and
q, for the actual kernel on 0<q<=1 and 0<=alpha<=7/32. The singular power
is q^(-alpha), not the fixed worst-case power q^(-7/32). The numerator
cancellation is proved using actual J's native order derivative and its
Poisson/Gamma formula. No Bessel estimate, spectral norm or Eq24 is an input.
The large-q oscillatory transform remains a separate obligation.
-/

namespace ImbalancedChen.Part3.ActualExceptionalJSmallKernel20261102

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a
open ActualJLocalOrderHolomorphic20261026a ActualJCriticalOrderZero20261026a
open ActualJCriticalLogBound20261026a
open ActualJCompactRealOrderContinuity20261026b
open ActualJFirstMixedDerivative20261026b

def exceptionalCap : ℝ := 7 / 32

theorem real_order_mem {nu : ℝ} (hnu : |nu| ≤ exceptionalCap) :
    (nu : ℂ) ∈ orderHalfPlane := by
  have hn := (abs_le.mp hnu).1
  change -(1 / 4 : ℝ) < nu
  norm_num [exceptionalCap] at hn ⊢
  linarith

private theorem gammaFactor_differentiableAt {nu : ℂ}
    (hnu : nu ∈ orderHalfPlane) : DifferentiableAt ℂ orderGammaFactor nu := by
  have hp : 0 < (nu + 1 / 2).re := by
    change -(1 / 4 : ℝ) < nu.re at hnu
    simp only [Complex.add_re]
    norm_num
    linarith
  have hg := (Complex.differentiableAt_Gamma (nu + 1 / 2) (fun n hn => by
    have he := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).comp nu
      (show DifferentiableAt ℂ (fun z : ℂ => z + 1 / 2) nu by fun_prop)
  have hnz : (Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne')
      (Complex.Gamma_ne_zero_of_re_pos hp)
  exact (hg.const_mul (Real.sqrt Real.pi : ℂ)).inv hnz

private theorem gammaFactor_analyticAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane) :
    AnalyticAt ℂ orderGammaFactor nu := by
  have hd : DifferentiableOn ℂ orderGammaFactor orderHalfPlane :=
    fun _ hz => (gammaFactor_differentiableAt hz).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hnu)

/-- A compact real-order bound on both native reciprocal-Gamma factors.
This is obtained by compactness of the actual analytic functions. -/
theorem exists_real_gamma_bounds :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ nu : ℝ, |nu| ≤ exceptionalCap →
        ‖orderGammaFactor (nu : ℂ)‖ ≤ A ∧
        ‖deriv orderGammaFactor (nu : ℂ)‖ ≤ B := by
  have hA : ContinuousOn (fun nu : ℝ => orderGammaFactor (nu : ℂ))
      (Icc (-exceptionalCap) exceptionalCap) := by
    intro nu hnu
    exact ((gammaFactor_analyticAt (real_order_mem (abs_le.mpr hnu))).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hB : ContinuousOn (fun nu : ℝ => deriv orderGammaFactor (nu : ℂ))
      (Icc (-exceptionalCap) exceptionalCap) := by
    intro nu hnu
    exact ((gammaFactor_analyticAt (real_order_mem (abs_le.mpr hnu))).deriv.continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨A, hAb⟩ := (isCompact_Icc : IsCompact (Icc (-exceptionalCap) exceptionalCap))
    .exists_bound_of_continuousOn hA
  obtain ⟨B, hBb⟩ := (isCompact_Icc : IsCompact (Icc (-exceptionalCap) exceptionalCap))
    .exists_bound_of_continuousOn hB
  refine ⟨|A| + 1, |B| + 1, by positivity, by positivity, ?_⟩
  intro nu hnu
  constructor
  · exact (hAb nu (abs_le.mp hnu)).trans (by linarith [le_abs_self A])
  · exact (hBb nu (abs_le.mp hnu)).trans (by linarith [le_abs_self B])

def realPoissonMass : ℝ :=
  ∫ u in Ioo (-1 : ℝ) 1, ‖jSymmetricPoissonWeight ((-3 / 8 : ℝ) : ℂ) u‖

theorem realPoissonMass_nonneg : 0 ≤ realPoissonMass :=
  integral_nonneg (fun _ => norm_nonneg _)

/-- One genuinely integrable endpoint weight dominates the full real
exceptional order band. The oscillatory q phase has norm one. -/
theorem real_orderPoissonIntegral_norm_le {nu : ℝ}
    (hnu : |nu| ≤ exceptionalCap) (q : ℝ) :
    ‖orderPoissonIntegral (nu : ℂ) q‖ ≤ realPoissonMass := by
  have hi : IntegrableOn
      (fun u => ‖jSymmetricPoissonWeight ((-3 / 8 : ℝ) : ℂ) u‖)
      (Ioo (-1 : ℝ) 1) := by
    simpa only [jSymmetricPoissonWeight, poissonWeight,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using
      (poissonWeight_integrable (nu := ((-3 / 8 : ℝ) : ℂ)) (by norm_num)).norm
  apply norm_integral_le_of_norm_le hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hphase : ‖Complex.exp (I * (q : ℂ) * (u : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [orderPoissonIntegrand_eq _ _ hu, jSymmetricPoissonIntegrand,
    norm_mul, hphase, one_mul]
  apply realPoissonWeight_norm_antitone _ hu
  have hn := (abs_le.mp hnu).1
  norm_num [exceptionalCap] at hn ⊢
  linarith

theorem real_orderPoissonDeriv_norm_le {nu : ℝ}
    (hnu : |nu| ≤ exceptionalCap) (q : ℝ) :
    ‖orderPoissonDeriv (nu : ℂ) q‖ ≤ poissonLogNormMass := by
  apply norm_integral_le_of_norm_le orderDerivativeEnvelope_integrable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact orderPoissonDerivIntegrand_norm_le (real_order_mem hnu) q hu

/-- The small-q power follows the radius of the current order segment.
The constant 2^(7/32) is independent of that radius. -/
theorem positive_power_norm_le {a nu q : ℝ}
    (ha : a ≤ exceptionalCap) (hnu : |nu| ≤ a) (hq : q ∈ Ioc (0 : ℝ) 1) :
    ‖(((q / 2 : ℝ) : ℂ) ^ (nu : ℂ))‖ ≤
      (2 : ℝ) ^ exceptionalCap * q ^ (-a) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < q / 2)]
  simp only [Complex.ofReal_re]
  calc
    (q / 2) ^ nu ≤ (q / 2) ^ (-a) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith [hq.2])
        (abs_le.mp hnu).1
    _ = (2 : ℝ) ^ a * q ^ (-a) := by
      rw [Real.div_rpow hq.1.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      ring
    _ ≤ (2 : ℝ) ^ exceptionalCap * q ^ (-a) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) ha)
        (Real.rpow_nonneg hq.1.le _)

/-- A derived, order-sensitive native derivative estimate. A single
constant works for every shrinking segment [-a,a], including a=0. -/
theorem exists_real_orderDerivative_small_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ a nu q : ℝ,
      0 ≤ a → a ≤ exceptionalCap → |nu| ≤ a → q ∈ Ioc (0 : ℝ) 1 →
      ‖actualJOrderDerivative (nu : ℂ) q‖ ≤
        D * (1 + |Real.log q|) * q ^ (-a) := by
  obtain ⟨A, B, hA, hB, hGamma⟩ := exists_real_gamma_bounds
  let H : ℝ := A * realPoissonMass * (1 + |Real.log 2|) +
    B * realPoissonMass + A * poissonLogNormMass + 1
  let D : ℝ := (2 : ℝ) ^ exceptionalCap * H
  have hM := realPoissonMass_nonneg
  have hL := poissonLogNormMass_nonneg
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro a nu q ha0 ha hnu hq
  have hn : |nu| ≤ exceptionalCap := hnu.trans ha
  obtain ⟨hGa, hGb⟩ := hGamma nu hn
  have hP := real_orderPoissonIntegral_norm_le hn q
  have hPd := real_orderPoissonDeriv_norm_le hn q
  have hpow := positive_power_norm_le ha hnu hq
  have hlog : ‖Complex.log (((q / 2 : ℝ) : ℂ))‖ ≤
      |Real.log q| + |Real.log 2| := by
    rw [← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ q / 2),
      Complex.norm_real, Real.norm_eq_abs,
      Real.log_div hq.1.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    exact abs_sub _ _
  let P : ℝ := (2 : ℝ) ^ exceptionalCap * q ^ (-a)
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hAM : 0 ≤ A * realPoissonMass := mul_nonneg hA.le hM
  have hBM : 0 ≤ B * realPoissonMass := mul_nonneg hB.le hM
  have hAL : 0 ≤ A * poissonLogNormMass := mul_nonneg hA.le hL
  have hco : A * realPoissonMass ≤ H := by
    dsimp [H]
    nlinarith [mul_nonneg hAM (abs_nonneg (Real.log 2))]
  have hconst : |Real.log 2| * A * realPoissonMass +
      B * realPoissonMass + A * poissonLogNormMass ≤ H := by
    dsimp [H]
    nlinarith
  have hbracket : (|Real.log q| + |Real.log 2|) * A * realPoissonMass +
      B * realPoissonMass + A * poissonLogNormMass ≤ H * (1 + |Real.log q|) := by
    have hm := mul_le_mul_of_nonneg_right hco (abs_nonneg (Real.log q))
    nlinarith
  calc
    ‖actualJOrderDerivative (nu : ℂ) q‖ ≤
        P * (|Real.log q| + |Real.log 2|) * A * realPoissonMass +
          P * B * realPoissonMass + P * A * poissonLogNormMass := by
      rw [actualJOrderDerivative_expansion (real_order_mem hn) hq.1]
      apply (norm_add_le _ _).trans
      apply add_le_add
      · apply (norm_add_le _ _).trans
        apply add_le_add
        · simp only [norm_mul]
          exact mul_le_mul (mul_le_mul (mul_le_mul hpow hlog (norm_nonneg _) hP0)
            hGa (norm_nonneg _) (mul_nonneg hP0 (by positivity)))
            hP (norm_nonneg _) (by positivity)
        · simp only [norm_mul]
          exact mul_le_mul (mul_le_mul hpow hGb (norm_nonneg _) hP0)
            hP (norm_nonneg _) (mul_nonneg hP0 hB.le)
      · simp only [norm_mul]
        exact mul_le_mul (mul_le_mul hpow hGa (norm_nonneg _) hP0)
          hPd (norm_nonneg _) (mul_nonneg hP0 hA.le)
    _ = P * ((|Real.log q| + |Real.log 2|) * A * realPoissonMass +
        B * realPoissonMass + A * poissonLogNormMass) := by ring
    _ ≤ P * (H * (1 + |Real.log q|)) :=
      mul_le_mul_of_nonneg_left hbracket hP0
    _ = D * (1 + |Real.log q|) * q ^ (-a) := by dsimp [P, D]; ring

/-- Exact positive-sign exceptional specialization of Pascadi (3.18).
The exceptional order is doubled; its zero value is the removable limit. -/
def positiveSignKernel (alpha q : ℝ) : ℂ :=
  if alpha = 0 then 2 * actualJOrderDerivative 0 q
  else ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ))) *
    (generalJ (alpha : ℂ) q - generalJ (-(alpha : ℂ)) q)

theorem positiveSignKernel_zero (q : ℝ) :
    positiveSignKernel 0 q = 2 * actualJOrderDerivative 0 q := by
  simp [positiveSignKernel]

theorem positiveSignKernel_eq {alpha : ℝ} (ha : alpha ≠ 0) (q : ℝ) :
    positiveSignKernel alpha q =
      ((Real.pi : ℂ) / (2 * (Real.sin (Real.pi * alpha / 2) : ℂ))) *
        (generalJ (alpha : ℂ) q - generalJ (-(alpha : ℂ)) q) := by
  simp only [positiveSignKernel, if_neg ha]

theorem alpha_le_sin {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) :
    alpha ≤ Real.sin (Real.pi * alpha / 2) := by
  have ha1 : alpha ≤ 1 := ha.trans (by norm_num [exceptionalCap])
  simpa only [div_mul_eq_mul_div] using Real.le_sin_mul ha0 ha1

/-- The existing analytic removable quotient gives the same convention,
including the exact factor -pi/2 and the value at alpha=0. -/
theorem positiveSignKernel_eq_critical {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    positiveSignKernel alpha q =
      -((Real.pi : ℂ) / 2) * criticalJRealKernel q (I * ((alpha / 2 : ℝ) : ℂ)) := by
  by_cases hzero : alpha = 0
  · subst alpha
    rw [positiveSignKernel_zero]
    simp only [zero_div, Complex.ofReal_zero, mul_zero, criticalJRealKernel_zero hq]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    <;> ring
  · have hap : 0 < alpha := lt_of_le_of_ne ha0 (Ne.symm hzero)
    have hs : Real.sin (Real.pi * alpha / 2) ≠ 0 :=
      (hap.trans_le (alpha_le_sin ha0 ha)).ne'
    have hz : I * ((alpha / 2 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (div_ne_zero hzero (by norm_num)))
    have hp : 2 * I * (I * ((alpha / 2 : ℝ) : ℂ)) = -(alpha : ℂ) := by
      push_cast
      calc
        2 * I * (I * ((alpha : ℂ) / 2)) = (I * I) * (alpha : ℂ) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    have hd : (Real.pi : ℂ) * (I * ((alpha / 2 : ℝ) : ℂ)) =
        ((Real.pi * alpha / 2 : ℝ) : ℂ) * I := by push_cast; ring
    rw [positiveSignKernel_eq hzero, criticalJRealKernel,
      criticalJQuotient_eq hz, hp, neg_neg, hd, Complex.sinh_mul_I,
      ← Complex.ofReal_sin]
    simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
    ring_nf
    <;> simp only [Complex.I_sq]
    <;> ring

/-- The literal pi/sinh(pi*r) and 1/(2*i) convention of Pascadi (3.18)
at r=i*alpha/2. This is an identity of actual J functions, not a spectral
normalization hypothesis. -/
theorem positiveSignKernel_eq_pascadi {alpha q : ℝ}
    (ha0 : 0 < alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    positiveSignKernel alpha q =
      ((Real.pi : ℂ) / Complex.sinh ((Real.pi : ℂ) * (I * ((alpha / 2 : ℝ) : ℂ)))) *
        ((generalJ (2 * I * (I * ((alpha / 2 : ℝ) : ℂ))) q -
            generalJ (-(2 * I * (I * ((alpha / 2 : ℝ) : ℂ)))) q) / (2 * I)) := by
  have hz : I * ((alpha / 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
  rw [positiveSignKernel_eq_critical ha0.le ha hq, criticalJRealKernel,
    criticalJQuotient_eq hz]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring

/-- Actual native real-order mean-value cancellation before division by
sin(pi*alpha/2). The derivative bound is proved above and is not a premise. -/
theorem exists_positiveSignKernel_small_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ alpha q : ℝ,
      0 ≤ alpha → alpha ≤ exceptionalCap → q ∈ Ioc (0 : ℝ) 1 →
      ‖positiveSignKernel alpha q‖ ≤
        B * (1 + |Real.log q|) * q ^ (-alpha) := by
  obtain ⟨D, hD, hDb⟩ := exists_real_orderDerivative_small_bound
  refine ⟨Real.pi * D, mul_pos Real.pi_pos hD, ?_⟩
  intro alpha q ha0 ha hq
  let E : ℝ := D * (1 + |Real.log q|) * q ^ (-alpha)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  by_cases hzero : alpha = 0
  · subst alpha
    have hb := hDb 0 0 q (by norm_num) (by norm_num [exceptionalCap])
      (by norm_num) hq
    rw [positiveSignKernel_zero, norm_mul, norm_ofNat]
    have hpi := mul_le_mul_of_nonneg_right Real.two_le_pi hE
    dsimp [E] at hpi
    calc
      2 * ‖actualJOrderDerivative 0 q‖ ≤
          2 * (D * (1 + |Real.log q|) * q ^ (-(0 : ℝ))) := by
        simpa only [Complex.ofReal_zero] using mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ Real.pi * (D * (1 + |Real.log q|) * q ^ (-(0 : ℝ))) := hpi
      _ = _ := by ring
  · have hap : 0 < alpha := lt_of_le_of_ne ha0 (Ne.symm hzero)
    have hdiff : ∀ nu ∈ Icc (-alpha) alpha,
        HasDerivWithinAt (fun s : ℝ => generalJ (s : ℂ) q)
          (actualJOrderDerivative (nu : ℂ) q) (Icc (-alpha) alpha) nu := by
      intro nu hnu
      exact (generalJ_order_hasDerivAt
        (real_order_mem ((abs_le.mpr hnu).trans ha)) hq.1).comp_ofReal.hasDerivWithinAt
    have hd : ∀ nu ∈ Icc (-alpha) alpha,
        ‖actualJOrderDerivative (nu : ℂ) q‖ ≤ E :=
      fun nu hnu => hDb alpha nu q ha0 ha (abs_le.mpr hnu) hq
    have hm := (convex_Icc (-alpha) alpha).norm_image_sub_le_of_norm_hasDerivWithin_le
      hdiff hd (show -alpha ∈ Icc (-alpha) alpha from ⟨le_rfl, by linarith⟩)
        (show alpha ∈ Icc (-alpha) alpha from ⟨by linarith, le_rfl⟩)
    have hlength : ‖alpha - -alpha‖ = 2 * alpha := by
      rw [sub_neg_eq_add, ← two_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ha0]
      norm_num
    rw [hlength, Complex.ofReal_neg] at hm
    have hs : 0 < Real.sin (Real.pi * alpha / 2) := hap.trans_le (alpha_le_sin ha0 ha)
    have hnum : ‖generalJ (alpha : ℂ) q - generalJ (-(alpha : ℂ)) q‖ ≤
        2 * E * Real.sin (Real.pi * alpha / 2) := by
      calc
        _ ≤ E * (2 * alpha) := hm
        _ ≤ E * (2 * Real.sin (Real.pi * alpha / 2)) := by gcongr; exact alpha_le_sin ha0 ha
        _ = _ := by ring
    rw [positiveSignKernel_eq hzero, norm_mul, norm_div, norm_mul,
      Complex.norm_real, Complex.norm_real, norm_ofNat,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hs]
    calc
      Real.pi / (2 * Real.sin (Real.pi * alpha / 2)) *
          ‖generalJ (alpha : ℂ) q - generalJ (-(alpha : ℂ)) q‖ ≤
        Real.pi / (2 * Real.sin (Real.pi * alpha / 2)) *
          (2 * E * Real.sin (Real.pi * alpha / 2)) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = Real.pi * E := by field_simp [hs.ne']; ring
      _ = _ := by dsimp [E]; ring

/-- Fixed once from actual Gamma/Poisson data, before every packet and
exceptional order. This definition introduces no bound as an assumption. -/
def smallKernelConstant : ℝ := exists_positiveSignKernel_small_bound.choose

theorem smallKernelConstant_pos : 0 < smallKernelConstant :=
  exists_positiveSignKernel_small_bound.choose_spec.1

theorem positiveSignKernel_small_bound {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : q ∈ Ioc (0 : ℝ) 1) :
    ‖positiveSignKernel alpha q‖ ≤
      smallKernelConstant * (1 + |Real.log q|) * q ^ (-alpha) :=
  exists_positiveSignKernel_small_bound.choose_spec.2 alpha q ha0 ha hq

/-- Positive-q continuity, including the actual order-zero derivative.
It licenses the same compact physical packet integration as the K branch. -/
theorem positiveSignKernel_continuousAt {alpha q : ℝ}
    (ha0 : 0 ≤ alpha) (ha : alpha ≤ exceptionalCap) (hq : 0 < q) :
    ContinuousAt (positiveSignKernel alpha) q := by
  by_cases hzero : alpha = 0
  · subst alpha
    have h := (actualJOrderDerivative_q_hasDerivAt
      (nu := (0 : ℂ)) (by norm_num [orderHalfPlane]) hq).continuousAt
    simpa only [positiveSignKernel, if_pos rfl] using continuousAt_const.mul h
  · have hpos : -1 < (alpha : ℂ).re := by simp only [Complex.ofReal_re]; linarith
    have hneg : -1 < (-(alpha : ℂ)).re := by
      simp only [Complex.neg_re, Complex.ofReal_re]
      norm_num [exceptionalCap] at ha
      linarith
    have h := (generalJ_differentiableAt hpos hq).continuousAt.sub
      (generalJ_differentiableAt hneg hq).continuousAt
    simpa only [positiveSignKernel, if_neg hzero] using continuousAt_const.mul h

end
end ImbalancedChen.Part3.ActualExceptionalJSmallKernel20261102
