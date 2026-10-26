import ImbalancedChen.Part3ActualJCriticalOrderZero
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Correct positive-q logarithmic bound for the actual order-zero primitive.
The actual order derivative of J on a compact imaginary-order interval is
bounded by C_T*(1+|log q|), uniformly over ALL q>0. This follows from the
literal differentiated Poisson representation: the positive-real power
has norm one on imaginary orders, the Poisson phase has norm one, and the
Gamma reciprocal and its native derivative are bounded on the compact
imaginary-order interval. The common endpoint logarithmic envelope comes
from the previously proved genuine order differentiation theorem.

The mean value theorem and |sinh(pi*t)| >= pi*|t| give the same logarithmic
bound for the actual removable i-normalized quotient, including t=0.
No finite bound at q=0, no sharp small-q asymptotic, and no identification
with a normalized automorphic Kuznetsov kernel are asserted.
-/

namespace ImbalancedChen.Part3.ActualJCriticalLogBound20261026a

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a
open ActualJLocalOrderHolomorphic20261026a ActualJCriticalOrderZero20261026a

def poissonNormMass : ℝ := ∫ t in Ioo (-1 : ℝ) 1, ‖poissonWeight 0 t‖

def poissonLogNormMass : ℝ := ∫ t in Ioo (-1 : ℝ) 1, orderDerivativeEnvelope t

theorem poissonNormMass_nonneg : 0 ≤ poissonNormMass :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem poissonLogNormMass_nonneg : 0 ≤ poissonLogNormMass :=
  integral_nonneg (fun _ => mul_nonneg (by norm_num) (norm_nonneg _))

/-- Actual reciprocal Gamma prefactor; its poles are excluded by the
positive real part of nu+1/2 on the order half-plane. -/
def orderGammaFactor (nu : ℂ) : ℂ :=
  ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2))⁻¹

private theorem orderGammaFactor_differentiableAt {nu : ℂ}
    (hnu : nu ∈ orderHalfPlane) : DifferentiableAt ℂ orderGammaFactor nu := by
  have hp : 0 < (nu + 1 / 2).re := by
    change -(1 / 4 : ℝ) < nu.re at hnu
    simp only [Complex.add_re]
    norm_num
    linarith
  have hg := (Complex.differentiableAt_Gamma (nu + 1 / 2) (fun n hn => by
    have h := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).comp nu (show DifferentiableAt ℂ (fun z : ℂ => z + 1 / 2) nu by fun_prop)
  have hnz : (Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne')
      (Complex.Gamma_ne_zero_of_re_pos hp)
  exact (hg.const_mul (Real.sqrt Real.pi : ℂ)).inv hnz

private theorem orderGammaFactor_analyticAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane) :
    AnalyticAt ℂ orderGammaFactor nu := by
  have hd : DifferentiableOn ℂ orderGammaFactor orderHalfPlane :=
    fun _ hz => (orderGammaFactor_differentiableAt hz).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hnu)

private theorem imaginary_order_mem (t : ℝ) : 2 * I * (t : ℂ) ∈ orderHalfPlane := by
  norm_num [orderHalfPlane, Complex.mul_re, Complex.mul_im]

private theorem imaginary_order_re (t : ℝ) : (2 * I * (t : ℂ)).re = 0 := by
  simp

theorem orderGammaFactor_imaginary_continuous :
    Continuous (fun t : ℝ => orderGammaFactor (2 * I * (t : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (orderGammaFactor_analyticAt (imaginary_order_mem t)).continuousAt.comp
    (show ContinuousAt (fun s : ℝ => 2 * I * (s : ℂ)) t by fun_prop)

theorem orderGammaFactor_deriv_imaginary_continuous :
    Continuous (fun t : ℝ => deriv orderGammaFactor (2 * I * (t : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (orderGammaFactor_analyticAt (imaginary_order_mem t)).deriv.continuousAt.comp
    (show ContinuousAt (fun s : ℝ => 2 * I * (s : ℂ)) t by fun_prop)

private theorem phase_norm_one (q t : ℝ) :
    ‖Complex.exp (I * (q : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem orderPoissonIntegrand_norm_imaginary {nu : ℂ} (hnu : nu.re = 0) (q : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ‖orderPoissonIntegrand nu q t‖ = ‖poissonWeight 0 t‖ := by
  have hx : 0 < 1 - t ^ 2 := by
    have hh := abs_lt.mpr ht
    nlinarith [sq_abs t, abs_nonneg t]
  rw [orderPoissonIntegrand, norm_mul, phase_norm_one, one_mul,
    poissonWeight, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, Complex.norm_exp, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.sub_re, hnu]

theorem orderPoissonIntegral_norm_imaginary {nu : ℂ} (hnu : nu.re = 0) (q : ℝ) :
    ‖orderPoissonIntegral nu q‖ ≤ poissonNormMass := by
  apply norm_integral_le_of_norm_le
    (poissonWeight_integrable (nu := (0 : ℂ)) (by norm_num)).norm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (orderPoissonIntegrand_norm_imaginary hnu q ht).le

theorem orderPoissonDeriv_norm_imaginary {nu : ℂ} (hnu : nu.re = 0) (q : ℝ) :
    ‖orderPoissonDeriv nu q‖ ≤ poissonLogNormMass := by
  apply norm_integral_le_of_norm_le orderDerivativeEnvelope_integrable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact orderPoissonDerivIntegrand_norm_le (by simp [orderHalfPlane, hnu]) q ht

private theorem positive_power_norm {nu : ℂ} (hnu : nu.re = 0)
    {q : ℝ} (hq : 0 < q) : ‖(((q / 2 : ℝ) : ℂ) ^ nu)‖ = 1 := by
  have hh : 0 < q / 2 := by positivity
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne'),
    ← Complex.ofReal_log hh.le, Complex.norm_exp]
  simp [Complex.mul_re, hnu]

private theorem positive_log_norm {q : ℝ} (hq : 0 < q) :
    ‖Complex.log (((q / 2 : ℝ) : ℂ))‖ = |Real.log (q / 2)| := by
  rw [← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ q / 2),
    Complex.norm_real, Real.norm_eq_abs]

/-- Expansion of the already proved actual native order derivative using
the actual reciprocal Gamma factor and its native derivative. -/
theorem actualJOrderDerivative_expansion {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    actualJOrderDerivative nu q =
      (((q / 2 : ℝ) : ℂ) ^ nu) * Complex.log (((q / 2 : ℝ) : ℂ)) *
        orderGammaFactor nu * orderPoissonIntegral nu q +
      (((q / 2 : ℝ) : ℂ) ^ nu) * deriv orderGammaFactor nu * orderPoissonIntegral nu q +
      (((q / 2 : ℝ) : ℂ) ^ nu) * orderGammaFactor nu * orderPoissonDeriv nu q := by
  have hp := (Complex.hasStrictDerivAt_const_cpow
    (x := (((q / 2 : ℝ) : ℂ))) (y := nu)
    (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity : (q / 2 : ℝ) ≠ 0)))).hasDerivAt
  have hg := (orderGammaFactor_differentiableAt hnu).hasDerivAt
  have h := (hp.mul hg).mul (orderPoissonIntegral_hasDerivAt hnu q)
  have hrepr : (fun z : ℂ => generalJ z q) =ᶠ[𝓝 nu]
      (fun z : ℂ => (((q / 2 : ℝ) : ℂ) ^ z) * orderGammaFactor z * orderPoissonIntegral z q) := by
    have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hnu] with z hz
    have hz' : -(1 / 2 : ℝ) < z.re := by
      change -(1 / 4 : ℝ) < z.re at hz
      linarith
    rw [orderPoissonIntegral_eq, generalJ_eq_symmetric_poisson_integral hz' hq,
      orderGammaFactor, div_eq_mul_inv]
  have hh := h.congr_of_eventuallyEq hrepr
  have he := (generalJ_order_hasDerivAt hnu hq).unique hh
  rw [he]
  ring

/-- Genuine compact imaginary-order derivative bound. The constant comes
from actual continuous reciprocal Gamma functions, not a supplied envelope.
It is uniform for all positive q, so in particular on 0<q<=B. -/
theorem exists_actualJOrderDerivative_log_bound (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → ∀ t ∈ Icc (-T) T,
      ‖actualJOrderDerivative (2 * I * (t : ℂ)) q‖ ≤ C * (1 + |Real.log q|) := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (-T) T)).exists_bound_of_continuousOn
    orderGammaFactor_imaginary_continuous.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-T) T)).exists_bound_of_continuousOn
    orderGammaFactor_deriv_imaginary_continuous.continuousOn
  let A' : ℝ := |A| + 1
  let B' : ℝ := |B| + 1
  let C : ℝ := A' * poissonNormMass * (1 + |Real.log 2|) +
    B' * poissonNormMass + A' * poissonLogNormMass + 1
  have hA' : 0 < A' := by dsimp [A']; positivity
  have hB' : 0 < B' := by dsimp [B']; positivity
  have hM : 0 ≤ poissonNormMass := poissonNormMass_nonneg
  have hML : 0 ≤ poissonLogNormMass := poissonLogNormMass_nonneg
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro q hq t ht
  have hAb : ‖orderGammaFactor (2 * I * (t : ℂ))‖ ≤ A' := by
    have h := hA t ht
    have hh := le_abs_self A
    dsimp [A']
    linarith
  have hBb : ‖deriv orderGammaFactor (2 * I * (t : ℂ))‖ ≤ B' := by
    have h := hB t ht
    have hh := le_abs_self B
    dsimp [B']
    linarith
  have hP := orderPoissonIntegral_norm_imaginary (imaginary_order_re t) q
  have hD := orderPoissonDeriv_norm_imaginary (imaginary_order_re t) q
  have hn := positive_power_norm (imaginary_order_re t) hq
  have hlog : |Real.log (q / 2)| ≤ |Real.log q| + |Real.log 2| := by
    rw [Real.log_div hq.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    exact abs_sub _ _
  have hAM : 0 ≤ A' * poissonNormMass := mul_nonneg hA'.le poissonNormMass_nonneg
  have hBM : 0 ≤ B' * poissonNormMass := mul_nonneg hB'.le poissonNormMass_nonneg
  have hAL : 0 ≤ A' * poissonLogNormMass := mul_nonneg hA'.le poissonLogNormMass_nonneg
  have hcoeff : A' * poissonNormMass ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hAM (abs_nonneg (Real.log 2))]
  have hconst : A' * poissonNormMass * |Real.log 2| +
      B' * poissonNormMass + A' * poissonLogNormMass ≤ C := by
    dsimp [C]
    nlinarith
  calc
    ‖actualJOrderDerivative (2 * I * (t : ℂ)) q‖ ≤
        |Real.log (q / 2)| * A' * poissonNormMass +
          B' * poissonNormMass + A' * poissonLogNormMass := by
      rw [actualJOrderDerivative_expansion (imaginary_order_mem t) hq]
      apply (norm_add_le _ _).trans
      apply add_le_add
      · apply (norm_add_le _ _).trans
        apply add_le_add
        · simp only [norm_mul, hn, one_mul, positive_log_norm hq]
          gcongr
        · simp only [norm_mul, hn, one_mul]
          exact mul_le_mul hBb hP (norm_nonneg _) hB'.le
      · simp only [norm_mul, hn, one_mul]
        exact mul_le_mul hAb hD (norm_nonneg _) hA'.le
    _ ≤ (|Real.log q| + |Real.log 2|) * A' * poissonNormMass +
        B' * poissonNormMass + A' * poissonLogNormMass := by
      gcongr
    _ ≤ C * (1 + |Real.log q|) := by
      have hm := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg (Real.log q))
      nlinarith

private theorem imaginaryJ_hasDerivAt {q : ℝ} (hq : 0 < q) (t : ℝ) :
    HasDerivAt (fun s : ℝ => generalJ (2 * I * (s : ℂ)) q)
      (2 * I * actualJOrderDerivative (2 * I * (t : ℂ)) q) t := by
  have hm : HasDerivAt (fun z : ℂ => 2 * I * z) (2 * I) (t : ℂ) :=
    (hasDerivAt_id (t : ℂ)).const_mul (2 * I)
  have h := ((generalJ_order_hasDerivAt (imaginary_order_mem t) hq).comp (t : ℂ) hm).comp_ofReal
  convert h using 1 <;> ring

/-- The numerator cancellation is proved from actual J's native order
derivative on the entire real segment, not an assumed quotient bound. -/
theorem oddOrderJ_norm_le_of_orderDerivative_bound {T C q : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hq : 0 < q)
    (hbound : ∀ s ∈ Icc (-T) T,
      ‖actualJOrderDerivative (2 * I * (s : ℂ)) q‖ ≤ C)
    {t : ℝ} (ht : |t| ≤ T) :
    ‖oddOrderJ q (t : ℂ)‖ ≤ 4 * C * |t| := by
  have ht' : t ∈ Icc (-T) T := abs_le.mp ht
  have hnt : -t ∈ Icc (-T) T := by constructor <;> linarith [ht'.1, ht'.2]
  have hdiff : ∀ s ∈ Icc (-T) T,
      HasDerivWithinAt (fun x : ℝ => generalJ (2 * I * (x : ℂ)) q)
        (2 * I * actualJOrderDerivative (2 * I * (s : ℂ)) q) (Icc (-T) T) s :=
    fun s _ => (imaginaryJ_hasDerivAt hq s).hasDerivWithinAt
  have hd : ∀ s ∈ Icc (-T) T,
      ‖2 * I * actualJOrderDerivative (2 * I * (s : ℂ)) q‖ ≤ 2 * C := by
    intro s hs
    simpa only [norm_mul, Complex.norm_I, norm_ofNat, mul_one] using
      mul_le_mul_of_nonneg_left (hbound s hs) (by norm_num : (0 : ℝ) ≤ 2)
  have hm := (convex_Icc (-T) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    hdiff hd hnt ht'
  have hs : 2 * I * ((-t : ℝ) : ℂ) = -(2 * I * (t : ℂ)) := by push_cast; ring
  have hnorm : ‖t - -t‖ = 2 * |t| := by
    rw [sub_neg_eq_add, ← two_mul, Real.norm_eq_abs, abs_mul]
    norm_num
  rw [hs, hnorm] at hm
  dsimp only [oddOrderJ]
  nlinarith

theorem pi_mul_abs_le_abs_sinh (t : ℝ) :
    Real.pi * |t| ≤ |Real.sinh (Real.pi * t)| := by
  rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
  exact Real.self_le_sinh_iff.mpr (mul_nonneg Real.pi_pos.le (abs_nonneg t))

/-- Correct logarithmic bound for the actual removable i-normalized
quotient, uniform in compact real height and all strictly positive q. -/
theorem exists_criticalJRealKernel_log_bound {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → ∀ t : ℝ, |t| ≤ T →
      ‖criticalJRealKernel q (t : ℂ)‖ ≤ C * (1 + |Real.log q|) := by
  obtain ⟨D, hD, hDb⟩ := exists_actualJOrderDerivative_log_bound T
  let C : ℝ := 4 * D / Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro q hq t ht
  have hL : 0 ≤ 1 + |Real.log q| := by positivity
  by_cases ht0 : t = 0
  · subst t
    have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
    have hb := hDb q hq 0 h0
    simp only [Complex.ofReal_zero, mul_zero] at hb ⊢
    rw [criticalJRealKernel_zero hq, norm_mul, norm_neg, norm_div,
      norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    dsimp [C]
    have hm := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ 4 / Real.pi)
    nlinarith
  · have hN := oddOrderJ_norm_le_of_orderDerivative_bound hT
      (mul_nonneg hD.le hL) hq (hDb q hq) ht
    have hden : 0 < |Real.sinh (Real.pi * t)| :=
      abs_pos.mpr (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht0))
    have hdenBound := pi_mul_abs_le_abs_sinh t
    rw [criticalJRealKernel, norm_mul, Complex.norm_I, one_mul,
      criticalJQuotient_eq (Complex.ofReal_ne_zero.mpr ht0), norm_div,
      ← Complex.ofReal_mul, ← Complex.ofReal_sinh,
      Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_left hdenBound
      (mul_nonneg hC.le hL)
    have heq : 4 * (D * (1 + |Real.log q|)) * |t| =
        (C * (1 + |Real.log q|)) * (Real.pi * |t|) := by
      dsimp [C]
      field_simp [Real.pi_ne_zero] <;> ring
    change ‖oddOrderJ q (t : ℂ)‖ ≤ _
    exact hN.trans (heq.le.trans hm)

/-- The explicit bounded positive-q domain requested by small-argument
orbital/Mellin consumers; q=0 is deliberately excluded. -/
theorem exists_criticalJRealKernel_small_q_bound {T : ℝ} (hT : 0 ≤ T) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Ioc (0 : ℝ) B, ∀ t : ℝ, |t| ≤ T →
      ‖criticalJRealKernel q (t : ℂ)‖ ≤ C * (1 + |Real.log q|) := by
  obtain ⟨C, hC, hb⟩ := exists_criticalJRealKernel_log_bound hT
  exact ⟨C, hC, fun q hq t ht => hb q hq.1 t ht⟩

end
end ImbalancedChen.Part3.ActualJCriticalLogBound20261026a
