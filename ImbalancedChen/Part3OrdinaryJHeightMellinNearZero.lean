import ImbalancedChen.Part3ActualJOrderDerivativeUniformLargeQ
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Standalone ordinary-J height-derivative Mellin majorant at q=0. Literal
principal/Gamma prefactors and actual Poisson moments supply the bound;
half of Re(s)>0 absorbs the logarithm. The result is about the actual
ordinary-J derivative integrand, not a replacement scalar/critical-kernel
theorem. No critical module, held46d7 source, or assumed domination is used.
-/

namespace ImbalancedChen.Part3.OrdinaryJHeightMellinNearZero20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open ActualJLocalOrderHolomorphic20261026a ActualJPoissonPrefactorMixed20261026b
open ActualJPoissonMixedMoments20261026b ActualJFirstMixedDerivative20261026b
open ActualJHeightRadialForcing20261026b

def ordinaryJHeightMellinIntegrand (s : ℂ) (t q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 1) * heightOrderJ t q

private def mass0 : ℝ := ∫ u in Ioo (-1 : ℝ) 1, ‖orderPoissonIntegrand 0 0 u‖
private def massLog : ℝ := ∫ u in Ioo (-1 : ℝ) 1, orderDerivativeEnvelope u

private theorem mass0_nonneg : 0 ≤ mass0 := integral_nonneg (fun _ => norm_nonneg _)
private theorem massLog_nonneg : 0 ≤ massLog :=
  integral_nonneg (fun _ => mul_nonneg (by norm_num) (norm_nonneg _))

private theorem imaginary_order_mem (t : ℝ) : 2 * I * (t : ℂ) ∈ orderHalfPlane := by
  simp [orderHalfPlane]

private theorem moment0_norm_le (t q : ℝ) : ‖poissonQMoment 0 (2 * I * (t : ℂ)) q‖ ≤ mass0 := by
  change ‖∫ u in Ioo (-1 : ℝ) 1, orderPoissonIntegrand (2 * I * (t : ℂ)) q u‖ ≤ _
  apply norm_integral_le_of_norm_le (orderPoisson_integrable (nu := (0 : ℂ)) (by norm_num) 0).norm
  filter_upwards with u
  unfold orderPoissonIntegrand
  simp only [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

private theorem logMoment0_norm_le (t q : ℝ) :
    ‖poissonQLogMoment 0 (2 * I * (t : ℂ)) q‖ ≤ massLog := by
  change ‖∫ u in Ioo (-1 : ℝ) 1, orderPoissonDerivIntegrand (2 * I * (t : ℂ)) q u‖ ≤ _
  apply norm_integral_le_of_norm_le orderDerivativeEnvelope_integrable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact orderPoissonDerivIntegrand_norm_le (imaginary_order_mem t) q hu

private theorem denominatorOrder_continuousAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane) :
    ContinuousAt gammaDenominatorOrder nu := by
  have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ gammaDenominator orderHalfPlane :=
    fun z hz => (gammaDenominator_hasDerivAt hz).differentiableAt.differentiableWithinAt
  have hc := (hd.analyticAt (hopen.mem_nhds hnu)).deriv.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hnu] with z hz
  exact (gammaDenominator_hasDerivAt hz).deriv.symm

private theorem inverseDenominator_height_continuous :
    Continuous (fun t : ℝ => (gammaDenominator (2 * I * (t : ℂ)))⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (((gammaDenominator_hasDerivAt (imaginary_order_mem t)).continuousAt
    .inv₀ (gammaDenominator_ne_zero (imaginary_order_mem t))).comp (by fun_prop))

private theorem denominatorOrderRatio_height_continuous :
    Continuous (fun t : ℝ => gammaDenominatorOrder (2 * I * (t : ℂ)) /
      gammaDenominator (2 * I * (t : ℂ)) ^ 2) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h0 := denominatorOrder_continuousAt (imaginary_order_mem t)
  have h1 := (gammaDenominator_hasDerivAt (imaginary_order_mem t)).continuousAt
  exact (h0.div (h1.pow 2) (pow_ne_zero 2 (gammaDenominator_ne_zero (imaginary_order_mem t))))
    .comp (by fun_prop)

private theorem prefactor_norm_eq (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖poissonPrefactor (2 * I * (t : ℂ)) q‖ = ‖(gammaDenominator (2 * I * (t : ℂ)))⁻¹‖ := by
  unfold poissonPrefactor
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < q / 2)]
  simp

private theorem prefactorOrder_norm_le (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ‖poissonPrefactorOrder (2 * I * (t : ℂ)) q‖ ≤
      ‖(gammaDenominator (2 * I * (t : ℂ)))⁻¹‖ * |Real.log (q / 2)| +
        ‖gammaDenominatorOrder (2 * I * (t : ℂ)) / gammaDenominator (2 * I * (t : ℂ)) ^ 2‖ := by
  let nu : ℂ := 2 * I * (t : ℂ)
  have hg := gammaDenominator_ne_zero (imaginary_order_mem t)
  have he : poissonPrefactorOrder nu q = poissonPrefactor nu q * Complex.log (((q / 2 : ℝ) : ℂ)) -
      (((q / 2 : ℝ) : ℂ) ^ nu) * (gammaDenominatorOrder nu / gammaDenominator nu ^ 2) := by
    unfold poissonPrefactorOrder poissonPrefactor
    field_simp [hg] <;> ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hp : ‖(((q / 2 : ℝ) : ℂ) ^ nu)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < q / 2)]
    dsimp [nu]
    simp
  rw [norm_mul, norm_mul, hp, one_mul, prefactor_norm_eq t hq,
    ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ q / 2), Complex.norm_real, Real.norm_eq_abs]

/-- Actual ordinary derivative-integrand near-zero L1 majorant. The
power is integrable and the bound is uniform on the supplied compact t. -/
theorem exists_ordinaryJHeightMellin_near_majorant {s : ℂ} (hs : 0 < s.re) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      IntegrableOn (fun q : ℝ => C * q ^ (s.re / 2 - 1)) (Ioc 0 1) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ q ∈ Ioc (0 : ℝ) 1,
        ‖ordinaryJHeightMellinIntegrand s t q‖ ≤ C * q ^ (s.re / 2 - 1) := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (-T) T))
    .exists_bound_of_continuousOn inverseDenominator_height_continuous.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-T) T))
    .exists_bound_of_continuousOn denominatorOrderRatio_height_continuous.continuousOn
  let A' : ℝ := |A| + 1
  let B' : ℝ := |B| + 1
  let D : ℝ := 2 * (A' * mass0 + A' * |Real.log 2| * mass0 + B' * mass0 + A' * massLog) + 1
  let C : ℝ := D * (1 + 2 / s.re)
  have hAp : 0 < A' := by dsimp [A']; positivity
  have hBp : 0 < B' := by dsimp [B']; positivity
  have hM0 : 0 ≤ mass0 := mass0_nonneg
  have hML : 0 ≤ massLog := massLog_nonneg
  have hDp : 0 < D := by dsimp [D]; positivity
  have hCp : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCp, ?_, ?_⟩
  · rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2
      (by linarith : -1 < s.re / 2 - 1)).const_mul C
  · intro t ht q hq
    have hAb : ‖(gammaDenominator (2 * I * (t : ℂ)))⁻¹‖ ≤ A' := by
      have h := hA t (abs_le.mp ht)
      have hh := le_abs_self A
      dsimp [A']
      linarith
    have hBb : ‖gammaDenominatorOrder (2 * I * (t : ℂ)) /
        gammaDenominator (2 * I * (t : ℂ)) ^ 2‖ ≤ B' := by
      have h := hB t (abs_le.mp ht)
      have hh := le_abs_self B
      dsimp [B']
      linarith
    have hlog : |Real.log (q / 2)| ≤ |Real.log q| + |Real.log 2| := by
      rw [Real.log_div hq.1.ne' (by norm_num : (2 : ℝ) ≠ 0)]
      exact abs_sub _ _
    have hD : ‖heightOrderJ t q‖ ≤ D * (1 + |Real.log q|) := by
      have hP := prefactorOrder_norm_le t hq.1
      have hM := moment0_norm_le t q
      have hL := logMoment0_norm_le t q
      rw [heightOrderJ, norm_mul, norm_mul, Complex.norm_I, norm_ofNat, mul_one]
      rw [actualJOrderDerivative_eq_poisson]
      apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
      simp only [norm_mul]
      rw [prefactor_norm_eq t hq.1]
      have hterm : ‖poissonPrefactorOrder (2 * I * (t : ℂ)) q‖ ≤
          A' * (|Real.log q| + |Real.log 2|) + B' := by
        calc
          _ ≤ ‖(gammaDenominator (2 * I * (t : ℂ)))⁻¹‖ * |Real.log (q / 2)| +
              ‖gammaDenominatorOrder (2 * I * (t : ℂ)) /
                gammaDenominator (2 * I * (t : ℂ)) ^ 2‖ := hP
          _ ≤ _ := add_le_add (mul_le_mul hAb hlog (abs_nonneg _) hAp.le) hBb
      have hm := mul_le_mul hterm hM (norm_nonneg _) (by positivity : 0 ≤ A' * (|Real.log q| + |Real.log 2|) + B')
      have hl := mul_le_mul hAb hL (norm_nonneg _) hAp.le
      have hX : 0 ≤ A' * mass0 := mul_nonneg hAp.le hM0
      have hY : 0 ≤ A' * |Real.log 2| * mass0 + B' * mass0 + A' * massLog := by positivity
      have hYL := mul_nonneg hY (abs_nonneg (Real.log q))
      dsimp [D]
      nlinarith [abs_nonneg (Real.log q)]
    have hd : 0 < s.re / 2 := by linarith
    have hu : q ^ (s.re / 2) ≤ 1 := Real.rpow_le_one hq.1.le hq.2 hd.le
    have hl := (Real.abs_log_mul_self_rpow_lt q (s.re / 2) hq.1 hq.2 hd).le
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hq.1.le _)] at hl
    have hrec : (1 : ℝ) / (s.re / 2) = 2 / s.re := by field_simp
    rw [hrec] at hl
    have hsplit : q ^ (s.re - 1) = q ^ (s.re / 2 - 1) * q ^ (s.re / 2) := by
      rw [← Real.rpow_add hq.1]
      congr 1
      ring
    rw [ordinaryJHeightMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq.1]
    simp only [Complex.sub_re, Complex.one_re]
    calc
      q ^ (s.re - 1) * ‖heightOrderJ t q‖ ≤ q ^ (s.re - 1) * (D * (1 + |Real.log q|)) :=
        mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hq.1.le _)
      _ ≤ C * q ^ (s.re / 2 - 1) := by
        rw [hsplit]
        have hp := mul_le_mul_of_nonneg_left (add_le_add hu hl)
          (mul_nonneg hDp.le (Real.rpow_nonneg hq.1.le (s.re / 2 - 1)))
        dsimp [C]
        nlinarith

end
end ImbalancedChen.Part3.OrdinaryJHeightMellinNearZero20261026b
