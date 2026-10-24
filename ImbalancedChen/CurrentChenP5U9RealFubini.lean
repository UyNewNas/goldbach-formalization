import ImbalancedChen.CurrentChenP5U9RealDomain
import ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral
import ImbalancedChen.FinitePiIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The two correct real U9 three-exponent integral dictionaries

SOURCE ONLY / UNCOMPILED. Over w in [(1-t-u)/2,1-t-u), the kernel
1/(t*u*w) integrates to log(2)/(t*u). The kernel 1/(t*u*w^2) instead
integrates to 1/(t*u*(1-t-u)), hence to the installed literal original J.

The second identity is a REAL integral dictionary, not a claim that the
actual unweighted prime source has reciprocal-squared log-coordinate
density. The actual source mass is supplied separately by the PNT chain.
-/

namespace ImbalancedChen.P5U9RealDomain

noncomputable section

open MeasureTheory Set
open scoped Classical BigOperators

private theorem integral_three (f : Point → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ t : ℝ, ∫ u : ℝ, ∫ w : ℝ, f ![t, u, w] := by
  let E := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piUnique _
  have hvec (t u w : ℝ) : Fin.cons t (Fin.cons u (E.symm w)) = ![t, u, w] := by
    ext i
    fin_cases i <;> simp [E, MeasurableEquiv.piUnique, Equiv.piUnique]
  calc
    _ = ∫ t : ℝ, ∫ u : ℝ, ∫ v : Fin 1 → ℝ,
        f (Fin.cons t (Fin.cons u v)) := integral_fin_pair f hf
    _ = ∫ t : ℝ, ∫ u : ℝ, ∫ w : ℝ,
        f (Fin.cons t (Fin.cons u (E.symm w))) := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply integral_congr_ae
      filter_upwards [] with u
      exact (hE.symm.integral_comp' (fun v => f (Fin.cons t (Fin.cons u v)))).symm
    _ = _ := by simp only [hvec]

/-- Fubini for the actual mixed half-open three-dimensional real domain.
The input is the genuine integrability of the chosen kernel on that domain. -/
theorem setIntegral_domain_eq_nested (f : Point → ℝ) (hf : IntegrableOn f domain) :
    (∫ x in domain, f x) =
      ∫ t in Ico (19 / 125 : ℝ) (59 / 250 : ℝ),
        ∫ u in Ico (59 / 250 : ℝ) ((1 - t) / 2),
          ∫ w in Ico ((1 - t - u) / 2) (1 - t - u), f ![t, u, w] := by
  let F := domain.indicator f
  have hF : Integrable F := hf.integrable_indicator measurableSet_domain
  have hpoint (t u w : ℝ) : F ![t, u, w] =
      (Ico (19 / 125 : ℝ) (59 / 250 : ℝ)).indicator
        (fun t => (Ico (59 / 250 : ℝ) ((1 - t) / 2)).indicator
          (fun u => (Ico ((1 - t - u) / 2) (1 - t - u)).indicator
            (fun w => f ![t, u, w]) w) u) t := by
    by_cases ht : t ∈ Ico (19 / 125 : ℝ) (59 / 250 : ℝ) <;>
      by_cases hu : u ∈ Ico (59 / 250 : ℝ) ((1 - t) / 2) <;>
      by_cases hw : w ∈ Ico ((1 - t - u) / 2) (1 - t - u) <;>
      simp_all only [F, Set.indicator_apply, domain_vec_iff, and_self,
        and_true, and_false, true_and, false_and, if_true, if_false]
  calc
    _ = ∫ x, F x := (integral_indicator measurableSet_domain).symm
    _ = ∫ t : ℝ, ∫ u : ℝ, ∫ w : ℝ, F ![t, u, w] := integral_three F hF
    _ = ∫ t : ℝ, (Ico (19 / 125 : ℝ) (59 / 250 : ℝ)).indicator
        (fun t => ∫ u in Ico (59 / 250 : ℝ) ((1 - t) / 2),
          ∫ w in Ico ((1 - t - u) / 2) (1 - t - u), f ![t, u, w]) t := by
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Ico (19 / 125 : ℝ) (59 / 250 : ℝ)
      · rw [indicator_of_mem ht]
        calc
          _ = ∫ u : ℝ, (Ico (59 / 250 : ℝ) ((1 - t) / 2)).indicator
              (fun u => ∫ w in Ico ((1 - t - u) / 2) (1 - t - u), f ![t, u, w]) u := by
            apply integral_congr_ae
            filter_upwards [] with u
            by_cases hu : u ∈ Ico (59 / 250 : ℝ) ((1 - t) / 2)
            · rw [indicator_of_mem hu]
              simp_rw [hpoint, indicator_of_mem ht, indicator_of_mem hu]
              exact integral_indicator measurableSet_Ico
            · rw [indicator_of_notMem hu]
              simp_rw [hpoint, indicator_of_mem ht, indicator_of_notMem hu]
              exact integral_zero ℝ ℝ
          _ = _ := integral_indicator measurableSet_Ico
      · rw [indicator_of_notMem ht]
        simp_rw [hpoint, indicator_of_notMem ht]
        simp only [integral_zero]
    _ = _ := integral_indicator measurableSet_Ico

/-- Exact logarithmic primitive for the unsquared reciprocal kernel. -/
theorem inner_kernel_integral {t u g : ℝ} (ht : 0 < t) (hu : 0 < u) (hg : 0 < g) :
    (∫ w in Ico (g / 2) g, 1 / (t * u * w)) = Real.log (2 : ℝ) / (t * u) := by
  have hab : g / 2 ≤ g := by linarith only [hg]
  let F := fun w : ℝ => Real.log w / (t * u)
  have hcont : ContinuousOn (fun w : ℝ => 1 / (t * u * w)) (Icc (g / 2) g) := by
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro w hw
    exact (mul_pos (mul_pos ht hu) ((half_pos hg).trans_le hw.1)).ne'
  have hderiv : ∀ w ∈ uIcc (g / 2) g, HasDerivAt F (1 / (t * u * w)) w := by
    intro w hw
    rw [uIcc_of_le hab] at hw
    have hwp : 0 < w := (half_pos hg).trans_le hw.1
    have hd := (Real.hasDerivAt_log hwp.ne').div_const (t * u)
    apply hd.congr_deriv
    field_simp [ht.ne', hu.ne', hwp.ne'] <;> ring
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hab)]
  have hquot : g / (g / 2) = (2 : ℝ) := by field_simp [hg.ne'] <;> ring
  dsimp only [F]
  rw [← sub_div, ← Real.log_div hg.ne' (half_pos hg).ne', hquot]

/-- Exact reciprocal primitive for the squared-terminal kernel. -/
theorem inner_squaredTerminalKernel_integral {t u g : ℝ}
    (ht : 0 < t) (hu : 0 < u) (hg : 0 < g) :
    (∫ w in Ico (g / 2) g, 1 / (t * u * w ^ 2)) = 1 / (t * u * g) := by
  have hab : g / 2 ≤ g := by linarith only [hg]
  let F := fun w : ℝ => -(w⁻¹) / (t * u)
  have hcont : ContinuousOn (fun w : ℝ => 1 / (t * u * w ^ 2)) (Icc (g / 2) g) := by
    apply continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
    intro w hw
    exact (mul_pos (mul_pos ht hu) (sq_pos_of_pos ((half_pos hg).trans_le hw.1))).ne'
  have hderiv : ∀ w ∈ uIcc (g / 2) g,
      HasDerivAt F (1 / (t * u * w ^ 2)) w := by
    intro w hw
    rw [uIcc_of_le hab] at hw
    have hwp : 0 < w := (half_pos hg).trans_le hw.1
    have hd := (hasDerivAt_inv hwp.ne').neg.div_const (t * u)
    apply hd.congr_deriv
    field_simp [ht.ne', hu.ne', hwp.ne'] <;> ring
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hab)]
  dsimp only [F]
  field_simp [ht.ne', hu.ne', hg.ne'] <;> ring

/-- Correct dictionary for 1/(t*u*w): the w integral is log two, not the
original residual denominator. This is an ordinary real Lebesgue integral. -/
theorem kernel_integral_eq_log_two_pair_integral :
    (∫ x in domain, kernel x) = Real.log (2 : ℝ) *
      ∫ t in Ico (19 / 125 : ℝ) (59 / 250 : ℝ),
        ∫ u in Ico (59 / 250 : ℝ) ((1 - t) / 2), 1 / (t * u) := by
  rw [setIntegral_domain_eq_nested kernel integrableOn_kernel_domain]
  calc
    _ = ∫ t in Ico (19 / 125 : ℝ) (59 / 250 : ℝ),
        ∫ u in Ico (59 / 250 : ℝ) ((1 - t) / 2), Real.log (2 : ℝ) / (t * u) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro t ht
      apply setIntegral_congr_fun measurableSet_Ico
      intro u hu
      have htp : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 19 / 125) ht.1
      have hup : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250) hu.1
      have hgp : 0 < 1 - t - u := by linarith only [ht.2, hu.2]
      simpa only [kernel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using
        inner_kernel_integral htp hup hgp
    _ = _ := by
      have hfactor (t u : ℝ) : Real.log (2 : ℝ) / (t * u) =
          Real.log (2 : ℝ) * (1 / (t * u)) := by ring
      simp_rw [hfactor, integral_const_mul]

/-- Correct dictionary for 1/(t*u*w^2): it is exactly the installed
original J, purely as a real integral identity. No prime density is asserted. -/
theorem squaredTerminalKernel_integral_eq_originalJ :
    (∫ x in domain, squaredTerminalKernel x) = currentChenUpsilon9HarmonicIntegral := by
  rw [setIntegral_domain_eq_nested squaredTerminalKernel integrableOn_squaredTerminalKernel_domain,
    currentChenUpsilon9HarmonicIntegral_eq_nested]
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  apply setIntegral_congr_fun measurableSet_Ico
  intro u hu
  have htp : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 19 / 125) ht.1
  have hup : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59 / 250) hu.1
  have hgp : 0 < 1 - t - u := by linarith only [ht.2, hu.2]
  simpa only [squaredTerminalKernel, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] using inner_squaredTerminalKernel_integral htp hup hgp

/-- The squared-kernel buffer converges to original J in this REAL-domain
dictionary only; it says nothing about fixed-eta unweighted prime counts. -/
theorem tendsto_squaredKernel_buffer_integral_originalJ :
    Filter.Tendsto (fun eta : ℝ => ∫ x in bufferDomain eta, squaredTerminalKernel x)
      (nhds 0) (nhds currentChenUpsilon9HarmonicIntegral) := by
  simpa only [squaredTerminalKernel_integral_eq_originalJ] using tendsto_squaredKernel_buffer_integral

theorem squaredTerminalKernel_weak_integral_eq_originalJ :
    (∫ x in weakDomain, squaredTerminalKernel x) = currentChenUpsilon9HarmonicIntegral := by
  rw [← setIntegral_domain_eq_weakDomain squaredTerminalKernel,
    squaredTerminalKernel_integral_eq_originalJ]

theorem tendsto_squaredKernel_continuous_ramps_originalJ (upper : Bool) :
    Filter.Tendsto (fun m : ℕ => ∫ x in cube,
      squaredTerminalKernel x * affinePrimeGateRamp forms bounds upper m x)
      Filter.atTop (nhds currentChenUpsilon9HarmonicIntegral) := by
  simpa only [squaredTerminalKernel_integral_eq_originalJ] using
    tendsto_squaredKernel_continuous_ramps upper

end

end ImbalancedChen.P5U9RealDomain
