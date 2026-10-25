import ImbalancedChen.Part3GeneralComplexISeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Order holomorphy of the literal general complex-order modified-I function.
Local summable bounds are derived from the Gamma coefficient estimate and
compactness; no uniform-convergence or holomorphy supplier is assumed.
SOURCE ONLY, UNCOMPILED, NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace ImbalancedChen.Part3.GeneralIOrderHolomorphySourceOnly

open GeneralComplexISeriesSourceOnly

theorem differentiable_generalICoeff_order (n : ℕ) :
    Differentiable ℂ (fun nu => generalICoeff nu n) := by
  have hg : Differentiable ℂ (fun nu : ℂ =>
      (Complex.Gamma ((n : ℂ) + nu + 1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp
      (((differentiable_const (n : ℂ)).add differentiable_id).add
        (differentiable_const 1))
  simpa only [generalICoeff, mul_inv_rev] using
    hg.mul_const ((n.factorial : ℂ)⁻¹)

/-- A uniform coefficient majorant on an actual closed order ball, proved
from reciprocal-Gamma continuity and the previously proved coefficient bound. -/
theorem exists_generalICore_order_ball_majorant (nu₀ z : ℂ)
    (hnu₀ : -1 < nu₀.re) :
    ∃ r > 0, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ nu ∈ Metric.closedBall nu₀ r,
        -1 < nu.re ∧ ∀ n, ‖generalICoeff nu n * z ^ n‖ ≤ u n := by
  let r : ℝ := (nu₀.re + 1) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hc : Continuous (fun nu : ℂ => (Complex.Gamma (nu + 1))⁻¹) :=
    (Complex.differentiable_one_div_Gamma.comp
      (differentiable_id.add (differentiable_const 1))).continuous
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall nu₀ r).exists_bound_of_continuousOn
    hc.continuousOn
  let C := max C₀ 0
  let u : ℕ → ℝ := fun n => C * ((‖z‖ / r) ^ n / (n.factorial : ℝ))
  have hu : Summable u := (Real.summable_pow_div_factorial (‖z‖ / r)).mul_left C
  refine ⟨r, hr, u, hu, ?_⟩
  intro nu hnu
  have hnorm : ‖nu - nu₀‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hnu
  have hre : |nu.re - nu₀.re| ≤ r := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (nu - nu₀)).trans hnorm
  have hdelta : r ≤ nu.re + 1 := by
    have := (abs_le.mp hre).1
    dsimp [r] at *
    linarith
  have hnu' : -1 < nu.re := by linarith
  refine ⟨hnu', fun n => ?_⟩
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hden : r ^ n * (n.factorial : ℝ) ≤
      (nu.re + 1) ^ n * (n.factorial : ℝ) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hdelta n) hf.le
  have hcoeff : ‖generalICoeff nu n‖ ≤ C / (r ^ n * (n.factorial : ℝ)) := by
    calc
      ‖generalICoeff nu n‖ ≤ ‖(Complex.Gamma (nu + 1))⁻¹‖ /
          ((nu.re + 1) ^ n * (n.factorial : ℝ)) := generalICoeff_norm_le hnu' n
      _ ≤ ‖(Complex.Gamma (nu + 1))⁻¹‖ / (r ^ n * (n.factorial : ℝ)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos (pow_pos hr _) hf) hden
      _ ≤ C / (r ^ n * (n.factorial : ℝ)) :=
        div_le_div_of_nonneg_right ((hC₀ nu hnu).trans (le_max_left _ _))
          (mul_nonneg (pow_nonneg hr.le _) hf.le)
  calc
    ‖generalICoeff nu n * z ^ n‖ = ‖generalICoeff nu n‖ * ‖z‖ ^ n := by
      rw [norm_mul, norm_pow]
    _ ≤ (C / (r ^ n * (n.factorial : ℝ))) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (norm_nonneg z) _)
    _ = u n := by
      dsimp [u]
      rw [div_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Actual local uniform convergence in the order variable. -/
theorem exists_generalICore_order_uniform_ball (nu₀ z : ℂ)
    (hnu₀ : -1 < nu₀.re) :
    ∃ r > 0, TendstoUniformlyOn
      (fun N nu => ∑ n ∈ Finset.range N, generalICoeff nu n * z ^ n)
      (fun nu => generalICore nu z) atTop (Metric.closedBall nu₀ r) := by
  obtain ⟨r, hr, u, hu, hb⟩ := exists_generalICore_order_ball_majorant nu₀ z hnu₀
  exact ⟨r, hr, tendstoUniformlyOn_tsum_nat hu (fun n nu hnu => (hb nu hnu).2 n)⟩

theorem analyticAt_generalICore_order (nu z : ℂ) (hnu : -1 < nu.re) :
    AnalyticAt ℂ (fun mu => generalICore mu z) nu := by
  obtain ⟨r, hr, u, hu, hb⟩ := exists_generalICore_order_ball_majorant nu z hnu
  have hd : DifferentiableOn ℂ (fun mu => generalICore mu z) (Metric.ball nu r) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
    · intro n
      exact ((differentiable_generalICoeff_order n).mul_const (z ^ n)).differentiableOn
    · exact Metric.isOpen_ball
    · intro n mu hmu
      exact (hb mu (Metric.ball_subset_closedBall hmu)).2 n
  exact hd.analyticAt (Metric.ball_mem_nhds nu hr)

theorem analyticOnNhd_generalICore_order (z : ℂ) :
    AnalyticOnNhd ℂ (fun nu => generalICore nu z) {nu : ℂ | -1 < nu.re} :=
  fun nu hnu => analyticAt_generalICore_order nu z hnu

/-- Holomorphy in the genuine complex order of the literal I function for
each positive q, with the canonical principal complex-power prefactor. -/
theorem analyticAt_generalI_order (nu : ℂ) (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    AnalyticAt ℂ (fun mu => generalI mu q) nu := by
  have hbase : (((q / 2 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (div_pos hq (by norm_num)))
  have hp : Differentiable ℂ (fun mu : ℂ => (((q / 2 : ℝ) : ℂ) ^ mu)) :=
    differentiable_id.const_cpow (Or.inl hbase)
  exact (hp.analyticAt nu).mul
    (analyticAt_generalICore_order nu ((((q / 2 : ℝ) : ℂ)) ^ 2) hnu)

theorem analyticOnNhd_generalI_order {q : ℝ} (hq : 0 < q) :
    AnalyticOnNhd ℂ (fun nu => generalI nu q) {nu : ℂ | -1 < nu.re} :=
  fun nu hnu => analyticAt_generalI_order nu hnu hq

end ImbalancedChen.Part3.GeneralIOrderHolomorphySourceOnly
