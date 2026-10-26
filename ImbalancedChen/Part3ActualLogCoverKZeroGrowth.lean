import ImbalancedChen.Part3ActualLogCoverIPoissonGrowth
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Honest zero-order growth for the independently defined logarithmic-cover
K0. A lower real-order Poisson weight dominates every complex order in
a genuine closed order ball of radius r<1/2. Reciprocal-Gamma continuity
gives one compact normalization bound. This proves an actual order-ball
I bound, uniform over the whole half-log phase band. Cauchy's derivative
estimate then bounds the actual order derivative at zero, already proved
equal to the independent K0 cover. The resulting growth is explicitly
polynomial in the physical argument norm times exp(|Re(q)|), q=2exp(L).
No singular pi/sin(0), order-limit interchange, growth hypothesis, or
large-sector Macdonald identity is used.
-/

namespace ImbalancedChen.Part3.ActualLogCoverKZeroGrowth20261026b

noncomputable section
open Set MeasureTheory Metric
open GeneralJSymmetricPoissonIntegralSourceOnly
open ActualComplexIPoissonCore20261026b ActualLogCoverKModel20261026b
open ActualLogCoverIPoissonGrowth20261026b

theorem symmetricPoissonWeight_real_base (nu : ℂ) (t : ℝ) :
    jSymmetricPoissonWeight nu t = ((1 - t ^ 2 : ℝ) : ℂ) ^ (nu - 1 / 2) := by
  simp only [jSymmetricPoissonWeight, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]

/-- The endpoint weight bound is uniform over complex orders with a
fixed real-order floor; imaginary order does not affect this norm. -/
theorem symmetricPoissonWeight_norm_le_order_floor {nu : ℂ} {sigma t : ℝ}
    (hfloor : sigma ≤ nu.re) (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ‖jSymmetricPoissonWeight nu t‖ ≤ ‖jSymmetricPoissonWeight (sigma : ℂ) t‖ := by
  have hx : 0 < 1 - t ^ 2 := by
    have ha := abs_lt.mpr ht
    nlinarith [sq_abs t, abs_nonneg t]
  simp only [symmetricPoissonWeight_real_base]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hn : (nu - 1 / 2).re = nu.re - 1 / 2 := by norm_num
  have hs : ((sigma : ℂ) - 1 / 2).re = sigma - 1 / 2 := by norm_num
  rw [hn, hs]
  exact Real.rpow_le_rpow_of_exponent_ge hx (by nlinarith [sq_nonneg t]) (by linarith)

theorem complexIPoissonIntegral_norm_le_order_floor {nu : ℂ} {sigma : ℝ}
    (hsigma : -(1 / 2 : ℝ) < sigma) (hfloor : sigma ≤ nu.re) (z : ℂ) :
    ‖complexIPoissonIntegral nu z‖ ≤
      Real.exp |z.re| * complexIPoissonNormMass (sigma : ℂ) := by
  have hw := symmetricPoissonWeight_integrableOn (nu := (sigma : ℂ)) (by simpa using hsigma)
  have h := norm_integral_le_of_norm_le (hw.norm.const_mul (Real.exp |z.re|))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (complexIPoissonDensity_norm_le nu z ht).trans
        (mul_le_mul_of_nonneg_left (symmetricPoissonWeight_norm_le_order_floor hfloor ht)
          (Real.exp_pos _).le))
  simpa only [complexIPoissonIntegral, integral_const_mul, complexIPoissonNormMass] using h

theorem order_ball_component_bounds {nu : ℂ} {r : ℝ}
    (hnu : nu ∈ closedBall (0 : ℂ) r) : |nu.re| ≤ r ∧ |nu.im| ≤ r := by
  have hn : ‖nu‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hnu
  exact ⟨(Complex.abs_re_le_norm nu).trans hn, (Complex.abs_im_le_norm nu).trans hn⟩

/-- A genuine uniform order-ball bound for the literal I cover. All
constants are derived from the actual Poisson weight and reciprocal
Gamma on the compact order ball; none is a supplied growth envelope. -/
theorem exists_logCoverI_order_ball_growth {r T : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ nu ∈ closedBall (0 : ℂ) r, ∀ L : ℂ, |L.im| ≤ T →
      ‖logCoverI nu L‖ ≤ C * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| := by
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    inversePoissonGammaNormalization_continuous.continuousOn
  let M : ℝ := max M₀ 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right M₀ 0]
  have hM₀M : M₀ ≤ M := by dsimp [M]; linarith [le_max_left M₀ 0]
  let W : ℝ := complexIPoissonNormMass ((-r : ℝ) : ℂ)
  have hW : 0 ≤ W := complexIPoissonNormMass_nonneg _
  let C : ℝ := M * W * Real.exp (r * T) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro nu hnu L hphase
  rcases order_ball_component_bounds hnu with ⟨hre, him⟩
  have hfloor : -r ≤ nu.re := (abs_le.mp hre).1
  have hn : -(1 / 2 : ℝ) < nu.re := by linarith
  have hgamma : ‖(poissonGammaNormalization nu)⁻¹‖ ≤ M := (hM₀ nu hnu).trans hM₀M
  have hP := complexIPoissonIntegral_norm_le_order_floor
    (by linarith : -(1 / 2 : ℝ) < -r) hfloor (coverPhysicalArgument L)
  have hreL : nu.re * L.re ≤ r * |L.re| := by
    calc
      _ ≤ |nu.re * L.re| := le_abs_self _
      _ = |nu.re| * |L.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  have himL : -nu.im * L.im ≤ r * T := by
    calc
      _ ≤ |nu.im * L.im| := by simpa only [neg_mul] using neg_le_abs (nu.im * L.im)
      _ = |nu.im| * |L.im| := abs_mul _ _
      _ ≤ _ := mul_le_mul him hphase (abs_nonneg _) hr.le
  have hexp : (nu * L).re ≤ r * |L.re| + r * T := by rw [Complex.mul_re]; linarith
  have hE := Real.exp_le_exp.mpr hexp
  rw [logCoverI_eq_poisson hn L, div_eq_mul_inv, norm_mul, norm_mul, Complex.norm_exp]
  calc
    _ ≤ (Real.exp (r * |L.re| + r * T) * M) *
        (Real.exp |(coverPhysicalArgument L).re| * W) := by
      exact mul_le_mul (mul_le_mul hE hgamma (norm_nonneg _) (Real.exp_pos _).le)
        hP (norm_nonneg _) (by positivity)
    _ = (M * W * Real.exp (r * T)) * Real.exp (r * |L.re|) *
        Real.exp |(coverPhysicalArgument L).re| := by rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| := by
      have hbase : M * W * Real.exp (r * T) ≤ C := by dsimp [C]; linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbase (Real.exp_pos _).le) (Real.exp_pos _).le

/-- The zero-order bound is an actual Cauchy estimate for the genuine
order derivative. It uses the independent K0 model identity and never
evaluates the nonintegral sine quotient at zero. -/
theorem exists_logCoverKZero_half_log_growth {r T : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℂ, |L.im| ≤ T →
      ‖logCoverKZero L‖ ≤ C * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| := by
  obtain ⟨C, hC, hI⟩ := exists_logCoverI_order_ball_growth hr hrhalf hT
  refine ⟨C / r, div_pos hC hr, ?_⟩
  intro L hphase
  have hd : DifferentiableOn ℂ (fun nu : ℂ => logCoverI nu L) (closedBall (0 : ℂ) r) := by
    intro nu hnu
    have hre := (order_ball_component_bounds hnu).1
    have hfloor := (abs_le.mp hre).1
    have hn : -1 < nu.re := by linarith
    exact (logCoverI_order_analyticAt nu L hn).differentiableAt.differentiableWithinAt
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hd.diffContOnCl_ball (Subset.refl _))
    (fun nu hnu => hI nu (sphere_subset_closedBall hnu) L hphase)
  calc
    ‖logCoverKZero L‖ = ‖deriv (fun nu : ℂ => logCoverI nu L) 0‖ := by
      rw [logCoverKZero_eq_neg_order_deriv, norm_neg]
    _ ≤ (C * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re|) / r := hcauchy
    _ = _ := by ring

theorem half_log_growth_le_physical_powers {r : ℝ} (hr : 0 ≤ r) (L : ℂ) :
    Real.exp (r * |L.re|) ≤ Real.exp (r * |Real.log 2|) *
      (‖coverPhysicalArgument L‖ ^ r + ‖coverPhysicalArgument L‖ ^ (-r)) := by
  let x : ℝ := Real.log ‖coverPhysicalArgument L‖
  have hL : L.re = x - Real.log 2 := by dsimp [x]; rw [coverPhysicalArgument_log_norm]; ring
  have habs : |L.re| ≤ |x| + |Real.log 2| := by
    rw [hL]
    exact abs_sub x (Real.log 2)
  have hradial : Real.exp (r * |x|) ≤
      ‖coverPhysicalArgument L‖ ^ r + ‖coverPhysicalArgument L‖ ^ (-r) := by
    rw [Real.rpow_def_of_pos (coverPhysicalArgument_norm_pos L),
      Real.rpow_def_of_pos (coverPhysicalArgument_norm_pos L)]
    change Real.exp (r * |x|) ≤ Real.exp (x * r) + Real.exp (x * (-r))
    by_cases hx : 0 ≤ x
    · calc
        _ = Real.exp (x * r) := by rw [abs_of_nonneg hx]; congr 1; ring
        _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
    · have hx' : x ≤ 0 := le_of_not_ge hx
      calc
        _ = Real.exp (x * (-r)) := by rw [abs_of_nonpos hx']; congr 1; ring
        _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    _ ≤ Real.exp (r * (|x| + |Real.log 2|)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hr)
    _ = Real.exp (r * |x|) * Real.exp (r * |Real.log 2|) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ (‖coverPhysicalArgument L‖ ^ r + ‖coverPhysicalArgument L‖ ^ (-r)) *
        Real.exp (r * |Real.log 2|) := mul_le_mul_of_nonneg_right hradial (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- Actual zero-order polynomial/exponential growth in the physical
argument norm, uniformly on every bounded half-log phase band. -/
theorem exists_logCoverKZero_radial_growth {r T : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℂ, |L.im| ≤ T →
      ‖logCoverKZero L‖ ≤ C *
        (‖coverPhysicalArgument L‖ ^ r + ‖coverPhysicalArgument L‖ ^ (-r)) *
          Real.exp |(coverPhysicalArgument L).re| := by
  obtain ⟨C, hC, hzero⟩ := exists_logCoverKZero_half_log_growth hr hrhalf hT
  refine ⟨C * Real.exp (r * |Real.log 2|), mul_pos hC (Real.exp_pos _), ?_⟩
  intro L hphase
  calc
    _ ≤ C * Real.exp (r * |L.re|) * Real.exp |(coverPhysicalArgument L).re| := hzero L hphase
    _ ≤ C * (Real.exp (r * |Real.log 2|) *
        (‖coverPhysicalArgument L‖ ^ r + ‖coverPhysicalArgument L‖ ^ (-r))) *
          Real.exp |(coverPhysicalArgument L).re| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (half_log_growth_le_physical_powers hr.le L) hC.le)
        (Real.exp_pos _).le
    _ = _ := by ring

theorem exists_logCoverK_zero_radial_growth {r T : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℂ, |L.im| ≤ T →
      ‖logCoverK 0 L‖ ≤ C *
        (‖coverPhysicalArgument L‖ ^ r + ‖coverPhysicalArgument L‖ ^ (-r)) *
          Real.exp |(coverPhysicalArgument L).re| := by
  simpa only [logCoverK, if_pos rfl] using exists_logCoverKZero_radial_growth hr hrhalf hT

end
end ImbalancedChen.Part3.ActualLogCoverKZeroGrowth20261026b
