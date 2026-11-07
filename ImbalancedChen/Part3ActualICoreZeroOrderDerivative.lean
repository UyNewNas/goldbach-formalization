import ImbalancedChen.Part3GeneralIOrderHolomorphy
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The genuine mixed analytic primitive needed at order zero. The actual
order derivative of the reciprocal-Gamma I core is identified with the
series of actual coefficient order derivatives. Cauchy estimates on
the already proved compact order-ball majorants give a summable bound
for those differentiated coefficients on every core-argument ball.
Consequently the actual order derivative at zero is entire in the
complex core argument. No mixed derivative or joint holomorphy is a
supplier assumption.
-/

namespace ImbalancedChen.Part3.ActualICoreZeroOrderDerivative20261026b

noncomputable section
open Set Filter Metric
open scoped Topology
open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly

def coefficientOrderDerivativeZero (n : ℕ) : ℂ :=
  deriv (fun nu : ℂ => generalICoeff nu n) 0

def coreOrderDerivativeZero (z : ℂ) : ℂ :=
  deriv (fun nu : ℂ => generalICore nu z) 0

def coreOrderDerivativeSeriesZero (z : ℂ) : ℂ :=
  ∑' n, coefficientOrderDerivativeZero n * z ^ n

theorem coefficient_order_derivative_mul (n : ℕ) (z : ℂ) :
    deriv (fun nu : ℂ => generalICoeff nu n * z ^ n) 0 =
      coefficientOrderDerivativeZero n * z ^ n := by
  exact ((differentiable_generalICoeff_order n 0).hasDerivAt.mul_const (z ^ n)).deriv

/-- The actual order derivative is the true differentiated coefficient
series, from the existing local normal convergence in the order variable. -/
theorem coreOrderDerivativeZero_hasSum (z : ℂ) :
    HasSum (fun n => coefficientOrderDerivativeZero n * z ^ n) (coreOrderDerivativeZero z) := by
  obtain ⟨r, hr, u, hu, hb⟩ := exists_generalICore_order_ball_majorant 0 z (by norm_num)
  have hs := Complex.hasSum_deriv_of_summable_norm
    (F := fun n nu => generalICoeff nu n * z ^ n) (U := ball (0 : ℂ) r) hu
    (fun n => ((differentiable_generalICoeff_order n).mul_const (z ^ n)).differentiableOn)
    isOpen_ball (fun n nu hnu => (hb nu (ball_subset_closedBall hnu)).2 n) (mem_ball_self hr)
  simpa only [coefficient_order_derivative_mul, coreOrderDerivativeZero, generalICore] using hs

theorem coreOrderDerivativeZero_eq_series (z : ℂ) :
    coreOrderDerivativeZero z = coreOrderDerivativeSeriesZero z :=
  (coreOrderDerivativeZero_hasSum z).tsum_eq.symm

/-- A genuine Cauchy bound for all differentiated coefficients at each
chosen argument radius. Its summable majorant is constructed from the
actual compact order-ball majorant, rather than supplied independently. -/
theorem exists_coefficientOrderDerivativeZero_majorant (R : ℝ) (hR : 0 ≤ R) :
    ∃ v : ℕ → ℝ, Summable v ∧ ∀ n,
      ‖coefficientOrderDerivativeZero n‖ * R ^ n ≤ v n := by
  obtain ⟨r, hr, u, hu, hb⟩ := exists_generalICore_order_ball_majorant 0 (R : ℂ) (by norm_num)
  refine ⟨fun n => u n / r, ?_, ?_⟩
  · simpa only [div_eq_mul_inv] using hu.mul_right r⁻¹
  · intro n
    have hd : DifferentiableOn ℂ (fun nu : ℂ => generalICoeff nu n * (R : ℂ) ^ n)
        (closedBall (0 : ℂ) r) :=
      ((differentiable_generalICoeff_order n).mul_const ((R : ℂ) ^ n)).differentiableOn
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      (hd.diffContOnCl_ball (Subset.refl _))
      (fun nu hnu => (hb nu (sphere_subset_closedBall hnu)).2 n)
    rw [coefficient_order_derivative_mul] at hcauchy
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR] using hcauchy

/-- The differentiated coefficient series is entire in the core argument. -/
theorem coreOrderDerivativeSeriesZero_analyticAt (z : ℂ) :
    AnalyticAt ℂ coreOrderDerivativeSeriesZero z := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨v, hv, hbound⟩ := exists_coefficientOrderDerivativeZero_majorant R hR.le
  have hd : DifferentiableOn ℂ coreOrderDerivativeSeriesZero (ball (0 : ℂ) R) := by
    apply Complex.differentiableOn_tsum_of_summable_norm hv
    · intro n
      exact ((differentiable_id.pow n).const_mul (coefficientOrderDerivativeZero n)).differentiableOn
    · exact isOpen_ball
    · intro n w hw
      have hwR : ‖w‖ ≤ R := by simpa only [dist_zero_right] using (mem_ball.mp hw).le
      calc
        ‖coefficientOrderDerivativeZero n * w ^ n‖ =
            ‖coefficientOrderDerivativeZero n‖ * ‖w‖ ^ n := by rw [norm_mul, norm_pow]
        _ ≤ ‖coefficientOrderDerivativeZero n‖ * R ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg w) hwR n) (norm_nonneg _)
        _ ≤ _ := hbound n
  have hz : z ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  exact hd.analyticAt (isOpen_ball.mem_nhds hz)

/-- Actual mixed derivative holomorphy at the zero order, obtained from
the differentiated normal series and its Cauchy bounds. -/
theorem coreOrderDerivativeZero_analyticAt (z : ℂ) :
    AnalyticAt ℂ coreOrderDerivativeZero z := by
  have he : coreOrderDerivativeZero = coreOrderDerivativeSeriesZero :=
    funext coreOrderDerivativeZero_eq_series
  rw [he]
  exact coreOrderDerivativeSeriesZero_analyticAt z

theorem coreOrderDerivativeZero_analyticOnNhd : AnalyticOnNhd ℂ coreOrderDerivativeZero univ :=
  fun z _ => coreOrderDerivativeZero_analyticAt z

end
end ImbalancedChen.Part3.ActualICoreZeroOrderDerivative20261026b
