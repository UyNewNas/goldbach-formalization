import ImbalancedChen.Part3GeneralComplexISeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
Native derivative-series proof for the literal Gamma-normalized general
complex I core. The order is genuinely complex, with -1 < Re nu.
The derivative majorant is supplied by the already proved absolute core
convergence at shifted order nu+1; no derivative or ODE is assumed.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.GeneralICoreDifferential20261025a

noncomputable section
open scoped BigOperators
open GeneralComplexISeriesSourceOnly

/-- Factorial cancellation shifts one derivative to one unit of complex
order. Gamma itself need not be nonzero for this identity. -/
theorem generalICoeff_derivative_shift (nu : ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * generalICoeff nu (n + 1) =
      generalICoeff (nu + 1) n := by
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hg : ((n + 1 : ℕ) : ℂ) + nu + 1 = (n : ℂ) + (nu + 1) + 1 := by
    push_cast
    ring
  simp only [generalICoeff, Nat.factorial_succ, Nat.cast_mul, hg, mul_inv]
  simp only [mul_assoc, mul_inv_cancel_left₀ hn]

/-- The actual Gamma recurrence, written as a recurrence in complex order. -/
theorem generalICoeff_order_recurrence (nu : ℂ) (n : ℕ) :
    ((n : ℂ) + nu + 1) * generalICoeff (nu + 1) n = generalICoeff nu n := by
  rw [← generalICoeff_derivative_shift nu n]
  convert generalICoeff_recurrence nu n using 1 <;> ring

private theorem shifted_order {nu : ℂ} (hnu : -1 < nu.re) :
    -1 < (nu + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  linarith

private theorem core_tail {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    generalICore nu z = generalICoeff nu 0 +
      ∑' n : ℕ, generalICoeff nu (n + 1) * z ^ (n + 1) := by
  have h := Summable.sum_add_tsum_nat_add 1 (generalICore_hasSum hnu z).summable
  simpa only [Finset.sum_range_one, pow_zero, mul_one, generalICore] using h.symm

/-- The actual core is differentiable by the native locally uniform
termwise derivative theorem on a complex disk around the evaluation point. -/
theorem generalICore_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    HasDerivAt (generalICore nu) (generalICore (nu + 1) z) z := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hnu1 := shifted_order hnu
  have hu : Summable (fun n : ℕ => ‖generalICoeff (nu + 1) n‖ * R ^ n) :=
    summable_norm_generalICoeff_mul_pow hnu1 R hR.le
  have hterm : ∀ (n : ℕ) (w : ℂ),
      HasDerivAt (fun x : ℂ => generalICoeff nu (n + 1) * x ^ (n + 1))
        (generalICoeff (nu + 1) n * w ^ n) w := by
    intro n w
    have h := ((hasDerivAt_id w).pow (n + 1)).const_mul
      (generalICoeff nu (n + 1))
    convert h using 1
    · funext x
      rfl
    · rw [← generalICoeff_derivative_shift nu n]
      simp only [Nat.add_sub_cancel, mul_one]
      ring
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) R →
      ‖generalICoeff (nu + 1) n * w ^ n‖ ≤
        ‖generalICoeff (nu + 1) n‖ * R ^ n := by
    intro n w hw
    have hwR : ‖w‖ ≤ R := by
      have h : ‖w‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hw
      exact h.le
    simp only [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hwR n)
      (norm_nonneg _)
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    simpa only [Metric.mem_ball, dist_zero_right, R] using lt_add_one ‖z‖
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by simpa using hR
  have hs0 : Summable (fun n : ℕ =>
      generalICoeff nu (n + 1) * (0 : ℂ) ^ (n + 1)) := by simp
  have ht := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun n w _ => hterm n w) hbound hzero hs0 hz
  have htailfun : generalICore nu = fun w : ℂ =>
      generalICoeff nu 0 + ∑' n : ℕ, generalICoeff nu (n + 1) * w ^ (n + 1) := by
    funext w
    exact core_tail hnu w
  rw [htailfun]
  simpa only [zero_add, generalICore] using
    (hasDerivAt_const z (generalICoeff nu 0)).add ht

theorem deriv_generalICore {nu : ℂ} (hnu : -1 < nu.re) :
    deriv (generalICore nu) = generalICore (nu + 1) := by
  funext z
  exact (generalICore_hasDerivAt hnu z).deriv

/-- The coefficient recurrence is summed with its zero term and shifted
tail retained explicitly. This is the actual contiguous core identity. -/
theorem generalICore_contiguous {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    generalICore nu z = (nu + 1) * generalICore (nu + 1) z +
      z * generalICore (nu + 1 + 1) z := by
  have hnu1 := shifted_order hnu
  have hnu2 := shifted_order hnu1
  have hs1 : Summable (fun n : ℕ =>
      generalICoeff (nu + 1) (n + 1) * z ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (generalICore_hasSum hnu1 z).summable
  have hterm : ∀ n : ℕ,
      generalICoeff nu (n + 1) * z ^ (n + 1) =
        (nu + 1) * (generalICoeff (nu + 1) (n + 1) * z ^ (n + 1)) +
          z * (generalICoeff (nu + 1 + 1) n * z ^ n) := by
    intro n
    rw [← generalICoeff_order_recurrence nu (n + 1),
      ← generalICoeff_derivative_shift (nu + 1) n, pow_succ]
    push_cast
    ring
  have htail : (∑' n : ℕ, generalICoeff nu (n + 1) * z ^ (n + 1)) =
      (nu + 1) * (∑' n : ℕ, generalICoeff (nu + 1) (n + 1) * z ^ (n + 1)) +
        z * generalICore (nu + 1 + 1) z := by
    have heq : (fun n : ℕ => generalICoeff nu (n + 1) * z ^ (n + 1)) =
        (fun n : ℕ => (nu + 1) *
          (generalICoeff (nu + 1) (n + 1) * z ^ (n + 1)) +
            z * (generalICoeff (nu + 1 + 1) n * z ^ n)) := funext hterm
    rw [heq]
    exact ((hs1.hasSum.mul_left (nu + 1)).add
      ((generalICore_hasSum hnu2 z).mul_left z)).tsum_eq
  rw [core_tail hnu z, core_tail hnu1 z, htail]
  have hzero := generalICoeff_order_recurrence nu 0
  norm_num at hzero
  rw [← hzero]
  ring

/-- The native complex second derivative solves the core differential
identity zH''+(nu+1)H'-H=0, with no derivative or ODE supplier premise. -/
theorem generalICore_ODE {nu : ℂ} (hnu : -1 < nu.re) (z : ℂ) :
    z * deriv (deriv (generalICore nu)) z +
      (nu + 1) * deriv (generalICore nu) z - generalICore nu z = 0 := by
  rw [deriv_generalICore hnu, deriv_generalICore (shifted_order hnu)]
  have h := generalICore_contiguous hnu z
  linear_combination -h

end
end ImbalancedChen.Part3.GeneralICoreDifferential20261025a