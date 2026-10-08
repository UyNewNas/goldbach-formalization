import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Growth sufficient to absorb the receiver-one correction

This module supplies genuine analytic growth, independent of every prime-count
estimate. Mathlib's theorem that `exp x / x ^ 2` tends to infinity, composed
with `log`, proves that `N / (log N) ^ 2` tends to infinity. Consequently, an
eventual lower comparison on even integers by a fixed positive multiple of
this function is enough to absorb the additive unit in the `D12Omega` to
`D12` correction.

The lower comparison and its strictly positive constant remain explicit
hypotheses. In particular, this module neither defines a singular series nor
asserts a lower bound for one, and it assumes no estimates for target counts.
-/

namespace ImbalancedChen

open Filter

/-- Any real-valued function tending to positive infinity absorbs the unit
after multiplication by an arbitrary fixed positive epsilon. -/
theorem eventually_unit_absorption_of_tendsto
    {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, 1 ≤ epsilon * H N := by
  intro epsilon hepsilon
  exact (hH.const_mul_atTop hepsilon).eventually (eventually_ge_atTop 1)

/-- The all-integer divergence hypothesis implies the even-integer unit
absorption hypothesis used by the corrected asymptotic transfer. -/
theorem eventuallyEven_unit_absorption_of_tendsto
    {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N → 1 ≤ epsilon * H N := by
  intro epsilon hepsilon
  exact (eventually_unit_absorption_of_tendsto hH epsilon hepsilon).mono
    (fun _ hN _ => hN)

/-- A normalization need only dominate a divergent function on even integers;
no assertion about its values on odd integers is needed. -/
theorem eventuallyEven_unit_absorption_of_eventually_le
    {G H : ℕ → ℝ} (hG : Tendsto G atTop atTop)
    (hLower : ∀ᶠ N : ℕ in atTop, Even N → G N ≤ H N) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N → 1 ≤ epsilon * H N := by
  intro epsilon hepsilon
  refine ((eventually_unit_absorption_of_tendsto hG epsilon hepsilon).and hLower).mono ?_
  rintro N ⟨hAbsorbN, hLowerN⟩ hEven
  exact hAbsorbN.trans
    (mul_le_mul_of_nonneg_left (hLowerN hEven) hepsilon.le)

/-- The standard real-variable normalization grows to infinity. The proof
uses the proved exponential-versus-polynomial asymptotic from mathlib. -/
theorem tendsto_self_div_log_sq_atTop :
    Tendsto (fun x : ℝ => x / (Real.log x) ^ 2) atTop atTop := by
  have h := (Real.tendsto_exp_div_pow_atTop 2).comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply, Real.exp_log hx]

/-- Restriction of `x / (log x) ^ 2` to natural arguments still tends to
infinity. Its exceptional values at `0` and `1` do not affect the limit. -/
theorem tendsto_nat_div_log_sq_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ 2) atTop atTop := by
  exact tendsto_self_div_log_sq_atTop.comp tendsto_natCast_atTop_atTop

/-- Every fixed positive multiple of the standard normalization diverges. -/
theorem tendsto_pos_mul_nat_div_log_sq_atTop
    {c0 : ℝ} (hc0 : 0 < c0) :
    Tendsto (fun N : ℕ => c0 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2)
      atTop atTop := by
  simpa only [mul_div_assoc] using
    tendsto_nat_div_log_sq_atTop.const_mul_atTop hc0

/-- A positive lower factor times `N / (log N) ^ 2`, assumed only eventually
on even integers, supplies the exact unit-absorption premise required by the
receiver-one correction. The lower factor is a hypothesis, not an unproved
claim about a singular series. -/
theorem eventuallyEven_unit_absorption_of_log_sq_lower
    {H : ℕ → ℝ} {c0 : ℝ} (hc0 : 0 < c0)
    (hLower : ∀ᶠ N : ℕ in atTop, Even N →
      c0 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤ H N) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N → 1 ≤ epsilon * H N := by
  exact eventuallyEven_unit_absorption_of_eventually_le
    (tendsto_pos_mul_nat_div_log_sq_atTop hc0) hLower

end ImbalancedChen
