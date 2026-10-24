import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.RealHalfProductMassSplit

/-!
# Joint endpoint payment for the actual upper count

SOURCE ONLY / YELLOW / UNCOMPILED (2026-10-24).

Both endpoint errors in `RealUpperCountingAssembly` are paid from one
prescribed tolerance, after one natural threshold that also ensures `N >= 2`.
The sieve endpoint is the exact natural ceiling, and the product endpoint is
the literal manuscript cutoff plus its unit. The parameters and endpoint
coefficients are fixed before the tolerance and threshold are chosen.

Only proved power-error budgets are used. These theorems do not require a
density estimate, distribution estimate, sieve gate, positive lower bound on
`theta`, parity restriction, or any other analytic premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- One common eventual budget for any fixed nonnegative endpoint weights.
The denominator remains positive even when both weights vanish. -/
theorem eventually_weighted_joint_upper_endpoint_budget
    {kappa theta : ℝ} (hkappa : 0 < kappa) (htheta : theta < 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧
        a * (Nat.ceil ((N : ℝ) ^ theta) : ℝ) +
          b * (manuscriptHalfProductCutoff kappa N + 1) ≤
            eta * singularNormalization N := by
  let denominator : ℝ := a + b + 1
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    linarith
  let epsilon : ℝ := eta / denominator
  have hepsilon : 0 < epsilon := div_pos heta hdenominator
  have hpayment : epsilon * denominator = eta := by
    dsimp [epsilon]
    field_simp [ne_of_gt hdenominator]
  have hcoefficient : (a + b) * epsilon ≤ eta := by
    calc
      (a + b) * epsilon ≤ denominator * epsilon := by
        apply mul_le_mul_of_nonneg_right _ hepsilon.le
        dsimp [denominator]
        linarith
      _ = eta := by rw [mul_comm]; exact hpayment
  have hceil : ∀ᶠ N : ℕ in atTop,
      (Nat.ceil ((N : ℝ) ^ theta) : ℝ) ≤
        epsilon * singularNormalization N := by
    simpa only [one_mul, pow_zero, mul_one] using
      eventually_ceil_powerLog_le_singularNormalization 1 theta 0
        (by norm_num) htheta epsilon hepsilon
  have hcutoff : ∀ᶠ N : ℕ in atTop,
      manuscriptHalfProductCutoff kappa N + 1 ≤
        epsilon * singularNormalization N := by
    simpa only [manuscriptHalfProductCutoff, pow_zero, mul_one] using
      eventually_powerLog_add_one_le_singularNormalization 2 (1 - kappa) 0
        (by linarith) epsilon hepsilon
  filter_upwards [hceil, hcutoff, eventually_ge_atTop (2 : ℕ)]
    with N hceilN hcutoffN hN
  have hnormalization : 0 ≤ singularNormalization N := by
    unfold singularNormalization
    exact div_nonneg
      (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N))
      (sq_nonneg _)
  refine ⟨hN, ?_⟩
  calc
    a * (Nat.ceil ((N : ℝ) ^ theta) : ℝ) +
        b * (manuscriptHalfProductCutoff kappa N + 1) ≤
        a * (epsilon * singularNormalization N) +
          b * (epsilon * singularNormalization N) :=
      add_le_add (mul_le_mul_of_nonneg_left hceilN ha)
        (mul_le_mul_of_nonneg_left hcutoffN hb)
    _ = ((a + b) * epsilon) * singularNormalization N := by ring
    _ ≤ eta * singularNormalization N :=
      mul_le_mul_of_nonneg_right hcoefficient hnormalization

/-- The two exact endpoints together cost at most `eta`, with `N >= 2`
included in the same eventual statement. -/
theorem eventually_joint_upper_endpoint_budget
    {kappa theta : ℝ} (hkappa : 0 < kappa) (htheta : theta < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧
        (Nat.ceil ((N : ℝ) ^ theta) : ℝ) +
          (manuscriptHalfProductCutoff kappa N + 1) ≤
            eta * singularNormalization N := by
  simpa only [one_mul] using
    eventually_weighted_joint_upper_endpoint_budget hkappa htheta
      1 1 (by norm_num) (by norm_num) eta heta

/-- Complete weighted supplier with one natural threshold. No analytic
estimate is an input; the threshold is uniform over all later natural `N`. -/
theorem exists_weighted_joint_upper_endpoint_threshold
    {kappa theta : ℝ} (hkappa : 0 < kappa) (htheta : theta < 1)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      a * (Nat.ceil ((N : ℝ) ^ theta) : ℝ) +
        b * (manuscriptHalfProductCutoff kappa N + 1) ≤
          eta * singularNormalization N := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_weighted_joint_upper_endpoint_budget hkappa htheta a b ha hb eta heta)
  refine ⟨max M 2, le_max_right _ _, ?_⟩
  intro N hN
  exact (hM N (le_trans (le_max_left _ _) hN)).2

/-- A complete supplier for the literal pair of upper-count endpoints.
`kappa` and `theta` are fixed before `eta`; the sole returned threshold
already includes the `N >= 2` requirement of the counting assembly. -/
theorem exists_joint_upper_endpoint_threshold
    {kappa theta : ℝ} (hkappa : 0 < kappa) (htheta : theta < 1) :
    ∀ eta : ℝ, 0 < eta →
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        (Nat.ceil ((N : ℝ) ^ theta) : ℝ) +
          (manuscriptHalfProductCutoff kappa N + 1) ≤
            eta * singularNormalization N := by
  intro eta heta
  simpa only [one_mul] using
    exists_weighted_joint_upper_endpoint_threshold hkappa htheta
      1 1 (by norm_num) (by norm_num) eta heta

end

end ImbalancedChen
