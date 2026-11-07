import ImbalancedChen.AsymptoticTransfer
import ImbalancedChen.RationalPowers
import ImbalancedChen.Constants

/-!
# Conditional numerical applications of the transfer lemmas

This file combines the exact logarithmic gaps from `Constants`, the corrected
asymptotic transfer from the manuscript's `D12Omega` count, and the equivalence
between the integer-power and real-power imbalance conditions.

Both conclusions are conditional. Their hypotheses explicitly require lower
estimates for the actual `D12Omega` count, upper estimates for the actual bad
count `B`, and growth of the normalization sufficient to absorb the possible
receiver-one contribution. No theorem here establishes these analytic
estimates, validates their quoted coefficients as sieve constants, or proves
the manuscript's unconditional main theorem.

All eventual estimates and conclusions are restricted to even integers. The
output `RealDb` counts each additive prime once using the literal real-power
receiver condition.
-/

namespace ImbalancedChen

/-- Conditional separate-input application at the real exponent `76407/100000`.
The explicit actual-count hypotheses and normalization-growth hypothesis imply
the lower bound `H N / 1000` for sufficiently large even `N`. -/
theorem eventually_RealDb_76407_lower_of_omega_bounds
    {H : ℕ → ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N)
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        ((18271 : ℝ) / 10000 - epsilon) * H N ≤ (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 76407 100000 N : ℝ) ≤
          ((3393 / 500 : ℝ) * Real.log (100000 / 76407) + epsilon) * H N) :
    ∀ᶠ N in Filter.atTop, Even N →
      H N / 1000 ≤ (RealDb (76407 / 100000 : ℝ) N : ℝ) := by
  have hTransfer :=
    eventually_transfer_of_omega_bounds hAbsorb hLowerOmega hUpper chen_gap_76407
  refine hTransfer.mono ?_
  intro N hN hEven
  have hCount : Db 76407 100000 N = RealDb (76407 / 100000 : ℝ) N := by
    exact Db_eq_RealDb (by norm_num)
  calc
    H N / 1000 = (1 / 1000 : ℝ) * H N := by ring
    _ ≤ (Db 76407 100000 N : ℝ) := hN hEven
    _ = (RealDb (76407 / 100000 : ℝ) N : ℝ) := by rw [hCount]

/-- Conditional external-input application at the real exponent `74774/100000`.
The coefficient `1233/625` is an explicit assumption about the actual Chen
count, not an analytic result supplied by this theorem. Under all stated
hypotheses the output lower bound is `H N / 50000` on sufficiently large even
integers. -/
theorem eventually_RealDb_74774_lower_of_omega_bounds
    {H : ℕ → ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N)
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        ((1233 : ℝ) / 625 - epsilon) * H N ≤ (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 74774 100000 N : ℝ) ≤
          ((3393 / 500 : ℝ) * Real.log (100000 / 74774) + epsilon) * H N) :
    ∀ᶠ N in Filter.atTop, Even N →
      H N / 50000 ≤ (RealDb (74774 / 100000 : ℝ) N : ℝ) := by
  have hTransfer :=
    eventually_transfer_of_omega_bounds hAbsorb hLowerOmega hUpper external_gap_74774
  refine hTransfer.mono ?_
  intro N hN hEven
  have hCount : Db 74774 100000 N = RealDb (74774 / 100000 : ℝ) N := by
    exact Db_eq_RealDb (by norm_num)
  calc
    H N / 50000 = (1 / 50000 : ℝ) * H N := by ring
    _ ≤ (Db 74774 100000 N : ℝ) := hN hEven
    _ = (RealDb (74774 / 100000 : ℝ) N : ℝ) := by rw [hCount]

end ImbalancedChen
