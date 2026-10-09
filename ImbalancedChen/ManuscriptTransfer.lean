import ImbalancedChen.NumericalTransfer
import ImbalancedChen.SingularSeries

/-!
# Conditional transfer with the manuscript's concrete normalization

The normalization in this file is the actual
`singularNormalization N = singularSeries N * N / (log N)^2`, with the
manuscript's infinite product and finite prime-divisor correction. Its growth
and eventual positivity are proved in `SingularSeries`; neither is a premise
of the results below. In particular the receiver-one correction is absorbed
using `eventuallyEven_singularNormalization_unit_absorption`.

The two analytic inputs remain explicit: a lower epsilon estimate for the
actual `D12Omega` count, and an upper epsilon estimate for the actual removed
count `B`, both on sufficiently large even integers. This file does not prove
either estimate, certify their numerical sieve coefficients, or establish an
unconditional Chen theorem. The second pair of results additionally requires
the external lower coefficient `1233/625 = 1.9728`.

The existence conclusions give literal equalities `N = p + r * q`, with
`p` and `q` prime, `r = 1` or prime, and the required real-power imbalance.
-/

namespace ImbalancedChen

/-- The concrete manuscript normalization removes the former growth premise
from the separate-input lower bound at `b = 76407/100000`. Only the two
displayed actual-count analytic estimates are hypotheses. -/
theorem eventually_RealDb_76407_lower_of_manuscript_bounds
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        ((18271 : ℝ) / 10000 - epsilon) * singularNormalization N ≤
          (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 76407 100000 N : ℝ) ≤
          ((3393 / 500 : ℝ) * Real.log (100000 / 76407) + epsilon) *
            singularNormalization N) :
    ∀ᶠ N in Filter.atTop, Even N →
      singularNormalization N / 1000 ≤
        (RealDb (76407 / 100000 : ℝ) N : ℝ) := by
  exact eventually_RealDb_76407_lower_of_omega_bounds
    eventuallyEven_singularNormalization_unit_absorption hLowerOmega hUpper

/-- The concrete manuscript normalization removes the former growth premise
from the external-input lower bound at `b = 74774/100000`. The stronger actual
Chen-count lower estimate remains an explicit hypothesis. -/
theorem eventually_RealDb_74774_lower_of_manuscript_bounds
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        ((1233 : ℝ) / 625 - epsilon) * singularNormalization N ≤
          (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 74774 100000 N : ℝ) ≤
          ((3393 / 500 : ℝ) * Real.log (100000 / 74774) + epsilon) *
            singularNormalization N) :
    ∀ᶠ N in Filter.atTop, Even N →
      singularNormalization N / 50000 ≤
        (RealDb (74774 / 100000 : ℝ) N : ℝ) := by
  exact eventually_RealDb_74774_lower_of_omega_bounds
    eventuallyEven_singularNormalization_unit_absorption hLowerOmega hUpper

/-- Under the two actual-count estimates, every sufficiently large even
integer has the manuscript's literal representation at `b = 76407/100000`.
There is no additional positivity or normalization-growth hypothesis. -/
theorem eventually_exists_representation_76407_of_manuscript_bounds
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        ((18271 : ℝ) / 10000 - epsilon) * singularNormalization N ≤
          (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 76407 100000 N : ℝ) ≤
          ((3393 / 500 : ℝ) * Real.log (100000 / 76407) + epsilon) *
            singularNormalization N) :
    ∀ᶠ N in Filter.atTop, Even N →
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (76407 / 100000 : ℝ) := by
  have hLower :=
    eventually_RealDb_76407_lower_of_manuscript_bounds hLowerOmega hUpper
  refine (eventually_singularNormalization_pos.and hLower).mono ?_
  rintro N ⟨hPosN, hLowerN⟩ hEven
  have hReal : (0 : ℝ) < (RealDb (76407 / 100000 : ℝ) N : ℝ) :=
    lt_of_lt_of_le (div_pos hPosN (by norm_num : (0 : ℝ) < 1000)) (hLowerN hEven)
  have hCount : 0 < RealDb (76407 / 100000 : ℝ) N := by
    exact_mod_cast hReal
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hCount
  obtain ⟨r, q, hpPrime, hr, hq, hEquality, hPower⟩ :=
    exists_representation_of_mem_realImbalancedPrimes
      (by norm_num : (0 : ℝ) ≤ 76407 / 100000) hp
  exact ⟨p, r, q, hpPrime, hr, hq, hEquality, hPower⟩

/-- Conditional literal representations at `b = 74774/100000`, using the
external lower coefficient and the concrete manuscript normalization. The
actual lower and upper analytic estimates remain unproved inputs. -/
theorem eventually_exists_representation_74774_of_manuscript_bounds
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        ((1233 : ℝ) / 625 - epsilon) * singularNormalization N ≤
          (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 74774 100000 N : ℝ) ≤
          ((3393 / 500 : ℝ) * Real.log (100000 / 74774) + epsilon) *
            singularNormalization N) :
    ∀ᶠ N in Filter.atTop, Even N →
      ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ (74774 / 100000 : ℝ) := by
  have hLower :=
    eventually_RealDb_74774_lower_of_manuscript_bounds hLowerOmega hUpper
  refine (eventually_singularNormalization_pos.and hLower).mono ?_
  rintro N ⟨hPosN, hLowerN⟩ hEven
  have hReal : (0 : ℝ) < (RealDb (74774 / 100000 : ℝ) N : ℝ) :=
    lt_of_lt_of_le (div_pos hPosN (by norm_num : (0 : ℝ) < 50000)) (hLowerN hEven)
  have hCount : 0 < RealDb (74774 / 100000 : ℝ) N := by
    exact_mod_cast hReal
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hCount
  obtain ⟨r, q, hpPrime, hr, hq, hEquality, hPower⟩ :=
    exists_representation_of_mem_realImbalancedPrimes
      (by norm_num : (0 : ℝ) ≤ 74774 / 100000) hp
  exact ⟨p, r, q, hpPrime, hr, hq, hEquality, hPower⟩

end ImbalancedChen
