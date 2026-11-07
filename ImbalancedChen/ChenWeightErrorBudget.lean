import ImbalancedChen.QuotientChenElevenSum
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.AsymptoticTransfer

/-!
# Absorbing the actual eleven-term Chen weight error

The finite Chen inequality loses exactly `984 N^(1 - 100/1149) + 4` when
passing to the count `D12`, which excludes receiver one. This loss is
negligible relative to the genuine `singularNormalization`, by the proved
sublinear-power error budget. The finite inequality's two size conditions
also hold eventually without any counting or sieve premise.

The lower estimate for the literal eleven-Upsilon combination is still an
explicit analytic hypothesis. No such mean estimate, and in particular no
coefficient `c = 1.8271`, is proved here. The final theorem merely composes
this conditional lower-bound transfer with the existing finite good/bad
count transfer, retaining its actual bad-count estimate as a hypothesis.
-/

namespace ImbalancedChen

open Filter

/-- The actual size gate used by the finite eleven-term inequality holds
eventually. Both exponents and the cutoff two are literal. -/
theorem eventually_chen_weight_size_conditions :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ (N : ℝ) ∧ 2 ≤ (N : ℝ) ^ (100 / 1149 : ℝ) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (100 / 1149 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 100 / 1149)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hpow.eventually (eventually_ge_atTop (2 : ℝ))] with N hN hA
  exact ⟨by exact_mod_cast hN, hA⟩

/-- The exact combined exceptional-receiver and receiver-one loss is
arbitrarily small in the project's actual singular normalization. -/
theorem eventually_chen_weight_error_le_singularNormalization :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        984 * (N : ℝ) ^ (1 - (100 / 1149 : ℝ)) + 4 ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  have hquarter : 0 < epsilon / 4 := by linarith
  have hbudget := eventually_powerLog_add_one_le_singularNormalization
    246 (1 - (100 / 1149 : ℝ)) 0 (by norm_num) (epsilon / 4) hquarter
  filter_upwards [hbudget] with N hN
  simp only [pow_zero, mul_one] at hN
  nlinarith only [hN]

/-- The literal eleven-term inequality after absorbing its proved finite
error. This is unconditional and does not assume a lower mean estimate. -/
theorem eventually_chen_eleven_upsilon_sub_normalized_error_le_four_D12 :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        3 * chenUpsilon1 N + chenUpsilon2 N - chenUpsilon3 N - chenUpsilon4 N +
          chenUpsilon5 N + chenUpsilon6 N - 2 * chenUpsilon7 N - chenUpsilon8 N -
          chenUpsilon9 N - chenUpsilon10 N - chenUpsilon11Full N -
          epsilon * singularNormalization N ≤ 4 * (D12 N : ℝ) := by
  intro epsilon hepsilon
  filter_upwards [eventually_chen_weight_size_conditions,
    eventually_chen_weight_error_le_singularNormalization epsilon hepsilon]
    with N hsize herror
  have hfinite := chen_eleven_upsilon_sub_error_sub_four_le_four_D12
    N hsize.1 hsize.2
  linarith only [hfinite, herror]

/-- An epsilon lower mean estimate with leading coefficient `4 * c` for
the actual eleven-Upsilon combination yields the epsilon lower estimate
with coefficient `c` for `D12`. The mean estimate is the unproved analytic
input; no premise mentions a lower bound for the target count. -/
theorem eventually_D12_lower_of_eleven_upsilon_lower
    {c : ℝ}
    (hMean : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        (4 * c - epsilon) * singularNormalization N ≤
          3 * chenUpsilon1 N + chenUpsilon2 N - chenUpsilon3 N - chenUpsilon4 N +
            chenUpsilon5 N + chenUpsilon6 N - 2 * chenUpsilon7 N - chenUpsilon8 N -
            chenUpsilon9 N - chenUpsilon10 N - chenUpsilon11Full N) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        (c - epsilon) * singularNormalization N ≤ (D12 N : ℝ) := by
  intro epsilon hepsilon
  have htwice : 0 < 2 * epsilon := by linarith
  filter_upwards [hMean (2 * epsilon) htwice,
    eventually_chen_eleven_upsilon_sub_normalized_error_le_four_D12
      (2 * epsilon) htwice] with N hMeanN hfinite
  intro hEven
  nlinarith only [hMeanN hEven, hfinite]

/-- Conditional transfer to the actual imbalanced count. Both analytic
inputs remain explicit: the lower estimate for all eleven Upsilon terms
and the upper estimate for the actual bad count. Normalization growth and
the Chen weight error absorption have already been proved. -/
theorem eventually_transfer_of_eleven_upsilon_bounds
    {num den : ℕ} {c k delta : ℝ}
    (hMean : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        (4 * c - epsilon) * singularNormalization N ≤
          3 * chenUpsilon1 N + chenUpsilon2 N - chenUpsilon3 N - chenUpsilon4 N +
            chenUpsilon5 N + chenUpsilon6 N - 2 * chenUpsilon7 N - chenUpsilon8 N -
            chenUpsilon9 N - chenUpsilon10 N - chenUpsilon11Full N)
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, Even N →
        (B num den N : ℝ) ≤ (k + epsilon) * singularNormalization N)
    (hdelta : delta < c - k) :
    ∀ᶠ N : ℕ in atTop, Even N →
      delta * singularNormalization N ≤ (Db num den N : ℝ) := by
  exact eventually_transfer_of_bounds
    (eventually_singularNormalization_pos.mono (fun _ hN _ => hN))
    (eventually_D12_lower_of_eleven_upsilon_lower hMean) hUpper hdelta

end ImbalancedChen
