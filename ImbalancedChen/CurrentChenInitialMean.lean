import ImbalancedChen.CurrentChenInitialSource
import ImbalancedChen.CurrentChenMeanLedger
import MathlibNt.SieveTheory.LiLiuGoldbachS1BetaFixedNormalizedLower

/-!
# An actual nontrivial mean bound for the current first Chen term

This module consumes the pinned, proved ordinary-BV lower sieve for the
literal prime-difference source at cutoff N^(4/33) and fixed ratio s = 4.
It transfers that estimate to the current first cutoff N^(417/5000).

The source transfer is proved on actual finite sets. The upstream sieve
ignores prime divisors of N, so its noncoprime differences are removed and
paid by the genuine distinct-prime-divisor count of N. The latter is
o(singularNormalization N). The upstream convergent singular series is
identified with the repository's actual infinite product and finite divisor
correction; no factor of two is inserted.

The conclusion has no analytic estimate, policy, mean bound or distribution
supplier left as a hypothesis. Its coefficient is (33/4) log 3. This is an
independent lower bound for the actual current Upsilon1; it is not the
adopted L1 endpoint and does not close the other ten rows or hLower.

Candidate status: this new module requires elaboration, kernel replay and
an axiom audit of its actual supplier closure. Source inspection alone
does not provide those checks.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.SwitchingPrinciple (dimensionOneLowerLinearSieveFactor)

/-- A proved ordinary-BV lower mean for the actual current first Chen row.
The upstream cutoff is larger, so monotonicity is in the lower-bound
direction. The source correction and all analytic errors are paid.

This coefficient is not the adopted current L1 endpoint. No conclusion
about the remaining rows or the complete current Chen mean is asserted. -/
theorem eventually_currentChenUpsilon1_ge_initial_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((33 / 4 : ℝ) * Real.log 3 - epsilon) * singularNormalization N ≤
        currentChenUpsilon1 N := by
  let c : ℝ := (33 / 4 : ℝ) * Real.log 3
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  let tau : ℝ := min (1 / 2) (epsilon / (4 * c))
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have htauOne : tau < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have htauCost : c * tau ≤ epsilon / 4 := by
    have h := (le_div_iff₀ (show 0 < 4 * c by positivity)).mp
      (show tau ≤ epsilon / (4 * c) from min_le_right _ _)
    nlinarith
  obtain ⟨N₀, hN₀, hmain⟩ :=
    goldbachS1_beta_fixed_normalized_lower 4 (epsilon / 4)
      (by norm_num) (by norm_num) (by positivity) tau htau htauOne
  have hcoef :
      (33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) * (1 - tau) *
          dimensionOneLowerLinearSieveFactor 4 = c * (1 - tau) := by
    calc
      _ = ((33 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) *
          dimensionOneLowerLinearSieveFactor 4) * (1 - tau) := by ring
      _ = _ := by rw [currentChen_initial_sieve_coefficient]
  filter_upwards
    [eventually_ge_atTop N₀,
      eventually_currentChen_primeFactors_negligible (epsilon / 2) (half_pos hepsilon)]
    with N hN herr
  intro hEven
  have hN4 : 4 ≤ N := hN₀.trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hcut : (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (N : ℝ) ^ (4 / 33 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hfinite := currentChen_goldbachS1_le_sifted_add_primeFactors N tau
    ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ))
    (by omega) htau.le hcut
  rw [← currentChenUpsilon1_eq_actual_sifted_card N hEven] at hfinite
  have hraw := hmain N hN hEven
  rw [hcoef, ← currentChen_singularSeries_eq_liuSingularSeries N] at hraw
  have hraw' :
      (c * (1 - tau) - epsilon / 4) * singularNormalization N ≤
        (goldbachS1 (goldbachDifferenceCarrier N tau) N
          ((N : ℝ) ^ (4 / 33 : ℝ)) : ℝ) := by
    simpa only [singularNormalization, Real.rpow_two, mul_assoc, mul_div_assoc] using hraw
  have hscale : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hcoefLower : c - epsilon / 2 ≤ c * (1 - tau) - epsilon / 4 := by
    nlinarith only [htauCost]
  have hlower := (mul_le_mul_of_nonneg_right hcoefLower hscale).trans hraw'
  change (c - epsilon) * singularNormalization N ≤ currentChenUpsilon1 N
  nlinarith only [hlower, hfinite, herr]

end

end ImbalancedChen
