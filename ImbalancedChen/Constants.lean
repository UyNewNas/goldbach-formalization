import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Exact arithmetic for the manuscript's final constants

These theorems check rational recombinations and logarithmic inequalities. They
do not establish the analytic sieve bounds or the validity of the quoted
integral-certificate endpoints. In particular, no theorem in this file proves
that the recombined numbers are coefficients of actual representation counts.

The numerical inputs are the displayed fractions in the manuscript's section
"Consequences of the fifth-prefix gain and sharper second seed".

The logarithm estimates use mathlib's proved atanh-series bound with three
terms and its coarser geometric remainder. This bound is sufficient for both
strict gaps; the sharper remainder asserted in the manuscript is not needed.
-/

namespace ImbalancedChen

/-- Exact subtraction of the three quoted gains leaves room below `3393/500`.
This is arithmetic on quoted numbers, not a verification of their provenance. -/
theorem final_K_recombination_lt :
    (1230679674488580033396846301 : ℝ) / 180734410032387061618573312
      - 10720642480494928338187 / 604462909807314587353088
      - 5155254219572575727579 / 1208925819614629174706176
      - 2167182368869852589729 / 1208925819614629174706176
      < 3393 / 500 := by
  norm_num

/-- The rescaled second-seed term replaces, rather than supplements, the old term. -/
theorem second_seed_rescaling :
    (10 : ℝ) / 9 * (56 / 465275) = 112 / 837495 := by
  norm_num

/-- Exact recombination of the quoted table and the two disjoint corrections. -/
theorem final_c_recombination :
    (9089 : ℝ) / 5000
      + 101203 / 40000 * (1 - (3393 / 500) / (681 / 100))
      + 2 / 6635 + 112 / 837495
      = 4609497840932309 / 2522777813550000 := by
  norm_num

/-- The recombined rational number is strictly above `18271/10000`. -/
theorem final_c_recombination_gt :
    (18271 : ℝ) / 10000 < 4609497840932309 / 2522777813550000 := by
  norm_num

/-- A proved rational upper bound for the logarithm at the first exponent. -/
theorem log_inv_76407_le :
    Real.log ((100000 : ℝ) / 76407) ≤ 2690973 / 10000000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (23593 : ℝ) / 176407) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

/-- A proved rational upper bound for the logarithm at the second exponent. -/
theorem log_inv_74774_le :
    Real.log ((100000 : ℝ) / 74774) ≤ 2907023 / 10000000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (12613 : ℝ) / 87387) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

/-- The strict arithmetic gap used with the manuscript's separate Chen coefficient.
Applying it to representation counts requires the corresponding analytic bounds. -/
theorem chen_gap_76407 :
    (18271 : ℝ) / 10000 - (3393 / 500) * Real.log (100000 / 76407)
      > 1 / 1000 := by
  linarith only [log_inv_76407_le]

/-- The strict arithmetic gap for the external coefficient `1233/625`.
This does not prove or audit the external Chen input. -/
theorem external_gap_74774 :
    (1233 : ℝ) / 625 - (3393 / 500) * Real.log (100000 / 74774)
      > 1 / 50000 := by
  linarith only [log_inv_74774_le]

end ImbalancedChen
