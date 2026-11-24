import ImbalancedChen.P2FirstIntegralPolynomialEnclosure
import ImbalancedChen.P2OriginalCertificateBudgetAssembly
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no rational producer or numeric replay.
Prospective import staging:
  sibling P2FirstIntegralSeries.lean -> ImbalancedChen/P2FirstIntegralSeries.lean;
  sibling P2FirstIntegralPolynomialEnclosure.lean -> its same ImbalancedChen name.

The literal selected endpoint is read from
docs/part2/adopted-evidence-catalog.json:A_upper.base_components.first_integral
and its source field is first_integral_upper_exact.  It is also exactly
P2OriginalCertificateBudget.baseUpper 1 in the actual budget assembly.

`polynomial_upper_le_selected` contains the complete finite rational arithmetic
proof request; the rational comparison is NOT an assumption.  The order-16
center is an explicit 256-term rational sum and the exact analytic radius is
used, rather than the weaker 2^-80 radius.  The proof body is intentionally
unexecuted under CODE_ONLY.  Consequently this is a source candidate, NOT a
claim that the comparison or the analytic dependency chain passed Lean.

If the future exact norm_num comparison fails, this candidate is rejected;
there is no fallback to an assumed endpoint.  The upstream analytic enclosure
remains independently meaningful.  No altered endpoint, normalization, gain,
target-equivalent hypothesis, or omitted interval is introduced.
-/

namespace ImbalancedChen.P2OriginalFirstIntegralEndpointSourceOnly

noncomputable section

open P2FirstIntegralSeriesSourceOnly
open P2FirstIntegralPolynomialEnclosureSourceOnly

def selectedUpperQ : ℚ := 7179974843999672947 / 9444732965739290427392

theorem selectedUpperQ_eq_budget :
    selectedUpperQ = P2OriginalCertificateBudget.baseUpper 1 := by
  norm_num [selectedUpperQ, P2OriginalCertificateBudget.baseUpper]

/-- The selected catalog upper endpoint is compared with actual finite
polynomial integration plus its derived analytic remainder.  All 256 terms
are expanded using exact rational arithmetic by this proof body. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem polynomial_upper_le_selected :
    centerQ 16 16 + radiusQ 16 16 ≤ selectedUpperQ := by
  norm_num [centerQ, coefficientQ, degree, radiusQ, errorQ, dQ,
    selectedUpperQ, Finset.sum_range_succ]

/-- Directed bound for the genuine original first integral, without an
integral-value hypothesis.  The two dependencies are analytic soundness and
the concrete finite rational comparison above. -/
theorem originalFirstIntegral_le_selected :
    originalFirstIntegral ≤ (selectedUpperQ : ℝ) := by
  have ha := (originalFirstIntegral_polynomial_enclosure 16 16).2
  have hq : ((centerQ 16 16 + radiusQ 16 16 : ℚ) : ℝ) ≤ (selectedUpperQ : ℝ) := by
    exact_mod_cast polynomial_upper_le_selected
  exact ha.trans hq

/-- Literal formula and endpoint, retaining Theta=299/500 and rho=19/96. -/
theorem originalFirstIntegral_literal_selected_bound :
    (4 / (299 / 500 : ℝ)) *
        (∫ s in (2 : ℝ)..((299 / 500 : ℝ) / (19 / 96 : ℝ) - 1),
          Real.log (s - 1) / s) ≤
      (7179974843999672947 / 9444732965739290427392 : ℝ) := by
  simpa [originalFirstIntegral, kernel, stop, theta, rho, selectedUpperQ] using
    originalFirstIntegral_le_selected

/-- Actual receiver adaptation for the original base component at index 1. -/
theorem originalFirstIntegral_le_budget_base_one :
    originalFirstIntegral ≤ (P2OriginalCertificateBudget.baseUpper 1 : ℝ) := by
  rw [← selectedUpperQ_eq_budget]
  exact originalFirstIntegral_le_selected

end

end ImbalancedChen.P2OriginalFirstIntegralEndpointSourceOnly
