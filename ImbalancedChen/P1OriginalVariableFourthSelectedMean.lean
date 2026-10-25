import ImbalancedChen.P1OriginalVariableFourthSelectedZeroCutoff
import ImbalancedChen.P1OriginalVariableFourthUntruncatedDomination

/-!
# Actual selected variable-fourth mean and its original full integral

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The actual arithmetic cutoff construction and the independent integrable
domination construction have the same original positive-cube integrals.
Uniqueness identifies their limits, so the complete selected actual tuple
source converges to the untruncated original variable raw-kernel integral.
No desired mean, tail, integrability or fixed-eligibility premise appears.
The original frontier outside the selected cells is a separate contribution.
-/

namespace ImbalancedChen.P1OriginalVariableFourthSelectedMean

noncomputable section
open Filter Topology
open P1OriginalCoarseContinuation P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthSelectedZeroCutoff
open P1OriginalVariableFourthUntruncatedDomination

/-- Complete ORIGINAL selected-cell variable-Q4 arithmetic source, with
the exact untruncated same-source raw PLUS integral as its mean. -/
theorem tendsto_selectedFullSource_original_fullIntegral
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J4 : Finset (FourthCell m)) (rows : Finset ProducerRow)
    (licensed : ProducerRow → Prop) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => selectedFullSource e chi m omega J4 rows licensed N (cap N))
      evenTargets (𝓝 (variableFullSelectedIntegral e chi m omega J4 rows licensed)) := by
  obtain ⟨L, hcut, hactual⟩ := exists_selected_actual_source_and_zero_cutoff_limit
    e chi m omega homega homegaRho J4 rows licensed
  have hfull := tendsto_refinedSelectedIntegral_fullIntegral
    e he chi m omega homega homegaRho J4 rows licensed
  have heq : L = variableFullSelectedIntegral e chi m omega J4 rows licensed :=
    tendsto_nhds_unique hcut hfull
  simpa only [heq] using hactual cap hcap

end
end ImbalancedChen.P1OriginalVariableFourthSelectedMean
