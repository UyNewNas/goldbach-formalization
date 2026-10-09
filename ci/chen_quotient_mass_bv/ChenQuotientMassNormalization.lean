/-
SPDX-License-Identifier: Apache-2.0

HELD, UNCOMPILED CONSUMER CANDIDATE. Both sibling mass modules and the
separately owned ChenQuotientLevelGeometry candidate require CI verification.
This file adds no foreign dependency beyond the approved ordinary-BV root.
-/
import ImbalancedChen.ChenQuotientMassBVAdapter
import ImbalancedChen.ChenQuotientLevelGeometry

/-!
# Actual all-selected quotient mass normalization

The all-selected multiplier cap is proved, not assumed: each literal
third-through-sixth multiplier is at most N^beta for one fixed beta<1/2.
Hence every label lies below the BV logarithmic square-root cap eventually.
The final conclusions have only evenness and the fixed coefficient bound
as hypotheses. In particular, no AP-error estimate or desired mass-replacement
conclusion is repackaged as an input.
-/

namespace ImbalancedChen.ChenQuotientMassBVAdapter

noncomputable section
open Filter Topology
open MathlibNt.SieveTheory.BombieriVinogradov
open scoped BigOperators

/-- Uniform L1 mass replacement across all literal third-through-sixth
selectors. C is fixed before N; the four signed weights are chosen after N. -/
theorem eventually_chenUpsilon36WeightedMassError_le_logAccuracy
    (K : ℕ) (C : ℝ) (hC : 0 ≤ C) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ _hN : Even N,
      ∀ w₃ w₄ : ℕ → ℝ, ∀ w₅ w₆ : (ℕ × ℕ) → ℝ,
      ChenUpsilon36MassWeightsBound N C w₃ w₄ w₅ w₆ →
      chenUpsilon36WeightedMassError N (trueLogarithmicIntegral N) w₃ w₄ w₅ w₆ ≤
        epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  obtain ⟨B, _hB, hbound⟩ := exists_logLevel_chenUpsilon36_weightedMassError_logAccuracy K
  filter_upwards [hbound C hC epsilon hepsilon, eventually_chenUpsilon36_multiplier_cap B]
    with N hNbound hNcap
  intro hN w₃ w₄ w₅ w₆ hw
  have hcap : ChenUpsilon36MultiplierCap N (chenInitialLevelCap B N) := hNcap
  exact hNbound hN (chenInitialLevelCap B N) w₃ w₄ w₅ w₆ le_rfl hcap hw

/-- The actual weighted total mass is replaced by true Li(N) times its
literal reciprocal-totient coefficient, at every fixed logarithmic accuracy. -/
theorem eventually_abs_chenUpsilon36WeightedMass_sub_LiMain_le_logAccuracy
    (K : ℕ) (C : ℝ) (hC : 0 ≤ C) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ _hN : Even N,
      ∀ w₃ w₄ : ℕ → ℝ, ∀ w₅ w₆ : (ℕ × ℕ) → ℝ,
      ChenUpsilon36MassWeightsBound N C w₃ w₄ w₅ w₆ →
      |chenUpsilon36WeightedMass N w₃ w₄ w₅ w₆ -
        trueLogarithmicIntegral N *
          chenUpsilon36WeightedMassMainCoefficient N w₃ w₄ w₅ w₆| ≤
        epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  filter_upwards [eventually_chenUpsilon36WeightedMassError_le_logAccuracy
    K C hC epsilon hepsilon] with N hbound
  intro hN w₃ w₄ w₅ w₆ hw
  exact (abs_chenUpsilon36WeightedMass_sub_main_le N (trueLogarithmicIntegral N)
    w₃ w₄ w₅ w₆).trans (hbound hN w₃ w₄ w₅ w₆ hw)

end
end ImbalancedChen.ChenQuotientMassBVAdapter
