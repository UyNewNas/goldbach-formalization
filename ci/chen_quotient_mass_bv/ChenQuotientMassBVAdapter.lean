/-
SPDX-License-Identifier: Apache-2.0

HELD, UNCOMPILED CONSUMER CANDIDATE. No Lean/Lake execution, kernel replay,
axiom audit, publication, or owned-core integration has been performed.
The only foreign dependency remains the approved ordinary-BV closure
already used by ChenInitialBVAdapter and ChenQuotientBVAdapter: 270
production plus nine Architect support modules, pinned upstream commit
09b97db5764ade1246bfb77206baa1b124760958. No new foreign root is imported.
-/
import ImbalancedChen.ChenQuotientMassFinite
import ImbalancedChen.ChenQuotientBVAdapter

/-!
# Genuine BV replacement of the bounded-weight quotient masses

The level exponent is chosen before the fixed coefficient bound, epsilon,
and every eventual label-dependent weight. BV at K+1 absorbs the constant;
no secondary reciprocal-totient logarithm is needed for mass replacement.
The literal centre-prime subtraction is paid by the owned polylog budget.
The finite all-selected cap will be discharged by fixed-gap geometry in
ChenQuotientMassNormalization; it is not an analytic estimate premise.
-/

namespace ImbalancedChen.ChenQuotientMassBVAdapter

noncomputable section
open Filter Topology
open MathlibNt.SieveTheory.BombieriVinogradov
open scoped BigOperators
open Classical

/-- A genuine distribution conclusion for all four actual masses.
The coefficient bound is fixed before N; the weights themselves are
uniformly quantified after N and may vary arbitrarily with the labels. -/
theorem exists_logLevel_chenUpsilon36_weightedMassError_logAccuracy (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ C : ℝ, 0 ≤ C → ∀ epsilon : ℝ, 0 < epsilon →
        ∀ᶠ N : ℕ in atTop, ∀ hN : Even N, ∀ Q : ℕ,
          ∀ w₃ w₄ : ℕ → ℝ, ∀ w₅ w₆ : (ℕ × ℕ) → ℝ,
          Q ≤ Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B) →
          ChenUpsilon36MultiplierCap N Q →
          ChenUpsilon36MassWeightsBound N C w₃ w₄ w₅ w₆ →
          chenUpsilon36WeightedMassError N (trueLogarithmicIntegral N) w₃ w₄ w₅ w₆ ≤
            epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  obtain ⟨B, hB, V, _hV, hBV⟩ :=
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
      ((K + 1 : ℕ) : ℝ) (by positivity)
  refine ⟨B, hB, ?_⟩
  intro C hC epsilon hepsilon
  filter_upwards
    [hBV,
      ChenInitialBVAdapter.eventually_two_mul_supplier_bound_le_half_accuracy
        (2 * C * V) K epsilon hepsilon,
      eventually_mul_chenUpsilon36CentreMass_le_logAccuracy K C hC
        (epsilon / 2) (half_pos hepsilon),
      eventually_ge_atTop (2 : ℕ)] with N hBVN hconstant hcentre hN2
  intro hN Q w₃ w₄ w₅ w₆ hQ hcap hw
  have hQproducer : Q ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
    rwa [ChenInitialBVAdapter.supplier_cutoff_eq_sqrt_level]
  have hBVnatural :
      (∑ k ∈ Finset.Icc 1 (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
        standardPrimeAPPrefixMaxError N k) ≤
          V * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 1) := by
    simpa only [Real.rpow_natCast] using hBVN hN2
  have hpool :=
    (ChenQuotientBVAdapter.sum_chenQuotientPrimeAPError_le_supplier N Q _ hQproducer).trans
      hBVnatural
  calc
    _ ≤ C * (4 * (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) +
          chenUpsilon36CentreMass N) :=
      chenUpsilon36WeightedMassError_le_primitive_add_centre N Q
        (trueLogarithmicIntegral N) C w₃ w₄ w₅ w₆ hC hw hcap
    _ = (4 * C) * (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|) +
          C * chenUpsilon36CentreMass N := by ring
    _ ≤ (4 * C) * (V * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 1)) +
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K :=
      add_le_add (mul_le_mul_of_nonneg_left hpool (by positivity)) (hcentre hN)
    _ = 2 * ((2 * C * V) * (N : ℝ) / (Real.log (N : ℝ)) ^ (K + 1)) +
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by ring
    _ ≤ (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K +
        (epsilon / 2) * (N : ℝ) / (Real.log (N : ℝ)) ^ K :=
      add_le_add hconstant le_rfl
    _ = epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by ring

end
end ImbalancedChen.ChenQuotientMassBVAdapter
