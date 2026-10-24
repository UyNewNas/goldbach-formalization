import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.P4BLabelledPairDictionary
import ImbalancedChen.P4BLogSavingBudget

/-!
# Direct consumption of the literal Part 3 prime-product target

YELLOW / SOURCE-ONLY / UNCOMPILED (2026-10-24).
The two P4B imports are intended future module names for companion drafts.

The sole external Part 3 analytic premise below is the existing
`Part3.UniformPrimeProductTarget`, at genuine rank two, labelled-prime cap
`N`, and the exact ordered-band indicator `P4BLabelledPairDictionary.W`.
The geometric family has one member at each target; it is fixed before
the PP constants and target threshold are returned. Signs remain inside
the one absolute value. The exact dictionary and the proved logarithmic
budget derive the actual physical distribution input, rather than asking
for that input as a premise.

This is a conditional consumer of PP, not a proof of the PP target or of
its geometric licensing. In particular the discontinuous ordered-band
indicator has not been shown to belong to a licensed P3 family here.
The actual P4A density bound is still an explicit premise. The attached
coefficient, attachment precision and enumeration cap are the same in
the density and PP inputs. That enumeration cap is distinct from the
labelled-prime carrier cap, which is exactly `N` throughout this file.
-/

namespace ImbalancedChen.P4BDirectPPUpperAssembly

noncomputable section
open Filter Topology

/-- An actual ordered-band PP target supplies the exact physical signed
error at any requested normalization precision. PP is consumed at A = 3;
its C and N0 are fixed before the subsequent target N is chosen. -/
theorem eventually_realPhysicalDistributionError_le_of_uniformPP
    (b kappa : ℝ) (Q : ℕ → Finset ℕ) (rho : ℕ → ℕ → ℝ)
    (hUniformPP : Part3.UniformPrimeProductTarget (ι := Unit) 2
      (fun N : ℕ => N) Q rho
      (fun N _ => P4BLabelledPairDictionary.W b N
        (manuscriptHalfProductCutoff kappa N)))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (Q N) (rho N)| ≤ delta * singularNormalization N := by
  obtain ⟨C, hC, N0, hPP⟩ := hUniformPP (3 : ℝ) (by norm_num)
  filter_upwards
    [eventually_logSaving_le_singularNormalization C hC.le 3 (by norm_num)
      delta hdelta, eventually_ge_atTop N0] with N hbudget hN
  intro hEven
  have hraw :
      |Part3.primeProductSignedError 2 N N (Q N) (rho N)
        (P4BLabelledPairDictionary.W b N (manuscriptHalfProductCutoff kappa N))| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (Real.log (N : ℝ)) (3 : ℕ)]
    exact hPP N hN hEven Unit.unit
  rw [P4BLabelledPairDictionary.primeProductSignedError_eq_realPhysicalDistributionError]
    at hraw
  exact hraw.trans hbudget.2

/-- Conditional actual same-rho hUpper assembly with a genuine P3 target
as its only P3 analytic input. `hdensity` is the remaining P4A obligation.
No exact physical-error estimate or hUpper conclusion is assumed.
For each positive precision, the actual coefficient is fixed before PP's
constants and threshold are selected; the existing same-rho assembly then
chooses one common precision for its final tolerance. -/
theorem eventually_RealB_le_currentK_log_of_actual_density_uniformPP
    {b kappa nu r : ℝ} (hb : 0 < b) (hbOne : b < 1) (hkappa : 0 < kappa)
    (hnu : 0 < nu) (hr : 0 < r) (hsieve : nu * r < 1)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hUniformPP : ∀ delta : ℝ, 0 < delta →
      Part3.UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
        (fun N _ => P4BLabelledPairDictionary.W b N
          (manuscriptHalfProductCutoff kappa N))) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  apply eventually_RealB_le_currentK_log_of_actual_density_distribution
    hb hbOne hkappa hnu hr hsieve hgap epsilon retain cap hepsilon hcap hdensity
  intro delta hdelta
  exact eventually_realPhysicalDistributionError_le_of_uniformPP b kappa
    (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
    (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
    (hUniformPP delta hdelta) delta hdelta

end
end ImbalancedChen.P4BDirectPPUpperAssembly
