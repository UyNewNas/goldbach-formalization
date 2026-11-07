import ImbalancedChen.P4BLabelledOuterPPUpperAssembly
import ImbalancedChen.P4BPhysicalProductOuterRamp
import ImbalancedChen.P4BOuterRampRoughness

/-!
# The actual physical ramp: PP, P4A density and arithmetic mass to hUpper

YELLOW / SOURCE-ONLY / UNCOMPILED (2026-10-24).
The imports are intended future normal modules for companion drafts.

The weight is exactly `P4B.physicalPairOuterRamp` from the physical-product
construction. Only the upper product wall is scaled by log N; the actual
outer endpoint is exp(width)*N. Every product contribution is retained.
This file introduces no arbitrary V, geometry, roughness, signed coprime
correction, primitive-error, or hUpper premise.

For each positive attachment precision, width is positive and twice width
fits the actual baseline exponent gap. The physical ramp supplies its own
nonnegativity and actual-indicator majorant. The ramp roughness theorem
then makes its same-rho outer coprime correction exactly zero. The labelled
consumer derives the signed primitive budget from the genuine rank-two,
cap-N UniformPrimeProductTarget at A=3 and the proved log-saving budget.

Three analytic obligations remain explicit and unproved: the actual P4A
density estimate, the arithmetic labelled mass surplus of this physical
ramp, and the genuine P3 PP target for this physical ramp. In particular
neither spectral/geometric licensing nor a boundary-count theorem is
asserted. The scalar ramp is not promoted to a licensed smooth P3 family.
-/

namespace ImbalancedChen.P4BPhysicalRampPPUpperAssembly

noncomputable section
open Filter Topology
open scoped BigOperators
open Part3

/-- Fixed-real-b upper bound for the actual physical ramp. The density,
mass and PP inputs refer to the same precision and the same literal
attached coefficient. The only outer-source parameters are its supplied
positive physical widths; all geometric and coprime slots are discharged. -/
theorem eventually_RealB_le_of_actual_physical_ramp_density_mass_uniformPP
    {b kappa nu r : ℝ}
    (hbHalf : 1 / 2 < b) (hbOne : b < 1)
    (hkappa : 0 < kappa) (_hkappaOne : kappa < 1)
    (hnu : 0 < nu) (hr : 0 < r)
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ) (width : ℝ → ℝ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hwidth : ∀ delta : ℝ, 0 < delta →
      0 < width delta ∧
        2 * width delta ≤ (1 - kappa) * b / (1 + b) - nu * r)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hlabelledMass : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (∑ t ∈ labelledPrimeTuples 2 N,
        P4B.physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N)
          (width delta) t) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hUniformPP : ∀ delta : ℝ, 0 < delta →
      UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
        (fun N _ => P4B.physicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) (width delta))) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  have hb : 0 < b := by linarith only [hbHalf]
  have hden : 0 < 1 + b := by linarith only [hb]
  have hbaseline : (1 - kappa) * b / (1 + b) < 1 := by
    apply (div_lt_iff₀ hden).2
    have hproduct : 0 < kappa * b := mul_pos hkappa hb
    nlinarith only [hproduct]
  obtain ⟨hwidthOne, hwidthGapOne⟩ := hwidth 1 (by norm_num)
  have hsieve : nu * r < 1 := by
    linarith only [hwidthOne, hwidthGapOne, hbaseline]
  apply P4BLabelledOuterPPUpperAssembly.eventually_RealB_le_of_actual_labelled_outer_uniformPP
    hb hbOne hkappa hnu hr hsieve epsilon retain cap
    (fun delta N => P4B.physicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) (width delta)) hepsilon hcap
  · intro delta hdelta
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N _hN
    intro _hEven t _ht
    exact (P4B.positiveRescaledFourWallWeight_bounds b _ _ _ _).1
  · intro delta hdelta
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    intro _hEven t ht
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
    have hT : 0 < manuscriptHalfProductCutoff kappa N := by
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hNpos _)
    exact P4B.actual_W_le_physicalPairOuterRamp hN1 hT (hwidth delta hdelta).1 ht
  · exact hlabelledMass
  · exact hdensity
  · intro delta hdelta
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    intro _hEven
    have hgap : 2 * width delta ≤ P4BOuterRampRoughness.baseline b kappa - nu * r :=
      (hwidth delta hdelta).2
    have hzero := P4BOuterRampRoughness.physical_ramp_outer_signed_coprime_sum_eq_zero
      hb hnu hN (hepsilon delta hdelta).2.2 (hwidth delta hdelta).1 hgap
      (retain delta) (cap delta)
    rw [hzero, abs_zero]
    apply mul_nonneg hdelta.le
    have hseries := (singularSeries_pos N).le
    unfold singularNormalization
    positivity
  · exact hUniformPP

end
end ImbalancedChen.P4BPhysicalRampPPUpperAssembly
