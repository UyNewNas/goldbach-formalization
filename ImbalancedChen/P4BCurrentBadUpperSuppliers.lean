import ImbalancedChen.P4BPhysicalRampMassReserve
import ImbalancedChen.P4BPhysicalRampPPUpperAssembly

/-!
# Final P4B supplier integration for each fixed real imbalance exponent

The arithmetic outer mass is selected from the actual four-wall reserve.
There is no mass, coprime, primitive-error or final upper-count premise.
The same original attached coefficient occurs throughout. Two genuine
upstream suppliers remain explicit: the P4A currentK density and the P3
signed prime-product estimate for each legal fixed physical ramp width.
Neither supplier is asserted here, and this is not an unconditional
`current_realBad_upper` declaration.

SOURCE ONLY / YELLOW / UNCOMPILED. Companion imports must be installed
with their complete source and checked before this candidate has proof
credit. The scalar continuous ramp is not claimed to have P3 licensing.
-/

namespace ImbalancedChen.P4BCurrentBadUpperSuppliers

noncomputable section
open Filter Topology
open scoped BigOperators
open Part3

/-- The real-b upper consumer after all actual arithmetic outer-mass
slots have been supplied. The remaining PP hypothesis is on a concrete
labelled source, with signs inside its complete physical modulus sum. -/
theorem current_realBad_upper_of_actual_density_and_uniform_physical_PP
    {b kappa nu r : ℝ}
    (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hnu : 0 < nu) (hr : 0 < r)
    (hgap : nu * r < (1 - kappa) * b / (1 + b))
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
    (hUniformPP : ∀ delta : ℝ, 0 < delta → ∀ physicalWidth : ℝ,
      0 < physicalWidth →
      2 * physicalWidth ≤ (1 - kappa) * b / (1 + b) - nu * r →
      UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
        (fun N _ => P4B.physicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) physicalWidth)) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  let widthMax : ℝ := ((1 - kappa) * b / (1 + b) - nu * r) / 2
  have hwidthMax : 0 < widthMax := by dsimp [widthMax]; linarith
  let width : ℝ → ℝ := fun delta =>
    if hdelta : 0 < delta then
      Classical.choose (P4B.exists_physical_ramp_mass_reserve
        hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)
    else 1
  have hwidthPos : ∀ delta : ℝ, 0 < delta → 0 < width delta := by
    intro delta hdelta
    dsimp only [width]
    rw [dif_pos hdelta]
    exact (Classical.choose_spec (P4B.exists_physical_ramp_mass_reserve
      hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)).1
  have hwidthLe : ∀ delta : ℝ, 0 < delta → width delta ≤ widthMax := by
    intro delta hdelta
    dsimp only [width]
    rw [dif_pos hdelta]
    exact (Classical.choose_spec (P4B.exists_physical_ramp_mass_reserve
      hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)).2.1
  have hwidthLegal : ∀ delta : ℝ, 0 < delta →
      0 < width delta ∧
        2 * width delta ≤ (1 - kappa) * b / (1 + b) - nu * r := by
    intro delta hdelta
    refine ⟨hwidthPos delta hdelta, ?_⟩
    have hle := hwidthLe delta hdelta
    dsimp only [widthMax] at hle
    linarith
  have hlabelledMass : ∀ delta : ℝ, 0 < delta →
      ∀ᶠ N : ℕ in atTop, Even N →
        (∑ t ∈ labelledPrimeTuples 2 N,
          P4B.physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N)
            (width delta) t) ≤
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
            delta * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro delta hdelta
    obtain ⟨N0, _hN0, hmass⟩ :=
      (Classical.choose_spec (P4B.exists_physical_ramp_mass_reserve
        hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)).2.2
    filter_upwards [eventually_ge_atTop N0] with N hN
    intro hEven
    simpa only [width, dif_pos hdelta] using hmass N hN hEven
  exact P4BPhysicalRampPPUpperAssembly.eventually_RealB_le_of_actual_physical_ramp_density_mass_uniformPP
      hbLower hbUpper hkappa hkappaOne hnu hr epsilon retain cap width
      hepsilon hcap hwidthLegal hdensity hlabelledMass
      (fun delta hdelta => hUniformPP delta hdelta (width delta)
        (hwidthLegal delta hdelta).1 (hwidthLegal delta hdelta).2)

end
end ImbalancedChen.P4BCurrentBadUpperSuppliers
