import ImbalancedChen.P4BSmoothPhysicalMassReserve
import ImbalancedChen.P4BSmoothOuterRampRoughness
import ImbalancedChen.P4BLabelledOuterPPUpperAssembly

/-!
# The actual smooth physical outer source: final same-rho upper consumer

The physical outer weight is the literal product of mathlib's smooth
transition functions applied to the actual affine log margins. Arithmetic
mass and the coprime correction are proved suppliers. The source keeps
all products, including products above N, through the integer-shift bridge.

Two upstream estimates remain explicit: the actual P4A density bound and
the genuine signed PP target for this smooth source. No PP licensing or
spectral estimate is asserted here. In particular C-infinity regularity
alone is not used as a distribution theorem.

SOURCE ONLY / YELLOW / UNCOMPILED; not an unconditional hUpper declaration.
-/

namespace ImbalancedChen.P4BCurrentSmoothBadUpperSuppliers

noncomputable section
open Filter Topology
open scoped BigOperators
open Part3 P4BLabelledOuterPushforward

theorem current_realBad_upper_of_actual_density_and_uniform_smooth_PP
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
        (fun N _ => P4B.smoothPhysicalPairOuterRamp b N
          (manuscriptHalfProductCutoff kappa N) physicalWidth)) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  have hb : 0 < b := by linarith only [hbLower]
  have hden : 0 < 1 + b := by linarith only [hb]
  have hbaseline : (1 - kappa) * b / (1 + b) < 1 := by
    apply (div_lt_iff₀ hden).2
    have hpositive := mul_pos hkappa hb
    nlinarith only [hpositive]
  have hsieve : nu * r < 1 := hgap.trans hbaseline
  let widthMax : ℝ := ((1 - kappa) * b / (1 + b) - nu * r) / 2
  have hwidthMax : 0 < widthMax := by dsimp [widthMax]; linarith
  let width : ℝ → ℝ := fun delta =>
    if hdelta : 0 < delta then
      Classical.choose (P4B.exists_smooth_physical_ramp_mass_reserve
        hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)
    else 1
  have hwidthPos : ∀ delta : ℝ, 0 < delta → 0 < width delta := by
    intro delta hdelta
    dsimp only [width]
    rw [dif_pos hdelta]
    exact (Classical.choose_spec (P4B.exists_smooth_physical_ramp_mass_reserve
      hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)).1
  have hwidthLe : ∀ delta : ℝ, 0 < delta → width delta ≤ widthMax := by
    intro delta hdelta
    dsimp only [width]
    rw [dif_pos hdelta]
    exact (Classical.choose_spec (P4B.exists_smooth_physical_ramp_mass_reserve
      hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)).2.1
  have hwidthGap : ∀ delta : ℝ, 0 < delta →
      2 * width delta ≤ (1 - kappa) * b / (1 + b) - nu * r := by
    intro delta hdelta
    have hle := hwidthLe delta hdelta
    dsimp only [widthMax] at hle
    linarith
  apply P4BLabelledOuterPPUpperAssembly.eventually_RealB_le_of_actual_labelled_outer_uniformPP
    hb hbUpper hkappa hnu hr hsieve epsilon retain cap
    (fun delta N => P4B.smoothPhysicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) (width delta)) hepsilon hcap
  · intro delta _hdelta
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N _hN
    intro _hEven t _ht
    exact (P4B.smoothPhysicalPairOuterRamp_bounds b N _ _ t).1
  · intro delta hdelta
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    intro _hEven t ht
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
    have hT : 0 < manuscriptHalfProductCutoff kappa N :=
      mul_pos (by norm_num) (Real.rpow_pos_of_pos hNpos _)
    exact P4B.actual_W_le_smoothPhysicalPairOuterRamp hN1 hT
      (hwidthPos delta hdelta) ht
  · intro delta hdelta
    obtain ⟨N0, _hN0, hmass⟩ :=
      (Classical.choose_spec (P4B.exists_smooth_physical_ramp_mass_reserve
        hbLower hbUpper hkappa hkappaOne delta widthMax hdelta hwidthMax)).2.2
    filter_upwards [eventually_ge_atTop N0] with N hN
    intro hEven
    simpa only [width, dif_pos hdelta] using hmass N hN hEven
  · exact hdensity
  · intro delta hdelta
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    intro _hEven
    have hlegal : 2 * width delta ≤
        P4BOuterRampRoughness.baseline b kappa - nu * r :=
      hwidthGap delta hdelta
    have hzero := P4BSmoothOuterRampRoughness.smooth_physical_ramp_outer_signed_coprime_sum_eq_zero
      hb hnu hN (hepsilon delta hdelta).2.2 (hwidthPos delta hdelta) hlegal
      (retain delta) (cap delta)
    rw [hzero, abs_zero]
    apply mul_nonneg hdelta.le
    have hseries := (singularSeries_pos N).le
    unfold singularNormalization
    positivity
  · intro delta hdelta
    exact hUniformPP delta hdelta (width delta) (hwidthPos delta hdelta)
      (hwidthGap delta hdelta)

end
end ImbalancedChen.P4BCurrentSmoothBadUpperSuppliers
