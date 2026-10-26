import ImbalancedChen.Part3ActualCylinderClosedDirichletParseval
import ImbalancedChen.Part3RadialClosedEnergyQuarterShear

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual all-vector gradient integration by parts in L2(dx dy/y^2).
For V=y*d/dy the adjoint is 1-V; for H=y*d/dx it is -H.
The native one-mode identities follow from the actual weak radial
derivative and real exponential multiplier graphs. Genuine convergent
Fourier reconstruction extends them to the actual closed cylinder domain.
No full-domain integration-by-parts or gradient premise is supplied.
-/

namespace ImbalancedChen.Part3.ActualCylinderClosedGradientGreen20261026b
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z CuspCylinderBesselMode20261024z
open CuspModePhysicalCoreForm20261026a CuspModeNativeClosedForm20261026a
open RadialSchrodingerL2Form20261025a RadialClosedEnergyQuarterShear20261026a
open WeightedHeightNativeUnitary20261026a
open ActualCylinderModeEmbeddings20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open ActualCylinderFiniteEnergyCore20261026b
open ActualCylinderClosedEnergyHilbertSum20261026b
open ActualCylinderClosedDirichletParseval20261026b

theorem radial_closed_exponential_symmetric (d e : radialClosedEnergyDomain 1) :
    inner ℂ (radialClosedExponential 1 d) (radialPhysicalEmbedding 1 e) =
      inner ℂ (radialPhysicalEmbedding 1 d) (radialClosedExponential 1 e) := by
  have hd := (radialClosedEnergyDomain_le_good 1 (by norm_num) d.property).2
  have he := (radialClosedEnergyDomain_le_good 1 (by norm_num) e.property).2
  change (radialClosedExponential 1 d : ℝ → ℂ) =ᵐ[volume]
    exponentialProduct (radialPhysicalEmbedding 1 d) at hd
  change (radialClosedExponential 1 e : ℝ → ℂ) =ᵐ[volume]
    exponentialProduct (radialPhysicalEmbedding 1 e) at he
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hd, he] with r hrD hrE
  simp only [RCLike.inner_apply', hrD, hrE, exponentialProduct, map_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

theorem mode_vertical_Green (n : NonzeroMode) (d e : ModeEnergy n) :
    inner ℂ (modeVertical n d) (modeValue n e) +
      inner ℂ (modeValue n d) (modeVertical n e) =
        inner ℂ (modeValue n d) (modeValue n e) := by
  obtain ⟨dR, rfl⟩ := (physicalClosedEnergyEquiv (frequencyScale n)
    (frequencyScale_pos n.property)).surjective d
  obtain ⟨eR, rfl⟩ := (physicalClosedEnergyEquiv (frequencyScale n)
    (frequencyScale_pos n.property)).surjective e
  simp only [modeVertical, modeValue, physicalClosedVertical_equiv,
    physicalClosedEmbedding_equiv, (weightedHeightUnitary _ _).symm.inner_map_map]
  unfold radialHalfShiftedDerivative
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [radial_closed_Green]
  norm_num
  ring

theorem physical_closed_potential_symmetric (n : NonzeroMode) (d e : ModeEnergy n) :
    inner ℂ (physicalClosedPotential _ _ d) (modeValue n e) =
      inner ℂ (modeValue n d) (physicalClosedPotential _ _ e) := by
  obtain ⟨dR, rfl⟩ := (physicalClosedEnergyEquiv (frequencyScale n)
    (frequencyScale_pos n.property)).surjective d
  obtain ⟨eR, rfl⟩ := (physicalClosedEnergyEquiv (frequencyScale n)
    (frequencyScale_pos n.property)).surjective e
  simp only [modeValue, physicalClosedPotential_equiv, physicalClosedEmbedding_equiv,
    (weightedHeightUnitary _ _).symm.inner_map_map]
  exact radial_closed_exponential_symmetric dR eR

theorem horizontalPhase_star (n : ℤ) :
    starRingEnd ℂ (horizontalPhase n) = -horizontalPhase n := by
  unfold horizontalPhase
  split_ifs <;> simp

theorem mode_horizontal_Green (n : NonzeroMode) (d e : ModeEnergy n) :
    inner ℂ (modeHorizontal n d) (modeValue n e) +
      inner ℂ (modeValue n d) (modeHorizontal n e) = 0 := by
  simp only [modeHorizontal, ContinuousLinearMap.smul_apply,
    inner_smul_left, inner_smul_right]
  rw [physical_closed_potential_symmetric, horizontalPhase_star]
  ring

def greenMap (j : Fin 3) (c : ℝ) (F : cylinderClosedEnergyDomain) :
    cylinderClosedEnergyDomain →L[ℂ] ℂ :=
  (innerSL ℂ (cylinderClosedCoordinate j F)).comp (cylinderClosedCoordinate 0) +
    (innerSL ℂ (cylinderClosedCoordinate 0 F)).comp (cylinderClosedCoordinate j) -
    (c : ℂ) • (innerSL ℂ (cylinderClosedCoordinate 0 F)).comp (cylinderClosedCoordinate 0)

theorem greenMap_apply (j : Fin 3) (c : ℝ) (F G : cylinderClosedEnergyDomain) :
    greenMap j c F G =
      inner ℂ (cylinderClosedCoordinate j F) (cylinderClosedCoordinate 0 G) +
      inner ℂ (cylinderClosedCoordinate 0 F) (cylinderClosedCoordinate j G) -
      (c : ℂ) * inner ℂ (cylinderClosedCoordinate 0 F) (cylinderClosedCoordinate 0 G) := rfl

theorem greenMap_conj_symm (j : Fin 3) (c : ℝ) (F G : cylinderClosedEnergyDomain) :
    greenMap j c F G = starRingEnd ℂ (greenMap j c G F) := by
  simp only [greenMap_apply, map_add, map_sub, map_mul, inner_conj_symm,
    Complex.conj_ofReal]
  ring

private theorem greenMap_zero_of_modes (j : Fin 3) (c : ℝ)
    (h : ∀ (n m : NonzeroMode) (d : ModeEnergy n) (e : ModeEnergy m),
      greenMap j c (cylinderModeEnergy n d) (cylinderModeEnergy m e) = 0)
    (F G : cylinderClosedEnergyDomain) : greenMap j c F G = 0 := by
  have hmode (n : NonzeroMode) (d : ModeEnergy n) (K : cylinderClosedEnergyDomain) :
      greenMap j c (cylinderModeEnergy n d) K = 0 := by
    have hs := (greenMap j c (cylinderModeEnergy n d)).hasSum
      (actualCylinderEnergyFourier_reconstruction K)
    have hs0 : HasSum (fun _ : NonzeroMode => (0 : ℂ))
        (greenMap j c (cylinderModeEnergy n d) K) := by
      simpa only [h] using hs
    exact hs0.unique hasSum_zero
  have hz (n : NonzeroMode) :
      greenMap j c G (cylinderModeEnergy n (actualCylinderEnergyFourier F n)) = 0 := by
    rw [greenMap_conj_symm, hmode, map_zero]
  have hs := (greenMap j c G).hasSum (actualCylinderEnergyFourier_reconstruction F)
  have hs0 : HasSum (fun _ : NonzeroMode => (0 : ℂ)) (greenMap j c G F) := by
    simpa only [hz] using hs
  rw [greenMap_conj_symm, hs0.unique hasSum_zero, map_zero]

/-- Genuine all-domain vertical integration by parts in dy/y^2.
The +1 term is the actual height-measure divergence correction. -/
theorem cylinder_closed_vertical_Green (F G : cylinderClosedEnergyDomain) :
    inner ℂ (cylinderClosedCoordinate 1 F) (cylinderClosedCoordinate 0 G) +
      inner ℂ (cylinderClosedCoordinate 0 F) (cylinderClosedCoordinate 1 G) =
        inner ℂ (cylinderClosedCoordinate 0 F) (cylinderClosedCoordinate 0 G) := by
  have h : greenMap 1 1 F G = 0 := by
    apply greenMap_zero_of_modes
    intro n m d e
    rw [greenMap_apply]
    change inner ℂ (modeEmbedding n (modeVertical n d)) (modeEmbedding m (modeValue m e)) +
      inner ℂ (modeEmbedding n (modeValue n d)) (modeEmbedding m (modeVertical m e)) -
      (1 : ℂ) * inner ℂ (modeEmbedding n (modeValue n d)) (modeEmbedding m (modeValue m e)) = 0
    simp only [modeEmbedding_inner, Subtype.val_injective.eq_iff]
    by_cases hnm : n = m
    · subst m
      simp only [if_pos rfl, one_mul]
      linear_combination mode_vertical_Green n d e
    · simp [hnm]
  simpa only [greenMap_apply, Complex.ofReal_one, one_mul, sub_eq_zero] using h

/-- Genuine all-domain horizontal integration by parts; the signed
Fourier phase is retained, and there is no height-divergence correction. -/
theorem cylinder_closed_horizontal_Green (F G : cylinderClosedEnergyDomain) :
    inner ℂ (cylinderClosedCoordinate 2 F) (cylinderClosedCoordinate 0 G) =
      -inner ℂ (cylinderClosedCoordinate 0 F) (cylinderClosedCoordinate 2 G) := by
  have h : greenMap 2 0 F G = 0 := by
    apply greenMap_zero_of_modes
    intro n m d e
    rw [greenMap_apply]
    change inner ℂ (modeEmbedding n (modeHorizontal n d)) (modeEmbedding m (modeValue m e)) +
      inner ℂ (modeEmbedding n (modeValue n d)) (modeEmbedding m (modeHorizontal m e)) -
      (0 : ℂ) * inner ℂ (modeEmbedding n (modeValue n d)) (modeEmbedding m (modeValue m e)) = 0
    simp only [modeEmbedding_inner, Subtype.val_injective.eq_iff, zero_mul, sub_zero]
    by_cases hnm : n = m
    · subst m
      simpa only [if_pos rfl, one_mul] using mode_horizontal_Green n d e
    · simp [hnm]
  have h' : inner ℂ (cylinderClosedCoordinate 2 F) (cylinderClosedCoordinate 0 G) +
      inner ℂ (cylinderClosedCoordinate 0 F) (cylinderClosedCoordinate 2 G) = 0 := by
    simpa only [greenMap_apply, Complex.ofReal_zero, zero_mul, sub_zero] using h
  linear_combination h'

end
end ImbalancedChen.Part3.ActualCylinderClosedGradientGreen20261026b
