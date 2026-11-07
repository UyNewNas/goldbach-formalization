import ImbalancedChen.Part3ActualCylinderClosedGradientGreen

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual closed whole-cylinder Dirichlet form has the exact quarter
Hardy square decomposition. It follows from genuine closed-gradient
integration by parts, without a spectral lower-bound hypothesis.
For the zero-horizontal-mean realization the endpoint is never attained
by a nonzero form-domain vector: its actual horizontal gradient is
injective. This is not a Gamma quotient gap or a truncated-cusp claim.
-/

namespace ImbalancedChen.Part3.ActualCylinderClosedHardyQuarter20261026b
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z CuspCylinderBesselMode20261024z
open CuspModePhysicalCoreForm20261026a CuspModeNativeClosedForm20261026a
open RadialSchrodingerL2Form20261025a WeightedHeightNativeUnitary20261026a
open ActualCylinderModeEmbeddings20261026a ActualCylinderFourierCoefficients20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open ActualCylinderFiniteEnergyCore20261026b
open ActualCylinderClosedEnergyHilbertSum20261026b
open ActualCylinderClosedDirichletParseval20261026b
open ActualCylinderClosedGradientGreen20261026b

theorem modeClosedPotential_zero (n : NonzeroMode) (d : ModeEnergy n)
    (hp : physicalClosedPotential _ _ d = 0) : d = 0 := by
  obtain ⟨dR, rfl⟩ := (physicalClosedEnergyEquiv (frequencyScale n)
    (frequencyScale_pos n.property)).surjective d
  rw [physicalClosedPotential_equiv] at hp
  have hpR : radialClosedExponential 1 dR = 0 := by
    simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using
      congrArg (weightedHeightUnitary (frequencyScale n) (frequencyScale_pos n.property)) hp
  have hgraph := (radialClosedEnergyDomain_le_good 1 (by norm_num) dR.property).2
  change (radialClosedExponential 1 dR : ℝ → ℂ) =ᵐ[volume]
    exponentialProduct (radialPhysicalEmbedding 1 dR) at hgraph
  rw [hpR] at hgraph
  have hf : radialPhysicalEmbedding 1 dR = 0 := by
    apply Lp.ext
    have hzero : (radialPhysicalEmbedding 1 dR : ℝ → ℂ) =ᵐ[volume] (fun _ => 0) := by
      filter_upwards [hgraph, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with r hr hz
      rw [hz] at hr
      have he : (Real.exp r : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos r).ne'
      exact (mul_eq_zero.mp hr.symm).resolve_left he
    exact hzero.trans (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)).symm
  have hdR : dR = 0 := (radialPhysicalEmbedding_injective 1 (by norm_num))
    (by simpa only [map_zero] using hf)
  simp only [hdR, map_zero]

/-- The horizontal gradient of the actual nonzero-mode cylinder form has
zero kernel. Positivity of exp(r) is used on actual L2 representatives. -/
theorem cylinderClosedHorizontal_zero (F : cylinderClosedEnergyDomain)
    (hH : cylinderClosedCoordinate 2 F = 0) : F = 0 := by
  apply actualCylinderEnergyFourier.injective
  ext n
  rw [map_zero]
  change actualCylinderEnergyFourier F n = 0
  have hc := cylinderClosedCoordinate_coefficient 2 F n
  rw [hH, map_zero] at hc
  have hm : modeHorizontal n (actualCylinderEnergyFourier F n) = 0 := hc.symm
  have hp : physicalClosedPotential _ _ (actualCylinderEnergyFourier F n) = 0 := by
    have h := congrArg (fun g : HeightL2 => star (horizontalPhase n) • g) hm
    change star (horizontalPhase n) • (horizontalPhase n •
      physicalClosedPotential _ _ (actualCylinderEnergyFourier F n)) =
        star (horizontalPhase n) • (0 : HeightL2) at h
    simpa only [smul_smul, horizontalPhase_unit, one_smul, smul_zero] using h
  exact modeClosedPotential_zero n (actualCylinderEnergyFourier F n) hp

def closedVerticalHalfShear : cylinderClosedEnergyDomain →L[ℂ] CylinderL2 :=
  cylinderClosedCoordinate 1 - (1 / 2 : ℂ) • cylinderClosedCoordinate 0

/-- Exact polarized Hardy identity on the genuine complete form domain. -/
theorem closedDirichletForm_quarter_square (F G : cylinderClosedEnergyDomain) :
    closedDirichletForm F G =
      inner ℂ (closedVerticalHalfShear F) (closedVerticalHalfShear G) +
      inner ℂ (cylinderClosedCoordinate 2 F) (cylinderClosedCoordinate 2 G) +
      (1 / 4 : ℂ) * inner ℂ (cylinderClosedValue F) (cylinderClosedValue G) := by
  have h := cylinder_closed_vertical_Green F G
  change inner ℂ (cylinderClosedCoordinate 1 F) (cylinderClosedCoordinate 1 G) +
    inner ℂ (cylinderClosedCoordinate 2 F) (cylinderClosedCoordinate 2 G) =
      inner ℂ (cylinderClosedCoordinate 1 F - (1 / 2 : ℂ) • cylinderClosedCoordinate 0 F)
        (cylinderClosedCoordinate 1 G - (1 / 2 : ℂ) • cylinderClosedCoordinate 0 G) +
      inner ℂ (cylinderClosedCoordinate 2 F) (cylinderClosedCoordinate 2 G) +
      (1 / 4 : ℂ) * inner ℂ (cylinderClosedCoordinate 0 F) (cylinderClosedCoordinate 0 G)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  norm_num
  linear_combination (1 / 2 : ℂ) * h

theorem closedDirichletForm_re_quarter_square (F : cylinderClosedEnergyDomain) :
    (closedDirichletForm F F).re =
      ‖closedVerticalHalfShear F‖ ^ 2 + ‖cylinderClosedCoordinate 2 F‖ ^ 2 +
        (1 / 4 : ℝ) * ‖cylinderClosedValue F‖ ^ 2 := by
  have h := congrArg Complex.re (closedDirichletForm_quarter_square F F)
  norm_num [inner_self_eq_norm_sq_to_K, Complex.mul_re] at h
  exact h

theorem closedDirichletForm_quarter_floor (F : cylinderClosedEnergyDomain) :
    (1 / 4 : ℝ) * ‖cylinderClosedValue F‖ ^ 2 ≤ (closedDirichletForm F F).re := by
  rw [closedDirichletForm_re_quarter_square]
  nlinarith [sq_nonneg ‖closedVerticalHalfShear F‖,
    sq_nonneg ‖cylinderClosedCoordinate 2 F‖]

/-- The endpoint is strict for each nonzero form vector; this does not
claim a uniform larger spectral gap above one quarter. -/
theorem closedDirichletForm_strict_quarter (F : cylinderClosedEnergyDomain) (hF : F ≠ 0) :
    (1 / 4 : ℝ) * ‖cylinderClosedValue F‖ ^ 2 < (closedDirichletForm F F).re := by
  have hH : cylinderClosedCoordinate 2 F ≠ 0 := fun hz => hF (cylinderClosedHorizontal_zero F hz)
  have hpos : 0 < ‖cylinderClosedCoordinate 2 F‖ ^ 2 := pow_pos (norm_pos_iff.mpr hH) 2
  rw [closedDirichletForm_re_quarter_square]
  nlinarith [sq_nonneg ‖closedVerticalHalfShear F‖]

end
end ImbalancedChen.Part3.ActualCylinderClosedHardyQuarter20261026b
