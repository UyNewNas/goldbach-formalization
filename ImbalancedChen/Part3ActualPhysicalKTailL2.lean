import ImbalancedChen.Part3ActualPhysicalKJets
import ImbalancedChen.Part3GeneralKRightEndpoint
import ImbalancedChen.Part3ActualFourierBesselLogL2
import ImbalancedChen.Part3ShiftOneEulerTailSelection

/-!
# Actual physical K has literal dy/y^2 tail L2 at every complex order

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual radial K is L2 on r>0. Its genuine C2 regularity supplies the
finite compact interval needed for any logarithmic lower endpoint.
The proved actual Jacobian transports that norm to the literal physical
reference sqrt(y)K_nu(a*y), with NO remaining scale factor a.
The public native MemLp conclusion uses the existing literal real-carrier
physicalTailMeasure=(dy/y^2)|y>1. No scalar classification is used.
-/

namespace ImbalancedChen.Part3.ActualPhysicalKTailL220261026b

noncomputable section
open Set MeasureTheory Filter
open ActualPhysicalKJets20261026b ComplexOrderKRadialRegularitySourceOnly
open GeneralKRightEndpoint20261025a ActualFourierBesselConjugation20261026a
open ActualFourierBesselLogL220261026a ShiftOneEulerTailSelection20261026b

/-- Actual K mass on ANY logarithmic tail: compact C2 mass fills the
finite part omitted by the established r>0 moment bound. -/
theorem radialK_sq_integrableOn_any_tail (nu : ℂ) (R : ℝ) :
    IntegrableOn (fun r : ℝ => ‖radialK nu r‖^2) (Ioi R) := by
  have hc := (radialK_C2 nu).continuous
  have hright : IntegrableOn (fun r : ℝ => ‖radialK nu r‖^2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable.restrict).mp
      (radialK_memLp_two_Ioi nu)
  have hcompact : IntegrableOn (fun r : ℝ => ‖radialK nu r‖^2) (Icc R 0) :=
    (hc.norm.pow 2).integrableOn_Icc
  apply (hcompact.union hright).mono_set
  intro r hr
  by_cases hpos : 0<r
  · exact Or.inr hpos
  · exact Or.inl ⟨hr.le,le_of_not_gt hpos⟩

/-- Exact normalized physical log transform of the literal K reference.
No frequency factor remains after sqrt(y) normalization. -/
theorem physicalK_logarithmicMode (nu : ℂ) {a : ℝ} (ha : 0<a) (r : ℝ) :
    logarithmicMode (physicalK nu a) a r=radialK nu r := by
  have hy : 0<Real.exp r/a := div_pos (Real.exp_pos r) ha
  have hs : a*(Real.exp r/a)=Real.exp r := by field_simp [ha.ne']
  have hp : heightPower (-1/2) (Real.exp r/a)*(Real.sqrt (Real.exp r/a) : ℂ)=1 := by
    have hr : (Real.exp r/a)^(-1/2 : ℝ)*Real.sqrt (Real.exp r/a)=1 := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_add hy]
      norm_num
    dsimp [heightPower]
    exact_mod_cast hr
  simp only [logarithmicMode,besselTransform,normalizedHeight,physicalK,hs,
    ← mul_assoc,hp,one_mul,radialK]

/-- Actual physical raw dy/y^2 tail square norm is finite at EVERY
positive lower height, uniformly in the type of complex order. -/
theorem physicalK_heightEnergy_integrable (nu : ℂ) {a Y : ℝ}
    (ha : 0<a) (hY : 0<Y) :
    IntegrableOn (fun y : ℝ => y⁻¹^2*‖physicalK nu a y‖^2) (Ioi Y) := by
  have hlog : IntegrableOn
      (fun r : ℝ => ‖logarithmicMode (physicalK nu a) a r‖^2)
      (Ioi (Real.log (a*Y))) := by
    simpa only [physicalK_logarithmicMode nu ha] using
      radialK_sq_integrableOn_any_tail nu (Real.log (a*Y))
  have hm := (logarithmicMode_sq_integrable_iff (physicalK nu a) ha (Real.log (a*Y))).mp hlog
  simpa only [heightEnergy,Real.exp_log (mul_pos ha hY),
    mul_div_cancel_left₀ _ ha.ne'] using hm

/-- Exact physical mass equality, not merely a bound or a default-zero
integral comparison; integrability is independently proved above. -/
theorem physicalK_heightEnergy_integral (nu : ℂ) {a Y : ℝ}
    (ha : 0<a) (hY : 0<Y) :
    (∫ y in Ioi Y, y⁻¹^2*‖physicalK nu a y‖^2)=
      ∫ r in Ioi (Real.log (a*Y)), ‖radialK nu r‖^2 := by
  simpa only [physicalK_logarithmicMode nu ha] using
    (logarithmicMode_energy_exact (c := physicalK nu a) ha hY).symm

/-- Native MemLp of the ACTUAL reference in the existing literal
physicalTailMeasure = dy/y^2 on y>1. All complex orders are allowed. -/
theorem physicalK_memLp_two_physicalTail (nu : ℂ) {a : ℝ} (ha : 0<a) :
    MemLp (physicalK nu a) 2 physicalTailMeasure := by
  have hcont : ContinuousOn (physicalK nu a) (Ioi (1 : ℝ)) :=
    (physicalK_contDiffOn_two nu ha).continuousOn.mono
      (fun y hy => zero_lt_one.trans hy)
  have hAS0 := hcont.aestronglyMeasurable measurableSet_Ioi
  have hAS : AEStronglyMeasurable (physicalK nu a) physicalTailMeasure :=
    AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _) hAS0
  rw [memLp_two_iff_integrable_sq_norm hAS]
  change Integrable (fun y : ℝ => ‖physicalK nu a y‖^2)
    (((volume : Measure ℝ).restrict (Ioi (1 : ℝ))).withDensity
      (fun y => (tailDensity y : ℝ≥0∞)))
  rw [integrable_withDensity_iff_integrable_smul₀ tailDensity_measurable.aemeasurable]
  change IntegrableOn (fun y : ℝ => y⁻¹^2*‖physicalK nu a y‖^2) (Ioi (1 : ℝ))
  exact physicalK_heightEnergy_integrable nu ha zero_lt_one

end
end ImbalancedChen.Part3.ActualPhysicalKTailL220261026b
