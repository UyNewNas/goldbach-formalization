import ImbalancedChen.Part3CuspArbitraryAELiftToRealChart

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An arbitrary real-chart field which is integer-periodic only AE descends
through the literal Ico circle representative. Countability supplies ONE
conull chart set for every integer shift; choosing the floor at a point
then proves that the canonical circle field's real lift equals the
ORIGINAL raw field AE. No pointwise measurability, seam trace or classical
derivative is imposed. Native physical AE licences can therefore be
joined to the genuine chart weak equation by the preceding QMP bridge.
-/
namespace ImbalancedChen.Part3.AEPeriodicChartCanonicalDescent20261026b
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z ClosedHorizontalCuspTail20261026a
open ProductConvolutionSecondDerivatives20261026a PeriodicCompactChartTests20261026b
open RealChartToPhysicalCuspWeak20261026b AERealChartPhysicalWeakTransfer20261026b
open CuspArbitraryAELiftToRealChart20261026b CuspRawWeakDerivativeBridge20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def canonicalCircleField (G : Plane → ℂ) (z : CuspCylinder) : ℂ :=
  AddCircle.liftIco (1 : ℝ) 0 (fun x => G (x, (z.2 : ℝ))) z.1

theorem canonicalCircleField_coe (G : Plane → ℂ) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (y : PositiveHeight) :
    canonicalCircleField G ((x : UnitAddCircle), y) = G (x, (y : ℝ)) :=
  AddCircle.liftIco_coe_apply (by simpa only [zero_add] using hx)

private theorem integer_coe_circle_zero (k : ℤ) : ((k : ℝ) : UnitAddCircle) = 0 := by
  calc
    ((k : ℝ) : UnitAddCircle) = ((k • (1 : ℝ) : ℝ) : UnitAddCircle) := by simp
    _ = k • ((1 : ℝ) : UnitAddCircle) := AddCircle.coe_zsmul
    _ = 0 := by rw [AddCircle.coe_period, smul_zero]

/-- AE integer periodicity suffices for a canonical circle representative
to recover the SAME original raw field almost everywhere in the chart. -/
theorem canonicalCircleField_real_lift_ae {a : ℝ} (ha : 0 < a) (G : Plane → ℂ)
    (hperiod : ∀ k : ℤ, ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2},
      G (p.1 + (k : ℝ), p.2) = G p) :
    realCylinderLift (canonicalCircleField G) =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}]
      G := by
  have hall : ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2}, ∀ k : ℤ,
      G (p.1 + (k : ℝ), p.2) = G p := ae_all_iff.mpr hperiod
  filter_upwards [hall, ae_restrict_mem (isOpen_lt continuous_const continuous_snd).measurableSet]
    with p hp hpa
  have hpos : 0 < p.2 := ha.trans hpa
  let k : ℤ := Int.floor p.1
  have hlo : (k : ℝ) ≤ p.1 := Int.floor_le p.1
  have hhi : p.1 < (k : ℝ) + 1 := Int.lt_floor_add_one p.1
  have hx : p.1 - (k : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hcoe : ((p.1 - (k : ℝ) : ℝ) : UnitAddCircle) = (p.1 : UnitAddCircle) := by
    rw [AddCircle.coe_sub, integer_coe_circle_zero, sub_zero]
  rw [realCylinderLift, dif_pos hpos]
  calc
    canonicalCircleField G ((p.1 : UnitAddCircle), ⟨p.2, hpos⟩) =
        canonicalCircleField G (((p.1 - (k : ℝ) : ℝ) : UnitAddCircle), ⟨p.2, hpos⟩) := by rw [hcoe]
    _ = G (p.1 - (k : ℝ), p.2) := canonicalCircleField_coe G hx _
    _ = G p := by simpa only [Int.cast_neg, sub_eq_add_neg] using hp (-k)

theorem native_raw_canonical_chart_match {a : ℝ} (ha : 0 < a) (G : Plane → ℂ)
    (J : CuspCylinder → ℂ)
    (hperiod : ∀ k : ℤ, ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2},
      G (p.1 + (k : ℝ), p.2) = G p)
    (hJ : J =ᵐ[derivativeMeasure a] canonicalCircleField G) :
    G =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift J :=
  ((arbitrary_raw_physical_ae_real_lift ha hJ).trans
    (canonicalCircleField_real_lift_ae ha G hperiod)).symm

theorem native_weighted_canonical_chart_match {a : ℝ} (ha : 0 < a) (G : Plane → ℂ)
    (J : CuspCylinder → ℂ)
    (hperiod : ∀ k : ℤ, ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2},
      G (p.1 + (k : ℝ), p.2) = G p)
    (hJ : J =ᵐ[functionMeasure a] canonicalCircleField G) :
    G =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift J :=
  ((arbitrary_weighted_physical_ae_real_lift ha hJ).trans
    (canonicalCircleField_real_lift_ae ha G hperiod)).symm

/-- Exact native input join once the actual energy/measure suppliers
license u and d, and weak uniqueness supplies integer-periodicity of the
SAME raw chart derivative. No measurability or trace surplus is required. -/
theorem canonical_chart_pair_physical_raw_weak {w a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) (F D : Plane → ℂ)
    (hF : LocallyIntegrableOn F {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hchart : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D)
    (hperiodF : ∀ k : ℤ, ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2},
      F (p.1 + (k : ℝ), p.2) = F p)
    (hperiodD : ∀ k : ℤ, ∀ᵐ p ∂(volume : Measure Plane).restrict {p : Plane | a < p.2},
      D (p.1 + (k : ℝ), p.2) = D p)
    (hvalue : (u : CuspCylinder → ℂ) =ᵐ[functionMeasure a] canonicalCircleField F)
    (hderivative : (fun z : CuspCylinder => (w : ℂ) * d z) =ᵐ[derivativeMeasure a] canonicalCircleField D) :
    HasRawWeakPhysicalTailDerivative w a u d :=
  ae_real_chart_implies_physical_raw_weak ha u d F D hF hD hchart
    (native_weighted_canonical_chart_match ha F u hperiodF hvalue)
    (native_raw_canonical_chart_match ha D _ hperiodD hderivative)

end
end ImbalancedChen.Part3.AEPeriodicChartCanonicalDescent20261026b
