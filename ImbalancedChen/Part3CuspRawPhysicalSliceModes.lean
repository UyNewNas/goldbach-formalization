import ImbalancedChen.Part3CuspRawWeakDerivativeBridge

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The raw distributional equation determines Fourier modes of the ORIGINAL
physical Lp representatives on almost every actual height slice. Genuine
product Fubini first gives L² circle slices for both physical components.
AE zero-extension identities are then sliced after swapping the actual
product measure, and the countable all-integer native equation is moved
back to those original slices. One raw-AE height set works for every n.
There is no chart derivative, slice weak equation, or coefficient premise.
-/
namespace ImbalancedChen.Part3.CuspRawPhysicalSliceModes20261026b
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open ActualCylinderModeEmbeddings20261026a ActualCylinderFourierCoefficients20261026a
open CuspPhysicalWeakTailModes20261026b CuspWeakCylinderFourierModes20261026b
open CuspRawWeakDerivativeBridge20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

/-- Weighted product Fubini supplies the actual value slices. Positive
height density then gives the same raw-AE exceptional set convention. -/
theorem physical_value_slices_memLp (a : ℝ) (u : FunctionL2 a) :
    ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      MemLp (fun x : UnitAddCircle => u (x, y)) 2 AddCircle.haarAddCircle := by
  have hsq : Integrable (fun z : CuspCylinder => ‖u z‖^2) (functionMeasure a) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  rw [functionMeasure_product] at hsq
  have hl2 : ∀ᵐ y ∂heightMeasure.restrict (strictHeightTail a),
      MemLp (fun x : UnitAddCircle => u (x, y)) 2 AddCircle.haarAddCircle := by
    filter_upwards [hsq.prod_right_ae] with y hy
    exact (memLp_two_iff_integrable_sq_norm
      ((Lp.stronglyMeasurable u).comp_measurable measurable_prodMk_right).aestronglyMeasurable).mpr hy
  exact heightMeasure_ae_iff_volume.mp
    ((ae_restrict_iff' (strictHeightTail_measurable a)).mp hl2)

/-- Raw product Fubini supplies the physical derivative slices directly. -/
theorem physical_derivative_slices_memLp (a : ℝ) (d : DerivativeL2 a) :
    ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      MemLp (fun x : UnitAddCircle => d (x, y)) 2 AddCircle.haarAddCircle := by
  have hsq : Integrable (fun z : CuspCylinder => ‖d z‖^2) (derivativeMeasure a) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable d)).mp (Lp.memLp d)
  rw [derivativeMeasure_product] at hsq
  have hl2 : ∀ᵐ y ∂(volume : Measure PositiveHeight).restrict (strictHeightTail a),
      MemLp (fun x : UnitAddCircle => d (x, y)) 2 AddCircle.haarAddCircle := by
    filter_upwards [hsq.prod_right_ae] with y hy
    exact (memLp_two_iff_integrable_sq_norm
      ((Lp.stronglyMeasurable d).comp_measurable measurable_prodMk_right).aestronglyMeasurable).mpr hy
  exact (ae_restrict_iff' (strictHeightTail_measurable a)).mp hl2

/-- The distributional cylinder tensor equation implies the actual
Fourier identity on ONE raw-AE height set for ALL integer n, with actual
L² slice regularity proved in the same statement. -/
theorem raw_weak_all_integer_physical_modes {w a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hraw : HasRawWeakPhysicalTailDerivative w a u d) :
    ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      MemLp (fun x : UnitAddCircle => u (x, y)) 2 AddCircle.haarAddCircle ∧
      MemLp (fun x : UnitAddCircle => d (x, y)) 2 AddCircle.haarAddCircle ∧
      ∀ n : ℤ,
        (w : ℂ) * AddCircle.fourierCoeff (fun x : UnitAddCircle => d (x, y)) n =
          modeFrequency n * AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n := by
  have hFswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂heightMeasure.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
      tailValue a u (p.2, p.1) = (strictCylinderTail a).indicator u (p.2, p.1) :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving).ae (tailValue_ae a u)
  have hG : ∀ᵐ z ∂cylinderMeasure,
      ((w : ℂ) • tailDerivative a ha d : CylinderL2) z =
        (strictCylinderTail a).indicator (fun z => (w : ℂ) * d z) z := by
    filter_upwards [Lp.coeFn_smul (w : ℂ) (tailDerivative a ha d),
      tailDerivative_ae a ha d] with z hs hd
    simp only [hs, Pi.smul_apply, smul_eq_mul, hd]
    by_cases hz : z ∈ strictCylinderTail a <;> simp [hz]
  have hGswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂heightMeasure.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
      ((w : ℂ) • tailDerivative a ha d : CylinderL2) (p.2, p.1) =
        (strictCylinderTail a).indicator (fun z => (w : ℂ) * d z) (p.2, p.1) :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving).ae hG
  have hFslice := heightMeasure_ae_iff_volume.mp (ae_ae_of_ae_prod hFswap)
  have hGslice := heightMeasure_ae_iff_volume.mp (ae_ae_of_ae_prod hGswap)
  have hmode := physical_tail_all_modes_raw_ae ha (raw_weak_implies_weighted hraw)
  filter_upwards [physical_value_slices_memLp a u, physical_derivative_slices_memLp a d,
    hFslice, hGslice, hmode] with y hU hD hF hG hn
  intro hy
  refine ⟨hU hy, hD hy, ?_⟩
  have hfu : (fun x : UnitAddCircle => tailValue a u (x, y)) =ᵐ[AddCircle.haarAddCircle]
      (fun x => u (x, y)) := by
    filter_upwards [hF] with x hx
    simpa [strictCylinderTail, strictHeightTail, hy] using hx
  have hgd : (fun x : UnitAddCircle => ((w : ℂ) • tailDerivative a ha d : CylinderL2) (x, y))
      =ᵐ[AddCircle.haarAddCircle] (fun x => (w : ℂ) * d (x, y)) := by
    filter_upwards [hG] with x hx
    simpa [strictCylinderTail, strictHeightTail, hy] using hx
  intro n
  have h := hn n
  change AddCircle.fourierCoeff
      (fun x : UnitAddCircle => ((w : ℂ) • tailDerivative a ha d : CylinderL2) (x, y)) n =
      modeFrequency n * AddCircle.fourierCoeff (fun x : UnitAddCircle => tailValue a u (x, y)) n at h
  rw [congrFun (AddCircle.fourierCoeff_congr_ae hgd) n,
    congrFun (AddCircle.fourierCoeff_congr_ae hfu) n,
    AddCircle.fourierCoeff.const_mul] at h
  exact h

/-- In period-one physical coordinates this is exactly G_n = 2π i n F_n
on one AE set for every integer n, including zero. -/
theorem raw_weak_unit_all_integer_modes {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hraw : HasRawWeakPhysicalTailDerivative 1 a u d) :
    ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) → ∀ n : ℤ,
      AddCircle.fourierCoeff (fun x : UnitAddCircle => d (x, y)) n =
        (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
          AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n := by
  filter_upwards [raw_weak_all_integer_physical_modes ha hraw] with y hy
  intro hay
  simpa only [Complex.ofReal_one, one_mul, modeFrequency] using (hy hay).2.2

/-- The original physical derivative has zero normalized-Haar mean,
without imposing a mean-zero premise on the original value. -/
theorem raw_weak_physical_derivative_zero_mean {w a : ℝ} (hw : w ≠ 0) (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hraw : HasRawWeakPhysicalTailDerivative w a u d) :
    ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, d (x, y) ∂AddCircle.haarAddCircle) = 0 := by
  filter_upwards [raw_weak_all_integer_physical_modes ha hraw] with y hy
  intro hay
  have hz : (w : ℂ) * AddCircle.fourierCoeff (fun x : UnitAddCircle => d (x, y)) 0 = 0 := by
    simpa [modeFrequency] using (hy hay).2.2 0
  have hcoeff := (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hw)
  simpa [AddCircle.fourierCoeff, AddCircle.fourier_zero] using hcoeff

end
end ImbalancedChen.Part3.CuspRawPhysicalSliceModes20261026b
