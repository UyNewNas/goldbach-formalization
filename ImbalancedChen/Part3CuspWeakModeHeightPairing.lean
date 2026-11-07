import ImbalancedChen.Part3CuspVerticalFourierWeakCoefficients
import ImbalancedChen.Part3CuspRawPhysicalSliceModes

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual compact height pairings for the native Fourier value coefficient
of an arbitrary physical weighted L² vector. Weighted character Fubini
and the literal dy/y² density give the ORIGINAL raw-height y^-2 term.
Raw and density-weighted test integrabilities are proved, not assumed.
This supplies the spectral-parameter term of a genuine weak mode equation;
it contains no mode ODE, eigenfunction smoothness or spectral assumption.
-/
namespace ImbalancedChen.Part3.CuspWeakModeHeightPairing20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open ActualCylinderModeEmbeddings20261026a ActualCylinderFourierCoefficients20261026a
open CuspPhysicalWeakTailModes20261026b CuspRawWeakDerivativeBridge20261026b
open CuspCompactHeightTestDetection20261026b CuspVerticalFourierWeakCoefficients20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def valueMode (a : ℝ) (n : ℤ) (u : FunctionL2 a) (y : PositiveHeight) : ℂ :=
  sliceCoefficient n (tailValue a u) y

def verticalMode (a : ℝ) (ha : 0 < a) (n : ℤ) (dy : DerivativeL2 a) (y : PositiveHeight) : ℂ :=
  sliceCoefficient n (tailDerivative a ha dy) y

theorem weightedHeightTail_eq_density (a : ℝ) :
    heightMeasure.restrict (strictHeightTail a) =
      (rawHeightTail a).withDensity (fun y => (heightDensity y : ℝ≥0∞)) :=
  restrict_withDensity (strictHeightTail_measurable a) _

theorem weightedHeightTail_ac_raw (a : ℝ) :
    heightMeasure.restrict (strictHeightTail a) ≪ rawHeightTail a := by
  rw [weightedHeightTail_eq_density]
  exact withDensity_absolutelyContinuous _ _

theorem valueMode_test_raw_integrable {a : ℝ} (ha : 0 < a) (n : ℤ) (u : FunctionL2 a)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    Integrable (fun y : PositiveHeight => (β (y : ℝ) : ℂ) * valueMode a n u y) (rawHeightTail a) := by
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  have hi := physical_character_height_pairing_integrable a u (Lp.memLp u) n hβ hc hpos
  apply hi.congr
  filter_upwards [zeroExtension_sliceCoefficients_on_tail a (tailValue a u) u (tailValue_ae a u)]
    with y hy
  rw [show valueMode a n u y = AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n from hy n]

theorem valueMode_test_weighted_integrable {a : ℝ} (ha : 0 < a) (n : ℤ) (u : FunctionL2 a)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    Integrable (fun y : PositiveHeight => (β (y : ℝ) : ℂ) * valueMode a n u y)
      (heightMeasure.restrict (strictHeightTail a)) := by
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  exact ((heightTest_memLp hβ hc hpos).restrict (strictHeightTail a)).integrable_mul
    ((sliceCoefficient_memLp n (tailValue a u)).restrict (strictHeightTail a))

theorem valueMode_density_test_integrable {a : ℝ} (ha : 0 < a) (n : ℤ) (u : FunctionL2 a)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    Integrable (fun y : PositiveHeight =>
      ((β (y : ℝ) * (1 / (y : ℝ))^2 : ℝ) : ℂ) * valueMode a n u y) (rawHeightTail a) := by
  have hi := valueMode_test_weighted_integrable ha n u hβ hc hs
  rw [weightedHeightTail_eq_density] at hi
  have hd := (integrable_withDensity_iff_integrable_smul heightDensity_continuous.measurable).mp hi
  apply hd.congr
  exact Eventually.of_forall fun y => by
    simp only [NNReal.smul_def, Complex.real_smul, heightDensity_coe, Complex.ofReal_mul]
    ring

/-- The weighted cylinder character integral is the literal raw-height
y^-2 pairing of the ACTUAL native value mode, with genuine Fubini. -/
theorem weighted_character_native_height_pairing {a : ℝ} (ha : 0 < a) (n : ℤ) (u : FunctionL2 a)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * AddCircle.fourier (-n) z.1 * u z
      ∂functionMeasure a) =
      ∫ y : PositiveHeight, ((β (y : ℝ) * (1 / (y : ℝ))^2 : ℝ) : ℂ) *
        valueMode a n u y ∂rawHeightTail a := by
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  have hi := weighted_tensor_integrable a u (Lp.memLp u) (AddCircle.fourier (-n)) hβ hc hpos
  have hcoeff := (zeroExtension_sliceCoefficients_on_tail a (tailValue a u) u (tailValue_ae a u)).filter_mono
    (weightedHeightTail_ac_raw a).ae_le
  calc
    _ = ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) *
        AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n
          ∂heightMeasure.restrict (strictHeightTail a) := by
      rw [functionMeasure_product] at hi ⊢
      rw [integral_prod_symm _ hi]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp_rw [mul_assoc]
        rw [integral_const_mul]
        rfl
    _ = ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) * valueMode a n u y
        ∂heightMeasure.restrict (strictHeightTail a) := by
      apply integral_congr_ae
      filter_upwards [hcoeff] with y hy
      rw [show valueMode a n u y = AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n from hy n]
    _ = _ := by
      rw [weightedHeightTail_eq_density,
        integral_withDensity_eq_integral_smul heightDensity_continuous.measurable]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        simp only [NNReal.smul_def, Complex.real_smul, heightDensity_coe, Complex.ofReal_mul]
        ring

end
end ImbalancedChen.Part3.CuspWeakModeHeightPairing20261026b
