import ImbalancedChen.Part3CuspWeakModeHeightPairing

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine physical H1 tensor eigenvariational equation determines every
Fourier height mode. Actual horizontal weak testing gives dx_n=2πin f_n;
the actual vertical weak equation gives f_n'=dy_n. Inserting the genuine
smooth Fourier tensor into the original variational identity gives the
coupled first-order/distributional mode equation with the ORIGINAL
dy/y² eigenvalue weight. No mode ODE, smooth eigenfunction, spectral
transform or Parseval assertion is assumed.
-/
namespace ImbalancedChen.Part3.CuspTensorEigenWeakModes20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a CuspPhysicalWeakTailModes20261026b
open CuspRawWeakDerivativeBridge20261026b CuspRawPhysicalSliceModes20261026b
open CuspWeakCylinderFourierModes20261026b CuspVerticalWeakCutoffProduct20261026b
open CuspVerticalFourierWeakCoefficients20261026b CuspWeakModeHeightPairing20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def horizontalModeSquare (n : ℤ) : ℝ := (2 * Real.pi * (n : ℝ))^2

/-- The ORIGINAL physical tensor eigenvariational identity: the test is
φ(x)β(y), its true horizontal derivative is ψ(x)β(y), and its true
vertical derivative is φ(x)β'(y). This is not a mode equation premise. -/
def HasPhysicalTensorEigenpair (a λ : ℝ) (u : FunctionL2 a)
    (dx dy : DerivativeL2 a) : Prop :=
  ∀ φ ψ : C(UnitAddCircle, ℂ),
    ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)) →
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) →
    ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioi a →
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * star (ψ z.1) * dx z ∂derivativeMeasure a) +
      (∫ z : CuspCylinder, (deriv β (z.2 : ℝ) : ℂ) * star (φ z.1) * dy z ∂derivativeMeasure a) =
      (λ : ℂ) * (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * star (φ z.1) * u z ∂functionMeasure a)

def HasWeakPhysicalModeEquation (a λ : ℝ) (n : ℤ) (f g : PositiveHeight → ℂ) : Prop :=
  HasWeakHeightDerivativeOnTail a f g ∧
  ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioi a →
    (∫ y, (deriv β (y : ℝ) : ℂ) * g y ∂rawHeightTail a) +
      (horizontalModeSquare n : ℂ) * (∫ y, (β (y : ℝ) : ℂ) * f y ∂rawHeightTail a) =
      (λ : ℂ) * (∫ y, ((β (y : ℝ) * (1 / (y : ℝ))^2 : ℝ) : ℂ) * f y ∂rawHeightTail a)

private theorem character_smooth (n : ℤ) :
    ContDiff ℝ ∞ (fun t : ℝ => AddCircle.fourier n (t : UnitAddCircle)) := by
  simp only [AddCircle.fourier_coe_apply, Complex.ofReal_one, div_one]
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

private theorem character_derivative (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => AddCircle.fourier n (s : UnitAddCircle))
      ((modeFrequency n • AddCircle.fourier n) (t : UnitAddCircle)) t := by
  convert AddCircle.hasDerivAt_fourier (1 : ℝ) n t using 1 <;>
    simp [modeFrequency, smul_eq_mul] <;> ring

private theorem frequency_star_mul (n : ℤ) :
    star (modeFrequency n) * modeFrequency n = (horizontalModeSquare n : ℂ) := by
  let q : ℝ := 2 * Real.pi * (n : ℝ)
  have hω : modeFrequency n = (q : ℂ) * Complex.I := by
    dsimp [modeFrequency, q]
    push_cast
    ring
  calc
    _ = -((q : ℂ)^2 * Complex.I^2) := by rw [hω]; simp [Complex.star_def] <;> ring
    _ = _ := by rw [Complex.I_sq]; simp [horizontalModeSquare, q, Complex.ofReal_pow]

private theorem star_character (n : ℤ) (x : UnitAddCircle) :
    star (AddCircle.fourier n x) = AddCircle.fourier (-n) x := by
  simp only [AddCircle.fourier_neg, Complex.star_def]

theorem horizontal_native_character_pairing {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {dx : DerivativeL2 a}
    (hweak : HasRawWeakPhysicalTailDerivative 1 a u dx) (n : ℤ)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * AddCircle.fourier (-n) z.1 * dx z
      ∂derivativeMeasure a) =
      modeFrequency n * (∫ y, (β (y : ℝ) : ℂ) * valueMode a n u y ∂rawHeightTail a) := by
  have hd : MemLp (dx : CuspCylinder → ℂ) 2 (functionMeasure a) :=
    (Lp.memLp dx).of_measure_le_smul (by simp) (functionMeasure_le_derivativeMeasure ha)
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  rw [physical_character_height_pairing a dx hd n hβ hc hpos, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(raw_weak_unit_all_integer_modes ha hweak).filter_mono
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le,
    zeroExtension_sliceCoefficients_on_tail a (tailValue a u) u (tailValue_ae a u),
    ae_restrict_mem (strictHeightTail_measurable a)] with y hx hu hy
  rw [hx hy n, show valueMode a n u y =
    AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n from hu n]
  rw [modeFrequency]
  ring

theorem vertical_native_character_pairing {a : ℝ} (ha : 0 < a) (n : ℤ) (dy : DerivativeL2 a)
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * AddCircle.fourier (-n) z.1 * dy z
      ∂derivativeMeasure a) =
      ∫ y, (β (y : ℝ) : ℂ) * verticalMode a ha n dy y ∂rawHeightTail a := by
  have hd : MemLp (dy : CuspCylinder → ℂ) 2 (functionMeasure a) :=
    (Lp.memLp dy).of_measure_le_smul (by simp) (functionMeasure_le_derivativeMeasure ha)
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  rw [physical_character_height_pairing a dy hd n hβ hc hpos]
  apply integral_congr_ae
  filter_upwards [zeroExtension_sliceCoefficients_on_tail a (tailDerivative a ha dy) dy
    (tailDerivative_ae a ha dy)] with y hy
  rw [show verticalMode a ha n dy y =
    AddCircle.fourierCoeff (fun x : UnitAddCircle => dy (x, y)) n from hy n]

/-- Every integer Fourier height mode satisfies the actual coupled weak
mode equation, derived by inserting a genuine Fourier tensor test. -/
theorem tensor_eigen_all_weak_modes {a λ : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {dx dy : DerivativeL2 a}
    (hdx : HasRawWeakPhysicalTailDerivative 1 a u dx)
    (hdy : HasRawWeakPhysicalVerticalDerivative a u dy)
    (heigen : HasPhysicalTensorEigenpair a λ u dx dy) :
    ∀ n : ℤ, HasWeakPhysicalModeEquation a λ n (valueMode a n u) (verticalMode a ha n dy) := by
  intro n
  refine ⟨vertical_weak_height_coefficients ha hdy n, ?_⟩
  intro β hβ hc hs
  have ht := heigen (AddCircle.fourier n) (modeFrequency n • AddCircle.fourier n)
    (character_smooth n) (character_derivative n) β hβ hc hs
  have hhor : (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) *
      star ((modeFrequency n • AddCircle.fourier n) z.1) * dx z ∂derivativeMeasure a) =
      (horizontalModeSquare n : ℂ) *
        (∫ y, (β (y : ℝ) : ℂ) * valueMode a n u y ∂rawHeightTail a) := by
    calc
      _ = star (modeFrequency n) * (∫ z : CuspCylinder,
          (β (z.2 : ℝ) : ℂ) * AddCircle.fourier (-n) z.1 * dx z ∂derivativeMeasure a) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul, map_mul, star_mul, star_character]
          ring
      _ = _ := by
        rw [horizontal_native_character_pairing ha hdx n hβ.continuous hc hs,
          ← mul_assoc, frequency_star_mul]
  have hvert : (∫ z : CuspCylinder, (deriv β (z.2 : ℝ) : ℂ) *
      star (AddCircle.fourier n z.1) * dy z ∂derivativeMeasure a) =
      ∫ y, (deriv β (y : ℝ) : ℂ) * verticalMode a ha n dy y ∂rawHeightTail a := by
    simp_rw [star_character]
    exact vertical_native_character_pairing ha n dy
      (contDiff_infty_iff_deriv.mp hβ).2.continuous hc.deriv (tsupport_deriv_subset.trans hs)
  have hvalue : (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) *
      star (AddCircle.fourier n z.1) * u z ∂functionMeasure a) =
      ∫ y, ((β (y : ℝ) * (1 / (y : ℝ))^2 : ℝ) : ℂ) * valueMode a n u y ∂rawHeightTail a := by
    simp_rw [star_character]
    exact weighted_character_native_height_pairing ha n u hβ.continuous hc hs
  rw [hhor, hvert, hvalue] at ht
  simpa only [add_comm] using ht

end
end ImbalancedChen.Part3.CuspTensorEigenWeakModes20261026b
