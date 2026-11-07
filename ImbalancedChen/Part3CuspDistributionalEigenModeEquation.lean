import ImbalancedChen.Part3CuspTensorEigenWeakModes

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL Fourier height coefficients of an arbitrary physical H1
weak eigenpair satisfy -f_n''+(2πn)^2 f_n=λ*y^-2*f_n in distributions on
(a,infty). The proof uses β' in the already derived first weak derivative
equation, not a classical second derivative assumption. Actual compact
test integrability is proved. A single raw-AE height set identifies ALL
integer native coefficients with the original physical value, dx and dy
slices, whose genuine L² regularity also holds on that same set.
No elliptic bootstrap, smooth eigenfunction or Gamma-modeling claim occurs.
-/
namespace ImbalancedChen.Part3.CuspDistributionalEigenModeEquation20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a CuspPhysicalWeakTailModes20261026b
open CuspRawWeakDerivativeBridge20261026b CuspRawPhysicalSliceModes20261026b
open CuspWeakCylinderFourierModes20261026b CuspVerticalWeakCutoffProduct20261026b
open CuspVerticalFourierWeakCoefficients20261026b CuspWeakModeHeightPairing20261026b
open CuspTensorEigenWeakModes20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Literal distributional second-order equation, tested against actual
real C-infinity compact functions strictly inside the positive tail. -/
def HasDistributionalEigenModeEquation (a λ : ℝ) (n : ℤ) (f : PositiveHeight → ℂ) : Prop :=
  ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioi a →
    -(∫ y, (deriv (deriv β) (y : ℝ) : ℂ) * f y ∂rawHeightTail a) +
      (horizontalModeSquare n : ℂ) * (∫ y, (β (y : ℝ) : ℂ) * f y ∂rawHeightTail a) =
      (λ : ℂ) * (∫ y, ((β (y : ℝ) * (1 / (y : ℝ))^2 : ℝ) : ℂ) * f y ∂rawHeightTail a)

theorem valueMode_second_test_integrable {a : ℝ} (ha : 0 < a) (n : ℤ) (u : FunctionL2 a)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi a) :
    Integrable (fun y : PositiveHeight => (deriv (deriv β) (y : ℝ) : ℂ) * valueMode a n u y)
      (rawHeightTail a) := by
  have h1 : ContDiff ℝ ∞ (deriv β) := (contDiff_infty_iff_deriv.mp hβ).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv β)) := (contDiff_infty_iff_deriv.mp h1).2
  exact valueMode_test_raw_integrable ha n u h2.continuous hc.deriv.deriv
    (tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hs))

/-- All integer equations, including zero, are DERIVED from genuine
physical weak derivatives and the original tensor eigenvariational law. -/
theorem physical_tensor_eigen_all_distributional_modes {a λ : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {dx dy : DerivativeL2 a}
    (hdx : HasRawWeakPhysicalTailDerivative 1 a u dx)
    (hdy : HasRawWeakPhysicalVerticalDerivative a u dy)
    (heigen : HasPhysicalTensorEigenpair a λ u dx dy) :
    ∀ n : ℤ, HasDistributionalEigenModeEquation a λ n (valueMode a n u) := by
  intro n β hβ hc hs
  have hmode := tensor_eigen_all_weak_modes ha hdx hdy heigen n
  have hfirst := hmode.1 (deriv β) (contDiff_infty_iff_deriv.mp hβ).2 hc.deriv
    (tsupport_deriv_subset.trans hs)
  have he := hmode.2 β hβ hc hs
  rw [hfirst] at he
  exact he

theorem distributionalEigenMode_congr_ae {a λ : ℝ} {n : ℤ}
    {f g : PositiveHeight → ℂ} (hfg : f =ᵐ[rawHeightTail a] g)
    (hf : HasDistributionalEigenModeEquation a λ n f) :
    HasDistributionalEigenModeEquation a λ n g := by
  intro β hβ hc hs
  have h1 : (∫ y, (deriv (deriv β) (y : ℝ) : ℂ) * g y ∂rawHeightTail a) =
      ∫ y, (deriv (deriv β) (y : ℝ) : ℂ) * f y ∂rawHeightTail a := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  have h2 : (∫ y, (β (y : ℝ) : ℂ) * g y ∂rawHeightTail a) =
      ∫ y, (β (y : ℝ) : ℂ) * f y ∂rawHeightTail a := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  have h3 : (∫ y, ((β (y : ℝ) * (1 / (y : ℝ))^2 : ℝ) : ℂ) * g y ∂rawHeightTail a) =
      ∫ y, ((β (y : ℝ) * (1 / (y : ℝ))^2 : ℝ) : ℂ) * f y ∂rawHeightTail a := by
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  rw [h1, h2, h3]
  exact hf β hβ hc hs

/-- In particular the ORIGINAL physical slice Fourier functions, not
only their native Lp representatives, satisfy the displayed weak ODE. -/
theorem physical_original_fourier_modes_distributional {a λ : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {dx dy : DerivativeL2 a}
    (hdx : HasRawWeakPhysicalTailDerivative 1 a u dx)
    (hdy : HasRawWeakPhysicalVerticalDerivative a u dy)
    (heigen : HasPhysicalTensorEigenpair a λ u dx dy) :
    ∀ n : ℤ, HasDistributionalEigenModeEquation a λ n
      (fun y => AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n) := by
  intro n
  apply distributionalEigenMode_congr_ae _ (physical_tensor_eigen_all_distributional_modes ha hdx hdy heigen n)
  filter_upwards [zeroExtension_sliceCoefficients_on_tail a (tailValue a u) u (tailValue_ae a u)]
    with y hy
  exact hy n

/-- ONE actual raw-height conull set works simultaneously for every
integer and for the original physical value/dx/dy representatives.
Genuine L² circle slices are proved, not postulated. -/
theorem physical_eigen_coefficients_common_ae {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {dx dy : DerivativeL2 a}
    (hdx : HasRawWeakPhysicalTailDerivative 1 a u dx) :
    ∀ᵐ y ∂rawHeightTail a,
      MemLp (fun x : UnitAddCircle => u (x, y)) 2 AddCircle.haarAddCircle ∧
      MemLp (fun x : UnitAddCircle => dx (x, y)) 2 AddCircle.haarAddCircle ∧
      MemLp (fun x : UnitAddCircle => dy (x, y)) 2 AddCircle.haarAddCircle ∧
      ∀ n : ℤ,
        valueMode a n u y = AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n ∧
        verticalMode a ha n dy y = AddCircle.fourierCoeff (fun x : UnitAddCircle => dy (x, y)) n ∧
        AddCircle.fourierCoeff (fun x : UnitAddCircle => dx (x, y)) n =
          modeFrequency n * valueMode a n u y := by
  have hx := (raw_weak_all_integer_physical_modes ha hdx).filter_mono
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le
  have hdySlices := (physical_derivative_slices_memLp a dy).filter_mono
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le
  have hU := zeroExtension_sliceCoefficients_on_tail a (tailValue a u) u (tailValue_ae a u)
  have hY := zeroExtension_sliceCoefficients_on_tail a (tailDerivative a ha dy) dy
    (tailDerivative_ae a ha dy)
  filter_upwards [hx, hdySlices, hU, hY,
    ae_restrict_mem (strictHeightTail_measurable a)] with y hx hy hu hY hytail
  refine ⟨(hx hytail).1, (hx hytail).2.1, hy hytail, ?_⟩
  intro n
  refine ⟨hu n, hY n, ?_⟩
  have h := (hx hytail).2.2 n
  simpa only [Complex.ofReal_one, one_mul, valueMode, hu n] using h

/-- Exact generic physical weak eigenmode primitive, with both the
distributional equation and a common original-coefficient AE interface. -/
theorem physical_tensor_eigen_mode_data {a λ : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {dx dy : DerivativeL2 a}
    (hdx : HasRawWeakPhysicalTailDerivative 1 a u dx)
    (hdy : HasRawWeakPhysicalVerticalDerivative a u dy)
    (heigen : HasPhysicalTensorEigenpair a λ u dx dy) :
    (∀ n : ℤ, HasDistributionalEigenModeEquation a λ n (valueMode a n u)) ∧
    (∀ᵐ y ∂rawHeightTail a, ∀ n : ℤ,
      valueMode a n u y = AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n ∧
      verticalMode a ha n dy y = AddCircle.fourierCoeff (fun x : UnitAddCircle => dy (x, y)) n) := by
  refine ⟨physical_tensor_eigen_all_distributional_modes ha hdx hdy heigen, ?_⟩
  filter_upwards [physical_eigen_coefficients_common_ae ha hdx] with y hy
  intro n
  exact ⟨(hy.2.2.2 n).1, (hy.2.2.2 n).2.1⟩

end
end ImbalancedChen.Part3.CuspDistributionalEigenModeEquation20261026b
