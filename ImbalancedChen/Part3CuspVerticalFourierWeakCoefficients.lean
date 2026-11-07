import ImbalancedChen.Part3CuspVerticalWeakCutoffProduct

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual vertical weak differentiation of height Fourier coefficients.
Raw cylinder Fubini is justified from the mixed physical L2 conditions.
Native weighted zero-extension coefficients agree with the physical
slices on one common raw-height AE set, simultaneously for every mode.
Testing the genuine vertical equation against a Fourier character gives
F_n'=G_n in the ordinary raw-height distribution convention on (a,infty).
No vertical coefficient equation or height-H1 approximation is assumed.
-/
namespace ImbalancedChen.Part3.CuspVerticalFourierWeakCoefficients20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open ActualCylinderModeEmbeddings20261026a ActualCylinderFourierCoefficients20261026a
open CuspPhysicalWeakTailModes20261026b CuspRawWeakDerivativeBridge20261026b
open CuspVerticalWeakCutoffProduct20261026b
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

def rawHeightTail (a : ℝ) : Measure PositiveHeight :=
  (volume : Measure PositiveHeight).restrict (strictHeightTail a)

def HasWeakHeightDerivativeOnTail (a : ℝ) (f g : PositiveHeight → ℂ) : Prop :=
  ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioi a →
    (∫ y, (β (y : ℝ) : ℂ) * g y ∂rawHeightTail a) =
      -(∫ y, (deriv β (y : ℝ) : ℂ) * f y ∂rawHeightTail a)

/-- Native zero-extension representatives give the physical Fourier
slice at every frequency on a SINGLE AE height set, in the raw measure. -/
theorem zeroExtension_sliceCoefficients_on_tail (a : ℝ) (H : CylinderL2)
    (f : CuspCylinder → ℂ)
    (hH : (H : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] (strictCylinderTail a).indicator f) :
    ∀ᵐ y ∂rawHeightTail a, ∀ n : ℤ,
      sliceCoefficient n H y = AddCircle.fourierCoeff (fun x : UnitAddCircle => f (x, y)) n := by
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂heightMeasure.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
      H (p.2, p.1) = (strictCylinderTail a).indicator f (p.2, p.1) :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hH
  have hslice : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) → ∀ n : ℤ,
      sliceCoefficient n H y = AddCircle.fourierCoeff (fun x : UnitAddCircle => f (x, y)) n := by
    filter_upwards [ae_ae_of_ae_prod hswap] with y hy
    intro hay n
    apply congrFun (AddCircle.fourierCoeff_congr_ae _) n
    filter_upwards [hy] with x hx
    simpa [strictCylinderTail, strictHeightTail, hay] using hx
  have hr := heightMeasure_ae_iff_volume.mp hslice
  filter_upwards [hr.filter_mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le,
    ae_restrict_mem (strictHeightTail_measurable a)] with y hy hyt
  exact hy hyt

theorem physical_character_height_pairing (a : ℝ) (H : CuspCylinder → ℂ)
    (hH : MemLp H 2 (functionMeasure a)) (n : ℤ) {β : ℝ → ℝ}
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * AddCircle.fourier (-n) z.1 * H z
      ∂derivativeMeasure a) =
      ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) *
        AddCircle.fourierCoeff (fun x : UnitAddCircle => H (x, y)) n ∂rawHeightTail a := by
  rw [raw_tensor_fubini a H hH (AddCircle.fourier (-n)) hβ hc hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    rw [integral_const_mul]
    rfl

theorem physical_character_height_pairing_integrable (a : ℝ) (H : CuspCylinder → ℂ)
    (hH : MemLp H 2 (functionMeasure a)) (n : ℤ) {β : ℝ → ℝ}
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    Integrable (fun y : PositiveHeight => (β (y : ℝ) : ℂ) *
      AddCircle.fourierCoeff (fun x : UnitAddCircle => H (x, y)) n) (rawHeightTail a) := by
  have hi := raw_tensor_integrable a H hH (AddCircle.fourier (-n)) hβ hc hs
  rw [derivativeMeasure_product] at hi
  have hp := hi.integral_prod_right
  convert hp using 1
  funext y
  rw [integral_const_mul]
  rfl

/-- The vertical derivative of every native Fourier height coefficient
is the coefficient of the ACTUAL given physical vertical weak derivative. -/
theorem vertical_weak_height_coefficients {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasRawWeakPhysicalVerticalDerivative a u d) (n : ℤ) :
    HasWeakHeightDerivativeOnTail a (sliceCoefficient n (tailValue a u))
      (sliceCoefficient n (tailDerivative a ha d)) := by
  intro β hβ hc hs
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  have hd : MemLp (d : CuspCylinder → ℂ) 2 (functionMeasure a) :=
    (Lp.memLp d).of_measure_le_smul (by simp) (functionMeasure_le_derivativeMeasure ha)
  have ht := hweak (AddCircle.fourier (-n)) β hβ hc hs
  rw [physical_character_height_pairing a d hd n hβ.continuous hc hpos,
    physical_character_height_pairing a u (Lp.memLp u) n
      (contDiff_infty_iff_deriv.mp hβ).2.continuous hc.deriv
      (tsupport_deriv_subset.trans hpos)] at ht
  have hu := zeroExtension_sliceCoefficients_on_tail a (tailValue a u) u (tailValue_ae a u)
  have hg := zeroExtension_sliceCoefficients_on_tail a (tailDerivative a ha d) d
    (tailDerivative_ae a ha d)
  calc
    _ = ∫ y : PositiveHeight, (β (y : ℝ) : ℂ) *
        AddCircle.fourierCoeff (fun x : UnitAddCircle => d (x, y)) n ∂rawHeightTail a := by
      apply integral_congr_ae
      filter_upwards [hg] with y hy
      rw [hy n]
    _ = -(∫ y : PositiveHeight, (deriv β (y : ℝ) : ℂ) *
        AddCircle.fourierCoeff (fun x : UnitAddCircle => u (x, y)) n ∂rawHeightTail a) := ht
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hu] with y hy
      rw [hy n]

end
end ImbalancedChen.Part3.CuspVerticalFourierWeakCoefficients20261026b
