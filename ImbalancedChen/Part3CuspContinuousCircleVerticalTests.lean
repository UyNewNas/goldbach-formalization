import ImbalancedChen.Part3CuspVerticalWeakCutoffProduct
import ImbalancedChen.Part3CuspRawTestPairingContinuity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Genuine extension of vertical weak tensor tests from smooth circle tests
to ALL continuous circle tests. Full Fourier sums include mode zero and
converge in actual Haar L2. Both raw physical pairings are explicit
continuous linear functionals of that circle L2 class, using the true
height tensor maps; the weighted value pairing pays the factor y^2.
Neither smooth density nor continuity of test pairings is assumed.
-/
namespace ImbalancedChen.Part3.CuspContinuousCircleVerticalTests20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open CuspZeroMeanSmoothApproximationSourceOnly ClosedHorizontalCuspTail20261026a
open SeparatedWeakCuspGraphApproximation20261026a CuspCompactHeightTestDetection20261026b
open CuspRawTestPairingContinuity20261026b CuspRawWeakDerivativeBridge20261026b
open CuspReciprocalHeightTests20261026b CuspVerticalWeakCutoffProduct20261026b
attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

def circleClass (φ : C(UnitAddCircle, ℂ)) : CircleL2 :=
  ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ φ

def fullPolynomial (f : CircleL2) (s : Finset ℤ) : C(UnitAddCircle, ℂ) :=
  ∑ n ∈ s, AddCircle.fourierCoeff f n • AddCircle.fourier n

theorem fullPolynomial_smooth (f : CircleL2) (s : Finset ℤ) :
    ContDiff ℝ ∞ (fun t : ℝ => fullPolynomial f s (t : UnitAddCircle)) := by
  apply ContDiff.sum
  intro n hn
  have h : ContDiff ℝ ∞ (fun t : ℝ => AddCircle.fourier n (t : UnitAddCircle)) := by
    simp only [AddCircle.fourier_coe_apply, Complex.ofReal_one, div_one]
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  exact h.const_smul _

theorem fullPolynomial_toLp (f : CircleL2) (s : Finset ℤ) :
    circleClass (fullPolynomial f s) =
      ∑ n ∈ s, AddCircle.fourierCoeff f n • AddCircle.fourierLp 2 n := by
  simp only [circleClass, fullPolynomial, map_sum, map_smul, AddCircle.fourierLp]

/-- Actual circle smooth density INCLUDING the zero Fourier mode. -/
theorem fullPolynomial_toLp_tendsto (f : CircleL2) :
    Tendsto (fun N => circleClass (fullPolynomial f (window N))) atTop (𝓝 f) := by
  simpa only [fullPolynomial_toLp] using
    (AddCircle.hasSum_fourier_series_L2 f).comp (Finset.tendsto_Icc_neg (R := ℤ))

def testHeightProfile (a : ℝ) (β : ℝ → ℝ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) : HeightProfile a where
  function := fun y => (β (y : ℝ) : ℂ)
  continuous := Complex.continuous_ofReal.comp (hβ.comp continuous_subtype_val)
  weighted_memLp := (heightTest_memLp hβ hc hs).restrict (strictHeightTail a)
  raw_memLp := (raw_height_test_memLp hβ hc hs).restrict (strictHeightTail a)

def starVector {μ : Measure CuspCylinder} (v : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (Lp.memLp v).star.toLp (fun z => star (v z))

theorem inner_starVector {μ : Measure CuspCylinder} (v t : Lp ℂ 2 μ) :
    inner ℂ (starVector v) t = ∫ z, t z * v z ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(Lp.memLp v).star.coeFn_toLp] with z hz
  rw [hz]
  simp only [RCLike.inner_apply', star_star]
  ring

def rawDerivativeCircleFunctional (a : ℝ) (β : ℝ → ℝ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ))
    (d : DerivativeL2 a) : CircleL2 →L[ℂ] ℂ :=
  (innerSL ℂ (starVector d)).comp (liftDerivative (testHeightProfile a β hβ hc hs))

def rawValueCircleFunctional (a : ℝ) (β : ℝ → ℝ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ))
    (u : FunctionL2 a) : CircleL2 →L[ℂ] ℂ :=
  (innerSL ℂ (starVector u)).comp
    (liftValue (testHeightProfile a (squareHeightTest β)
      (hβ.mul (continuous_id.pow 2)) (squareHeightTest_compact hc)
      ((squareHeightTest_tsupport_subset β).trans hs)))

private theorem circleClass_raw_product_ae (a : ℝ) (φ : C(UnitAddCircle, ℂ)) :
    ∀ᵐ z ∂derivativeMeasure a, circleClass φ z.1 = φ z.1 := by
  rw [derivativeMeasure_product]
  exact (quasiMeasurePreserving_fst).ae
    (ContinuousMap.coeFn_toLp (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) φ)

private theorem circleClass_weighted_product_ae (a : ℝ) (φ : C(UnitAddCircle, ℂ)) :
    ∀ᵐ z ∂functionMeasure a, circleClass φ z.1 = φ z.1 := by
  rw [functionMeasure_product]
  exact (quasiMeasurePreserving_fst).ae
    (ContinuousMap.coeFn_toLp (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) φ)

/-- True raw pairing with the given derivative, continuous in circle L2. -/
theorem rawDerivativeCircleFunctional_pairing (a : ℝ) (β : ℝ → ℝ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ))
    (d : DerivativeL2 a) (φ : C(UnitAddCircle, ℂ)) :
    rawDerivativeCircleFunctional a β hβ hc hs d (circleClass φ) =
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * d z ∂derivativeMeasure a := by
  change inner ℂ (starVector d) (liftDerivative (testHeightProfile a β hβ hc hs) (circleClass φ)) = _
  rw [inner_starVector]
  apply integral_congr_ae
  filter_upwards [liftDerivative_ae (testHeightProfile a β hβ hc hs) (circleClass φ),
    circleClass_raw_product_ae a φ] with z hz hc
  rw [hz, hc]
  simp only [testHeightProfile]
  ring

/-- The RAW value pairing uses a true y^2 height tensor in weighted L2. -/
theorem rawValueCircleFunctional_pairing (a : ℝ) (β : ℝ → ℝ) (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ))
    (u : FunctionL2 a) (φ : C(UnitAddCircle, ℂ)) :
    rawValueCircleFunctional a β hβ hc hs u (circleClass φ) =
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * u z ∂derivativeMeasure a := by
  rw [raw_tensor_integral_eq_weighted]
  change inner ℂ (starVector u) (liftValue _ (circleClass φ)) = _
  rw [inner_starVector]
  apply integral_congr_ae
  filter_upwards [liftValue_ae (testHeightProfile a (squareHeightTest β)
      (hβ.mul (continuous_id.pow 2)) (squareHeightTest_compact hc)
      ((squareHeightTest_tsupport_subset β).trans hs)) (circleClass φ),
    circleClass_weighted_product_ae a φ] with z hz hc
  rw [hz, hc]
  simp only [testHeightProfile]
  ring

def HasSmoothCircleRawVerticalWeak (a : ℝ) (u : FunctionL2 a) (d : DerivativeL2 a) : Prop :=
  ∀ φ : C(UnitAddCircle, ℂ), ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)) →
    ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ Ioi a →
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * d z ∂derivativeMeasure a) =
        -(∫ z : CuspCylinder, (deriv β (z.2 : ℝ) : ℂ) * φ z.1 * u z ∂derivativeMeasure a)

/-- Genuine smooth-circle testing implies the FULL vertical convention
of 2358, with every continuous circle test admitted. -/
theorem smooth_circle_tests_imply_full_vertical_weak {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasSmoothCircleRawVerticalWeak a u d) :
    HasRawWeakPhysicalVerticalDerivative a u d := by
  intro φ β hβ hc hs
  have hpos : tsupport β ⊆ Ioi (0 : ℝ) := fun y hy => ha.trans (hs hy)
  let A := rawDerivativeCircleFunctional a β hβ.continuous hc hpos d
  let B := rawValueCircleFunctional a (deriv β) (contDiff_infty_iff_deriv.mp hβ).2.continuous
    hc.deriv (tsupport_deriv_subset.trans hpos) u
  have hS : IsClosed {f : CircleL2 | A f = -(B f)} :=
    isClosed_eq A.continuous B.continuous.neg
  have ht := fullPolynomial_toLp_tendsto (circleClass φ)
  have hlimit : A (circleClass φ) = -(B (circleClass φ)) :=
    hS.mem_of_tendsto ht (Eventually.of_forall fun N => by
      change rawDerivativeCircleFunctional a β hβ.continuous hc hpos d
        (circleClass (fullPolynomial (circleClass φ) (window N))) =
        -(rawValueCircleFunctional a (deriv β) (contDiff_infty_iff_deriv.mp hβ).2.continuous
          hc.deriv (tsupport_deriv_subset.trans hpos) u
          (circleClass (fullPolynomial (circleClass φ) (window N))))
      rw [rawDerivativeCircleFunctional_pairing, rawValueCircleFunctional_pairing]
      exact hweak _ (fullPolynomial_smooth _ _) β hβ hc hs)
  simpa only [A, B, rawDerivativeCircleFunctional_pairing, rawValueCircleFunctional_pairing] using hlimit

end
end ImbalancedChen.Part3.CuspContinuousCircleVerticalTests20261026b
