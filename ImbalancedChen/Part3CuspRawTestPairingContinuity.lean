import ImbalancedChen.Part3CuspRawPhysicalSliceModes

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual compact raw tensor-test pairings are continuous on the two
different physical L² spaces. The value pairing uses β*y² in weighted
L²; the derivative pairing uses a genuine raw L² test. Both are proved
to equal native Hilbert inner products against explicit conjugate tests.
No convergence of distributions, pairings or derivatives is assumed.
-/
namespace ImbalancedChen.Part3.CuspRawTestPairingContinuity20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a CuspCompactHeightTestDetection20261026b
open CuspGeneralWeakGraphClosure20261026b CuspReciprocalHeightTests20261026b
open CuspRawWeakDerivativeBridge20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

def conjugateCircleTest (φ : C(UnitAddCircle, ℂ)) : C(UnitAddCircle, ℂ) :=
  ⟨fun x => star (φ x), φ.continuous.star⟩

theorem raw_height_test_memLp {β : ℝ → ℝ} (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    MemLp (fun y : PositiveHeight => (β (y : ℝ) : ℂ)) 2 (volume : Measure PositiveHeight) := by
  obtain ⟨B, hB⟩ := hc.bddAbove
  have hC : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  apply supported_height_raw_memLp hC (heightTest_memLp hβ hc hs)
  intro y hy
  have hyβ : β (y : ℝ) ≠ 0 := by simpa only [mem_support, Complex.ofReal_eq_zero] using hy
  exact (hB (subset_closure hyβ)).trans (le_max_left B 1)

theorem raw_tensor_test_memLp (φ : C(UnitAddCircle, ℂ)) {β : ℝ → ℝ}
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    MemLp (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * φ z.1) 2 rawCylinderMeasure := by
  have hb := (raw_height_test_memLp hβ hc hs).comp_snd
    (AddCircle.haarAddCircle (T := (1 : ℝ)))
  apply hb.of_le_mul (c := ‖φ‖)
  · exact ((Complex.continuous_ofReal.comp
      (hβ.comp (continuous_subtype_val.comp continuous_snd))).mul
        (φ.continuous.comp continuous_fst)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm z.1)
        (norm_nonneg _)).trans_eq (mul_comm _ _)

def derivativeTestVector (a : ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    DerivativeL2 a :=
  ((raw_tensor_test_memLp (conjugateCircleTest φ) hβ hc hs).restrict
    (strictCylinderTail a)).toLp
      (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * star (φ z.1))

def valueTestVector (a : ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    FunctionL2 a :=
  ((tensor_test_memLp (conjugateCircleTest φ) (hβ.mul (continuous_id.pow 2))
    (squareHeightTest_compact hc) ((squareHeightTest_tsupport_subset β).trans hs)).restrict
      (strictCylinderTail a)).toLp
        (fun z : CuspCylinder => (squareHeightTest β (z.2 : ℝ) : ℂ) * star (φ z.1))

theorem derivativeTestVector_pairing (a : ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ))
    (d : DerivativeL2 a) :
    inner ℂ (derivativeTestVector a φ β hβ hc hs) d =
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * d z ∂derivativeMeasure a := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((raw_tensor_test_memLp (conjugateCircleTest φ) hβ hc hs).restrict
    (strictCylinderTail a)).coeFn_toLp] with z hz
  change inner ℂ (derivativeTestVector a φ β hβ hc hs z) (d z) = _
  rw [hz]
  simp [RCLike.inner_apply', Complex.star_def]

theorem valueTestVector_pairing (a : ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ))
    (u : FunctionL2 a) :
    inner ℂ (valueTestVector a φ β hβ hc hs) u =
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * u z ∂derivativeMeasure a := by
  rw [raw_tensor_integral_eq_weighted a β φ u, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((tensor_test_memLp (conjugateCircleTest φ)
    (hβ.mul (continuous_id.pow 2)) (squareHeightTest_compact hc)
    ((squareHeightTest_tsupport_subset β).trans hs)).restrict (strictCylinderTail a)).coeFn_toLp]
      with z hz
  change inner ℂ (valueTestVector a φ β hβ hc hs z) (u z) = _
  rw [hz]
  simp [RCLike.inner_apply', Complex.star_def]

/-- Continuity in raw derivative L² of the actual raw tensor pairing. -/
theorem continuous_raw_derivative_pairing (a : ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    Continuous (fun d : DerivativeL2 a =>
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * d z ∂derivativeMeasure a) := by
  have he : (fun d : DerivativeL2 a =>
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * d z ∂derivativeMeasure a) =
      (fun d => inner ℂ (derivativeTestVector a φ β hβ hc hs) d) :=
    funext fun d => (derivativeTestVector_pairing a φ β hβ hc hs d).symm
  rw [he]
  exact continuous_const.inner continuous_id

/-- Continuity in weighted value L² of the actual RAW tensor pairing. -/
theorem continuous_raw_value_pairing (a : ℝ) (φ : C(UnitAddCircle, ℂ)) (β : ℝ → ℝ)
    (hβ : Continuous β) (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    Continuous (fun u : FunctionL2 a =>
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * u z ∂derivativeMeasure a) := by
  have he : (fun u : FunctionL2 a =>
      ∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * u z ∂derivativeMeasure a) =
      (fun u => inner ℂ (valueTestVector a φ β hβ hc hs) u) :=
    funext fun u => (valueTestVector_pairing a φ β hβ hc hs u).symm
  rw [he]
  exact continuous_const.inner continuous_id

end
end ImbalancedChen.Part3.CuspRawTestPairingContinuity20261026b
