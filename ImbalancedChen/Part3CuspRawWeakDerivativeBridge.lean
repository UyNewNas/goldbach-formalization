import ImbalancedChen.Part3CuspReciprocalHeightTests

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The raw dx dy distributional horizontal weak equation is converted to
the native dy/y² convention by ACTUAL smooth compact reciprocal-height
tests. All tensor pairings are genuinely integrable from the mixed L²
regularity, including the value which need not lie in global raw L².
Actual Bochner Fubini is then available on the raw product measure.
The equivalence of conventions and raw/weighted height AE identity feed
the full width-dependent weak graph and sharp tail theorem.

No chart derivative, Fourier relation, graph approximation, or form-domain
identification is assumed. Identifying an arbitrary Gamma quotient weak
form with these literal physical cusp inputs remains a separate task.
-/
namespace ImbalancedChen.Part3.CuspRawWeakDerivativeBridge20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open CuspCompactHeightTestDetection20261026b CuspPhysicalWeakTailModes20261026b
open CuspWidthWeakGraphTail20261026b CuspReciprocalHeightTests20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

/-- A bounded continuous circle factor times an actual compact height
test is in native cylinder L². Its norm bound uses the actual circle norm. -/
theorem tensor_test_memLp (φ : C(UnitAddCircle, ℂ)) {β : ℝ → ℝ}
    (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    MemLp (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * φ z.1) 2 cylinderMeasure := by
  have hb := (heightTest_memLp hβ hc hs).comp_snd
    (AddCircle.haarAddCircle (T := (1 : ℝ)))
  apply hb.of_le_mul (c := ‖φ‖)
  · exact ((Complex.continuous_ofReal.comp
      (hβ.comp (continuous_subtype_val.comp continuous_snd))).mul
        (φ.continuous.comp continuous_fst)).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (φ.norm_coe_le_norm z.1)
        (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem weighted_tensor_integrable (a : ℝ) (H : CuspCylinder → ℂ)
    (hH : MemLp H 2 (functionMeasure a)) (φ : C(UnitAddCircle, ℂ))
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    Integrable (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * φ z.1 * H z)
      (functionMeasure a) := by
  simpa only [Pi.mul_apply] using
    ((tensor_test_memLp φ hβ hc hs).restrict (strictCylinderTail a)).integrable_mul hH

/-- Local raw integrability follows from weighted L² by testing with
β*y² and then applying the literal density identity. No global raw L²
regularity of H is required. -/
theorem raw_tensor_integrable (a : ℝ) (H : CuspCylinder → ℂ)
    (hH : MemLp H 2 (functionMeasure a)) (φ : C(UnitAddCircle, ℂ))
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    Integrable (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * φ z.1 * H z)
      (derivativeMeasure a) := by
  have hγ : Continuous (squareHeightTest β) := hβ.mul (continuous_id.pow 2)
  have hγc := squareHeightTest_compact hc
  have hγs := (squareHeightTest_tsupport_subset β).trans hs
  have hw := weighted_tensor_integrable a H hH φ hγ hγc hγs
  rw [functionMeasure_eq_raw_withDensity] at hw
  have hd := (integrable_withDensity_iff_integrable_smul
    (heightDensity_continuous.measurable.comp measurable_snd)).mp hw
  apply hd.congr
  exact Eventually.of_forall fun z => by
    calc
      heightDensity z.2 • ((squareHeightTest β (z.2 : ℝ) : ℂ) * φ z.1 * H z) =
          (((heightDensity z.2 : ℝ) * squareHeightTest β (z.2 : ℝ) : ℝ) : ℂ) *
            φ z.1 * H z := by
        simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]
        ring
      _ = _ := by rw [density_times_squareHeightTest]

/-- Actual raw-product Bochner Fubini, justified by the integrability
proved from the genuine weighted L² input immediately above. -/
theorem raw_tensor_fubini (a : ℝ) (H : CuspCylinder → ℂ)
    (hH : MemLp H 2 (functionMeasure a)) (φ : C(UnitAddCircle, ℂ))
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * H z ∂derivativeMeasure a) =
      ∫ y : PositiveHeight, ∫ x : UnitAddCircle,
        (β (y : ℝ) : ℂ) * φ x * H (x, y) ∂AddCircle.haarAddCircle
          ∂(volume : Measure PositiveHeight).restrict (strictHeightTail a) := by
  have hi := raw_tensor_integrable a H hH φ hβ hc hs
  rw [derivativeMeasure_product] at hi ⊢
  exact integral_prod_symm _ hi

/-- Genuine raw dx dy distributional testing, with width w in the unit
circle coordinate. Both test derivatives and the test support are actual. -/
def HasRawWeakPhysicalTailDerivative (w a : ℝ) (u : FunctionL2 a) (d : DerivativeL2 a) : Prop :=
  ∀ φ ψ : C(UnitAddCircle, ℂ),
    ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)) →
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) →
    ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β →
      tsupport β ⊆ Ioi (0 : ℝ) →
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * d z)
        ∂derivativeMeasure a) =
      -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * u z ∂derivativeMeasure a)

/-- The regularity of physical mixed L² vectors proves BOTH raw tensor
integrabilities; the distributional definition is not exploiting the
zero value assigned by Bochner integration to a nonintegrable function. -/
theorem physical_raw_test_integrabilities {w a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) (φ ψ : C(UnitAddCircle, ℂ))
    {β : ℝ → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    Integrable (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * d z))
        (derivativeMeasure a) ∧
      Integrable (fun z : CuspCylinder => (β (z.2 : ℝ) : ℂ) * ψ z.1 * u z)
        (derivativeMeasure a) := by
  have hd : MemLp (fun z : CuspCylinder => (w : ℂ) * d z) 2 (functionMeasure a) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      ((Lp.memLp d).of_measure_le_smul (by simp)
        (functionMeasure_le_derivativeMeasure ha)).const_smul (w : ℂ)
  exact ⟨raw_tensor_integrable a _ hd φ hβ hc hs,
    raw_tensor_integrable a u (Lp.memLp u) ψ hβ hc hs⟩

theorem raw_weak_implies_weighted {w a : ℝ} {u : FunctionL2 a} {d : DerivativeL2 a}
    (hraw : HasRawWeakPhysicalTailDerivative w a u d) :
    HasWeakPhysicalTailDerivative w a u d := by
  intro φ ψ hφ hd β hβ hc hs
  rw [weighted_tensor_integral_eq_raw a β φ,
    weighted_tensor_integral_eq_raw a β ψ]
  exact hraw φ ψ hφ hd (reciprocalSquareTest β)
    (reciprocalSquareTest_smooth hβ hs) (reciprocalSquareTest_compact hc)
    ((reciprocalSquareTest_tsupport_subset β).trans hs)

theorem weighted_weak_implies_raw {w a : ℝ} {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweighted : HasWeakPhysicalTailDerivative w a u d) :
    HasRawWeakPhysicalTailDerivative w a u d := by
  intro φ ψ hφ hd β hβ hc hs
  rw [raw_tensor_integral_eq_weighted a β φ,
    raw_tensor_integral_eq_weighted a β ψ]
  exact hweighted φ ψ hφ hd (squareHeightTest β)
    (squareHeightTest_smooth hβ) (squareHeightTest_compact hc)
    ((squareHeightTest_tsupport_subset β).trans hs)

/-- Exact equality of the two genuine distributional conventions. -/
theorem raw_weak_iff_weighted {w a : ℝ} {u : FunctionL2 a} {d : DerivativeL2 a} :
    HasRawWeakPhysicalTailDerivative w a u d ↔ HasWeakPhysicalTailDerivative w a u d :=
  ⟨raw_weak_implies_weighted, weighted_weak_implies_raw⟩

/-- Actual raw-distributional weak data and raw-AE horizontal zero mean
give the full physical graph, with the literal width retained. -/
theorem raw_weak_physical_pair_mem_closed_graph {w a : ℝ} (hw : 0 < w) (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hraw : HasRawWeakPhysicalTailDerivative w a u d)
    (hmean : ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    (u, d) ∈ closedHorizontalGraph w a :=
  width_weak_physical_pair_mem_closed_graph hw ha (raw_weak_implies_weighted hraw)
    (heightMeasure_ae_iff_volume.mpr hmean)

theorem raw_weak_physical_pair_sharp_tail {w a Y : ℝ}
    (hw : 0 < w) (ha : 0 < a) (hY : 0 < Y) (haY : a ≤ Y)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hraw : HasRawWeakPhysicalTailDerivative w a u d)
    (hmean : ∀ᵐ y ∂(volume : Measure PositiveHeight), a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    ‖tailRestriction a Y haY u‖^2 ≤ (w^2 / (4 * Real.pi^2 * Y^2)) * ‖d‖^2 :=
  closed_horizontal_tail_bound hw hY haY (raw_weak_physical_pair_mem_closed_graph hw ha hraw hmean)

end
end ImbalancedChen.Part3.CuspRawWeakDerivativeBridge20261026b
