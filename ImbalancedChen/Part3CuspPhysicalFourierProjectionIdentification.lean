import ImbalancedChen.Part3CuspHeightCutoffFourierModes
import ImbalancedChen.Part3FiniteHeightModeGraphClosure

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual physical representatives of a finite Fourier graph reconstruction.
The value and derivative are identified in their different L² quotient
spaces with literal character sums. For a height-localized weak cylinder
pair the derivative sum is the ACTUAL finite Fourier projection of the
given derivative, not a newly chosen independent polynomial.

Raw L² membership of each localized value coefficient is an explicit
primitive input here. On a compact height band this follows from the
independently owned upper-band measure comparison. No derivative
coefficient equation or graph membership is an input.
-/
namespace ImbalancedChen.Part3.CuspPhysicalFourierProjectionIdentification20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open ActualCylinderFiniteFourierProjection20261026b
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open ClosedHorizontalCuspTail20261026a SeparatedWeakCuspGraphApproximation20261026a
open FiniteHeightModeGraphClosure20261026b
open CuspWeakCylinderFourierModes20261026b CuspHeightCutoffFourierModes20261026b
open CuspPhysicalHeightExhaustion20261026b CuspPhysicalWeakTailModes20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

section Tensor
variable (μ : Measure PositiveHeight) [SFinite μ] (μC : Measure CuspCylinder)
variable (hμ : μC = (AddCircle.haarAddCircle (T := (1 : ℝ))).prod μ)

private theorem tensor_character_ae (c : ℂ) (k : ℤ) (f : PositiveHeight → ℂ)
    (hf : MemLp f 2 μ) :
    (tensorVector μ μC hμ (c • AddCircle.fourierLp 2 k) (hf.toLp f) : CuspCylinder → ℂ)
      =ᵐ[μC] (fun z => c * AddCircle.fourier k z.1 * f z.2) := by
  have hcircle : ∀ᵐ z : CuspCylinder ∂μC,
      (c • AddCircle.fourierLp 2 k : Lp ℂ 2 AddCircle.haarAddCircle) z.1 =
        c * AddCircle.fourier k z.1 := by
    rw [hμ]
    apply (quasiMeasurePreserving_fst).ae
    filter_upwards [Lp.coeFn_smul c (AddCircle.fourierLp 2 k),
      AddCircle.coeFn_fourierLp 2 k] with x hs hx
    simp only [hs, Pi.smul_apply, smul_eq_mul, hx]
  have hheight : ∀ᵐ z : CuspCylinder ∂μC, hf.toLp f z.2 = f z.2 := by
    rw [hμ]
    exact (quasiMeasurePreserving_snd).ae hf.coeFn_toLp
  filter_upwards [tensorVector_ae μ μC hμ (c • AddCircle.fourierLp 2 k)
    (hf.toLp f), hcircle, hheight] with z hz hc hh
  simpa only [tensorFunction, hc, hh] using hz

end Tensor

theorem coefficientPair_value_ae (a : ℝ) (k : ℤ) (f : PositiveHeight → ℂ)
    (hw : MemLp f 2 heightMeasure) (hr : MemLp f 2 (volume : Measure PositiveHeight)) :
    ((coefficientPair a k f hw hr).1 : CuspCylinder → ℂ) =ᵐ[functionMeasure a]
      (fun z => AddCircle.fourier k z.1 * f z.2) := by
  simpa only [coefficientPair, one_smul, one_mul] using
    tensor_character_ae (functionHeightMeasure a) (functionMeasure a)
      (functionMeasure_product a) 1 k f (hw.mono_measure Measure.restrict_le_self)

theorem coefficientPair_derivative_ae (a : ℝ) (k : ℤ) (f : PositiveHeight → ℂ)
    (hw : MemLp f 2 heightMeasure) (hr : MemLp f 2 (volume : Measure PositiveHeight)) :
    ((coefficientPair a k f hw hr).2 : CuspCylinder → ℂ) =ᵐ[derivativeMeasure a]
      (fun z => frequency k * AddCircle.fourier k z.1 * f z.2) :=
  tensor_character_ae (derivativeHeightMeasure a) (derivativeMeasure a)
    (derivativeMeasure_product a) (frequency k) k f
    (hr.mono_measure Measure.restrict_le_self)

def indexedCoefficientPair (a : ℝ) (s : Finset NonzeroMode)
    (f : ℤ → PositiveHeight → ℂ) (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight)) :
    FunctionL2 a × DerivativeL2 a :=
  ∑ k ∈ s, coefficientPair a k (f k) (hw k) (hr k)

theorem indexedCoefficientPair_value_ae (a : ℝ) (s : Finset NonzeroMode)
    (f : ℤ → PositiveHeight → ℂ) (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight)) :
    ((indexedCoefficientPair a s f hw hr).1 : CuspCylinder → ℂ) =ᵐ[functionMeasure a]
      (fun z => ∑ k ∈ s, AddCircle.fourier (k : ℤ) z.1 * f k z.2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [indexedCoefficientPair] using Lp.coeFn_zero ℂ 2 (functionMeasure a)
  | @insert k s hk ih =>
      simp only [indexedCoefficientPair, Finset.sum_insert hk] at ih ⊢
      filter_upwards [Lp.coeFn_add (coefficientPair a k (f k) (hw k) (hr k)).1
        ((∑ j ∈ s, coefficientPair a j (f j) (hw j) (hr j)).1),
        coefficientPair_value_ae a k (f k) (hw k) (hr k), ih] with z hz hk hs
      simpa only [Pi.add_apply, hk, hs] using hz

theorem indexedCoefficientPair_derivative_ae (a : ℝ) (s : Finset NonzeroMode)
    (f : ℤ → PositiveHeight → ℂ) (hw : ∀ k, MemLp (f k) 2 heightMeasure)
    (hr : ∀ k, MemLp (f k) 2 (volume : Measure PositiveHeight)) :
    ((indexedCoefficientPair a s f hw hr).2 : CuspCylinder → ℂ) =ᵐ[derivativeMeasure a]
      (fun z => ∑ k ∈ s, frequency k * AddCircle.fourier (k : ℤ) z.1 * f k z.2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [indexedCoefficientPair] using Lp.coeFn_zero ℂ 2 (derivativeMeasure a)
  | @insert k s hk ih =>
      simp only [indexedCoefficientPair, Finset.sum_insert hk] at ih ⊢
      filter_upwards [Lp.coeFn_add (coefficientPair a k (f k) (hw k) (hr k)).2
        ((∑ j ∈ s, coefficientPair a j (f j) (hw j) (hr j)).2),
        coefficientPair_derivative_ae a k (f k) (hw k) (hr k), ih] with z hz hk hs
      simpa only [Pi.add_apply, hk, hs] using hz

def localizedProfile (K : Set PositiveHeight) (F : CylinderL2) (k : ℤ) :
    PositiveHeight → ℂ := K.indicator (sliceCoefficient k F)

theorem localizedProfile_memLp (K : Set PositiveHeight) (hK : MeasurableSet K)
    (F : CylinderL2) (k : ℤ) : MemLp (localizedProfile K F k) 2 heightMeasure :=
  (sliceCoefficient_memLp k F).indicator hK

private theorem rawCylinder_absolutelyContinuous : rawCylinderMeasure ≪ cylinderMeasure := by
  have hheight : (volume : Measure PositiveHeight) ≪ heightMeasure :=
    withDensity_absolutelyContinuous'
      heightDensity_continuous.measurable.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun y => ENNReal.coe_ne_zero.mpr (heightDensity_pos y).ne')
  exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl hheight

/-- Exact identification with the ACTUAL projection of the given weak
derivative, including the physical raw measure on the conclusion. -/
theorem localized_projection_derivative_ae (a : ℝ) (s : Finset NonzeroMode)
    (K : Set PositiveHeight) (hK : MeasurableSet K) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G)
    (hr : ∀ k, MemLp (localizedProfile K F k) 2 (volume : Measure PositiveHeight)) :
    ((indexedCoefficientPair a s (localizedProfile K F)
      (localizedProfile_memLp K hK F) hr).2 : CuspCylinder → ℂ)
      =ᵐ[derivativeMeasure a]
        (finiteFourierProjection s (heightLocalizedCylinder K hK G) : CuspCylinder → ℂ) := by
  have hp := rawCylinder_absolutelyContinuous.ae_eq
    (finiteFourierProjection_ae s (heightLocalizedCylinder K hK G))
  have hp' := (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq hp
  have hmode : ∀ᵐ y ∂heightMeasure, ∀ k : ℤ,
      sliceCoefficient k (heightLocalizedCylinder K hK G) y =
        frequency k * localizedProfile K F k y := by
    filter_upwards [heightLocalizedCylinder_all_coefficients_ae K hK G,
      weak_cylinder_all_modes_ae hweak] with y hG heq
    intro k
    rw [hG k]
    by_cases hy : y ∈ K <;> simp [localizedProfile, hy, heq k, frequency, modeFrequency]
  have hmodeRaw := heightMeasure_ae_iff_volume.mp hmode
  have hz : ∀ᵐ z ∂derivativeMeasure a, ∀ k : ℤ,
      sliceCoefficient k (heightLocalizedCylinder K hK G) z.2 =
        frequency k * localizedProfile K F k z.2 := by
    have hprod := (quasiMeasurePreserving_snd
      (μ := AddCircle.haarAddCircle) (ν := (volume : Measure PositiveHeight))).ae hmodeRaw
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq hprod
  filter_upwards [indexedCoefficientPair_derivative_ae a s (localizedProfile K F)
    (localizedProfile_memLp K hK F) hr, hp', hz] with z hpair hproj hcoeff
  rw [hpair, hproj]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hcoeff k]
  ring

/-- Thus the actual projected derivative is genuinely in raw physical L²;
this is deduced from the identified finite coefficient reconstruction. -/
theorem localized_projection_derivative_memLp (a : ℝ) (s : Finset NonzeroMode)
    (K : Set PositiveHeight) (hK : MeasurableSet K) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G)
    (hr : ∀ k, MemLp (localizedProfile K F k) 2 (volume : Measure PositiveHeight)) :
    MemLp (finiteFourierProjection s (heightLocalizedCylinder K hK G) : CuspCylinder → ℂ)
      2 (derivativeMeasure a) :=
  (Lp.memLp (indexedCoefficientPair a s (localizedProfile K F)
    (localizedProfile_memLp K hK F) hr).2).congr
    (localized_projection_derivative_ae a s K hK hweak hr)

theorem localized_projection_value_ae (a : ℝ) (s : Finset NonzeroMode)
    (K : Set PositiveHeight) (hK : MeasurableSet K) (F : CylinderL2)
    (hr : ∀ k, MemLp (localizedProfile K F k) 2 (volume : Measure PositiveHeight)) :
    ((indexedCoefficientPair a s (localizedProfile K F)
      (localizedProfile_memLp K hK F) hr).1 : CuspCylinder → ℂ)
      =ᵐ[functionMeasure a]
        (finiteFourierProjection s (heightLocalizedCylinder K hK F) : CuspCylinder → ℂ) := by
  have hp := (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq
    (finiteFourierProjection_ae s (heightLocalizedCylinder K hK F))
  have hz : ∀ᵐ z ∂functionMeasure a, ∀ k : ℤ,
      sliceCoefficient k (heightLocalizedCylinder K hK F) z.2 =
        localizedProfile K F k z.2 := by
    have hh := (quasiMeasurePreserving_snd (μ := AddCircle.haarAddCircle)
      (ν := heightMeasure)).ae (heightLocalizedCylinder_all_coefficients_ae K hK F)
    exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq hh
  filter_upwards [indexedCoefficientPair_value_ae a s (localizedProfile K F)
    (localizedProfile_memLp K hK F) hr, hp, hz] with z hpair hproj hcoeff
  rw [hpair, hproj]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hcoeff k]

/-- Both coordinates are the actual native finite Fourier projections;
the second toLp exists because of the derivative identification above. -/
def localizedPhysicalProjection (a : ℝ) (s : Finset NonzeroMode)
    (K : Set PositiveHeight) (hK : MeasurableSet K) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G)
    (hr : ∀ k, MemLp (localizedProfile K F k) 2 (volume : Measure PositiveHeight)) :
    FunctionL2 a × DerivativeL2 a :=
  (((Lp.memLp (finiteFourierProjection s (heightLocalizedCylinder K hK F))).mono_measure
      Measure.restrict_le_self).toLp
        (finiteFourierProjection s (heightLocalizedCylinder K hK F)),
   (localized_projection_derivative_memLp a s K hK hweak hr).toLp
        (finiteFourierProjection s (heightLocalizedCylinder K hK G)))

theorem localizedPhysicalProjection_eq_coefficientPair (a : ℝ) (s : Finset NonzeroMode)
    (K : Set PositiveHeight) (hK : MeasurableSet K) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G)
    (hr : ∀ k, MemLp (localizedProfile K F k) 2 (volume : Measure PositiveHeight)) :
    localizedPhysicalProjection a s K hK hweak hr =
      indexedCoefficientPair a s (localizedProfile K F) (localizedProfile_memLp K hK F) hr := by
  apply Prod.ext
  · apply Lp.ext
    exact ((Lp.memLp (finiteFourierProjection s (heightLocalizedCylinder K hK F))).mono_measure
      Measure.restrict_le_self).coeFn_toLp.trans
        (localized_projection_value_ae a s K hK F hr).symm
  · apply Lp.ext
    exact (localized_projection_derivative_memLp a s K hK hweak hr).coeFn_toLp.trans
      (localized_projection_derivative_ae a s K hK hweak hr).symm

/-- Actual finite projections of a compact-height localized weak pair
belong to the physical classical graph closure, without an hWeakGraph
premise. Only local raw L² of the value coefficients is a primitive input. -/
theorem localizedPhysicalProjection_mem_closed_graph {a A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (s : Finset NonzeroMode) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G)
    (hr : ∀ k, MemLp (localizedProfile {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B} F k)
      2 (volume : Measure PositiveHeight)) :
    localizedPhysicalProjection a s {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
      ((isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)).measurableSet
      hweak hr ∈ closedHorizontalGraph 1 a := by
  classical
  let K : Set PositiveHeight := {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
  have hK : MeasurableSet K :=
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).measurableSet
  rw [localizedPhysicalProjection_eq_coefficientPair]
  have heq : indexedCoefficientPair a s (localizedProfile K F)
      (localizedProfile_memLp K hK F) hr =
      finiteCoefficientPair a (s.image ((↑) : NonzeroMode → ℤ)) (localizedProfile K F)
        (localizedProfile_memLp K hK F) hr := by
    unfold indexedCoefficientPair finiteCoefficientPair
    rw [Finset.sum_image]
    intro x hx y hy hxy
    exact Subtype.ext hxy
  rw [heq]
  apply finite_modes_mem_closed_graph hA hAB
  · intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    exact n.property
  · intro k y hy
    by_contra hnot
    exact hy (by simp [localizedProfile, K, hnot])

end
end ImbalancedChen.Part3.CuspPhysicalFourierProjectionIdentification20261026b
