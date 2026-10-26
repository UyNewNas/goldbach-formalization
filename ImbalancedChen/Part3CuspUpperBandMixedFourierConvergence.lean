import ImbalancedChen.Part3ActualCylinderFiniteFourierProjection
import ImbalancedChen.Part3ClosedHorizontalCuspTail
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The physical upper-band comparison dy <= B^2 dy/y^2 is proved from the
actual height density. It gives a native continuous map from weighted
cylinder L2 to raw-cylinder L2 after upper-height truncation. Actual
Fourier projections preserve every measurable height support, and the
existing weighted Fourier reconstruction therefore converges in BOTH
physical norms on a fixed upper band. No raw-norm convergence, graph
closure, Parseval theorem or height support conclusion is assumed.
-/
namespace ImbalancedChen.Part3.CuspUpperBandMixedFourierConvergence20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open ActualZeroMeanCylinderFourierUnitary20261026a
open ActualCylinderFiniteFourierProjection20261026b
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

def upperHeight (B : ℝ) : Set PositiveHeight := {y | (y : ℝ) ≤ B}
def upperCylinder (B : ℝ) : Set CuspCylinder := Set.univ ×ˢ upperHeight B
def upperNormBound (B : ℝ) : ℝ≥0 := ⟨B ^ 2, sq_nonneg _⟩

theorem upperHeight_measurable (B : ℝ) : MeasurableSet (upperHeight B) :=
  measurableSet_le measurable_subtype_coe measurable_const
theorem upperCylinder_measurable (B : ℝ) : MeasurableSet (upperCylinder B) :=
  MeasurableSet.univ.prod (upperHeight_measurable B)

/-- Literal physical height-measure comparison on 0 < y <= B. -/
theorem raw_height_upper_le_weighted {B : ℝ} (hB : 0 < B) :
    (volume : Measure PositiveHeight).restrict (upperHeight B) ≤
      (upperNormBound B : ℝ≥0∞) • heightMeasure.restrict (upperHeight B) := by
  let μ := (volume : Measure PositiveHeight).restrict (upperHeight B)
  have hm : Measurable (fun y : PositiveHeight => (heightDensity y : ℝ≥0∞)) :=
    heightDensity_continuous.measurable.coe_nnreal_ennreal
  calc
    _ = μ.withDensity (fun _ => (1 : ℝ≥0∞)) := (withDensity_one).symm
    _ ≤ μ.withDensity ((upperNormBound B : ℝ≥0∞) •
        (fun y => (heightDensity y : ℝ≥0∞))) := by
      apply withDensity_mono
      filter_upwards [ae_restrict_mem (upperHeight_measurable B)] with y hy
      change (1 : ℝ≥0∞) ≤ (upperNormBound B : ℝ≥0∞) * (heightDensity y : ℝ≥0∞)
      rw [← ENNReal.coe_mul]
      apply ENNReal.coe_le_coe.mpr
      change (1 : ℝ) ≤ B ^ 2 * (heightDensity y : ℝ)
      rw [heightDensity_coe]
      have hsq : (y : ℝ) ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ y.property.le hy 2
      have hy0 : (y : ℝ) ≠ 0 := y.property.ne'
      have he : B ^ 2 * (1 / (y : ℝ)) ^ 2 = B ^ 2 / (y : ℝ) ^ 2 := by
        rw [div_pow, one_pow]
        ring
      rw [he]
      exact (le_div_iff₀ (sq_pos_of_pos y.property)).mpr (by simpa using hsq)
    _ = _ := by
      rw [withDensity_smul _ hm]
      congr 1
      exact (restrict_withDensity (upperHeight_measurable B) _).symm

theorem raw_cylinder_upper_le_weighted {B : ℝ} (hB : 0 < B) :
    rawCylinderMeasure.restrict (upperCylinder B) ≤
      (upperNormBound B : ℝ≥0∞) • cylinderMeasure.restrict (upperCylinder B) := by
  have h := Measure.prod_mono (μ := AddCircle.haarAddCircle)
    (μ' := AddCircle.haarAddCircle) le_rfl (raw_height_upper_le_weighted hB)
  rw [Measure.prod_smul_right] at h
  simpa only [rawCylinderMeasure, cylinderMeasure, upperCylinder,
    ← Measure.prod_restrict, Measure.restrict_univ] using h

theorem raw_cylinder_upper_le_full_weighted {B : ℝ} (hB : 0 < B) :
    rawCylinderMeasure.restrict (upperCylinder B) ≤
      (upperNormBound B : ℝ≥0∞) • cylinderMeasure := by
  exact (raw_cylinder_upper_le_weighted hB).trans (by
    gcongr
    exact Measure.restrict_le_self)

section ZeroExtension
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) (hs : MeasurableSet s)

def restrictedZeroExtensionVector (u : Lp ℂ 2 (μ.restrict s)) : Lp ℂ 2 μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp u)).toLp (s.indicator u)

theorem restrictedZeroExtensionVector_ae (u : Lp ℂ 2 (μ.restrict s)) :
    (restrictedZeroExtensionVector μ s hs u : α → ℂ) =ᵐ[μ] s.indicator u :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp u)).coeFn_toLp

def restrictedZeroExtension : Lp ℂ 2 (μ.restrict s) →ₗᵢ[ℝ] Lp ℂ 2 μ where
  toFun := restrictedZeroExtensionVector μ s hs
  map_add' u v := by
    apply Lp.ext
    have huv := (ae_restrict_iff' hs).mp (Lp.coeFn_add u v)
    filter_upwards [restrictedZeroExtensionVector_ae μ s hs (u + v),
      restrictedZeroExtensionVector_ae μ s hs u,
      restrictedZeroExtensionVector_ae μ s hs v,
      Lp.coeFn_add (restrictedZeroExtensionVector μ s hs u)
        (restrictedZeroExtensionVector μ s hs v), huv] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, h₄, h₂, h₃]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Pi.add_apply, h₅ hx]
    · simp [hx]
  map_smul' c u := by
    apply Lp.ext
    have hcu := (ae_restrict_iff' hs).mp (Lp.coeFn_smul c u)
    filter_upwards [restrictedZeroExtensionVector_ae μ s hs (c • u),
      restrictedZeroExtensionVector_ae μ s hs u,
      Lp.coeFn_smul c (restrictedZeroExtensionVector μ s hs u), hcu]
      with x h₁ h₂ h₃ h₄
    rw [h₁, h₃, h₂]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Pi.smul_apply, h₄ hx]
    · simp [hx]
  norm_map' u := by
    rw [restrictedZeroExtensionVector, Lp.norm_toLp,
      eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.norm_def]

end ZeroExtension

abbrev RawCylinderL2 := Lp ℂ 2 rawCylinderMeasure

/-- The native weighted-to-raw map first restricts using the proved B^2
measure bound and then extends by zero isometrically. -/
def upperBandRawLift (B : ℝ) (hB : 0 < B) : CylinderL2 →L[ℝ] RawCylinderL2 :=
  (restrictedZeroExtension rawCylinderMeasure (upperCylinder B)
    (upperCylinder_measurable B)).toContinuousLinearMap.comp
    (Lp.LpToLpOfMeasureLeSMul (c := (upperNormBound B : ℝ≥0∞)) (by simp)
      (raw_cylinder_upper_le_full_weighted hB))

theorem upperBandRawLift_ae (B : ℝ) (hB : 0 < B) (F : CylinderL2) :
    (upperBandRawLift B hB F : CuspCylinder → ℂ) =ᵐ[rawCylinderMeasure]
      (upperCylinder B).indicator F := by
  let R : CylinderL2 →L[ℝ] Lp ℂ 2 (rawCylinderMeasure.restrict (upperCylinder B)) :=
    Lp.LpToLpOfMeasureLeSMul (c := (upperNormBound B : ℝ≥0∞)) (by simp)
      (raw_cylinder_upper_le_full_weighted hB)
  have hR := (ae_restrict_iff' (upperCylinder_measurable B)).mp
    (Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
      (raw_cylinder_upper_le_full_weighted hB) F)
  filter_upwards [restrictedZeroExtensionVector_ae rawCylinderMeasure
    (upperCylinder B) (upperCylinder_measurable B) (R F), hR] with z hz hRz
  change upperBandRawLift B hB F z = _
  change (restrictedZeroExtensionVector rawCylinderMeasure (upperCylinder B)
    (upperCylinder_measurable B) (R F)) z = _
  rw [hz]
  by_cases hzt : z ∈ upperCylinder B
  · simp [hzt, hRz hzt]
  · simp [hzt]

def valueTailMap (a : ℝ) : CylinderL2 →L[ℝ] FunctionL2 a :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    simpa only [one_smul] using (Measure.restrict_le_self : functionMeasure a ≤ cylinderMeasure))

def rawTailMap (a : ℝ) : RawCylinderL2 →L[ℝ] DerivativeL2 a :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    simpa only [one_smul] using (Measure.restrict_le_self : derivativeMeasure a ≤ rawCylinderMeasure))

def bandDerivativeMap (a B : ℝ) (hB : 0 < B) : CylinderL2 →L[ℝ] DerivativeL2 a :=
  (rawTailMap a).comp (upperBandRawLift B hB)

theorem bandDerivativeMap_ae (a B : ℝ) (hB : 0 < B) (F : CylinderL2) :
    (bandDerivativeMap a B hB F : CuspCylinder → ℂ) =ᵐ[derivativeMeasure a]
      (upperCylinder B).indicator F := by
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
    (by simpa only [one_smul] using
      (Measure.restrict_le_self : derivativeMeasure a ≤ rawCylinderMeasure))
    (upperBandRawLift B hB F)).trans
      ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq
        (upperBandRawLift_ae B hB F))

/-- Physical mixed-norm convergence of the actual finite reconstruction.
The second limit is raw dy, and its upper-band truncation is explicit. -/
theorem mixed_finiteFourierProjection_tendsto (a B : ℝ) (hB : 0 < B)
    (F G : zeroMeanCylinder) :
    Tendsto (fun s : Finset NonzeroMode =>
      (valueTailMap a (finiteFourierProjection s (F : CylinderL2)),
       bandDerivativeMap a B hB (finiteFourierProjection s (G : CylinderL2)))) atTop
      (𝓝 (valueTailMap a (F : CylinderL2), bandDerivativeMap a B hB (G : CylinderL2))) := by
  exact (((valueTailMap a).continuous.tendsto _).comp
    (finiteFourierProjection_tendsto F)).prodMk_nhds
      (((bandDerivativeMap a B hB).continuous.tendsto _).comp
        (finiteFourierProjection_tendsto G))

/-- Fourier projection cannot create values at a height where the input
vanishes. This is proved by actual AE product slicing and literal Fourier
coefficients, including the zero representative on the complement. -/
theorem finiteFourierProjection_preserves_height_support
    (K : Set PositiveHeight) (hK : MeasurableSet K) (s : Finset NonzeroMode)
    (F : CylinderL2)
    (hF : ∀ᵐ z ∂cylinderMeasure, z.2 ∉ K → F z = 0) :
    ∀ᵐ z ∂cylinderMeasure, z.2 ∉ K → finiteFourierProjection s F z = 0 := by
  have hm : MeasurableSet {z : CuspCylinder | z.2 ∈ K ∨ F z = 0} :=
    (hK.preimage measurable_snd).union
      (measurableSet_eq_fun (Lp.stronglyMeasurable F).measurable measurable_const)
  have hF' : ∀ᵐ z ∂cylinderMeasure, z.2 ∈ K ∨ F z = 0 := by
    filter_upwards [hF] with z hz
    by_cases h : z.2 ∈ K
    · exact Or.inl h
    · exact Or.inr (hz h)
  have hslice : ∀ᵐ y ∂heightMeasure, ∀ᵐ x ∂AddCircle.haarAddCircle,
      y ∈ K ∨ F (x, y) = 0 :=
    (ae_ae_comm hm).mp ((ae_prod_iff_ae_ae hm).mp hF')
  have hc : ∀ᵐ y ∂heightMeasure, y ∉ K → ∀ n : ℤ, sliceCoefficient n F y = 0 := by
    filter_upwards [hslice] with y hy
    intro hyK n
    change (∫ x : UnitAddCircle, AddCircle.fourier (-n) x * F (x, y)
      ∂AddCircle.haarAddCircle) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [hy] with x hx
    rw [hx.resolve_left hyK, mul_zero]
  have hz := (quasiMeasurePreserving_snd (μ := AddCircle.haarAddCircle)
    (ν := heightMeasure)).ae hc
  filter_upwards [finiteFourierProjection_ae s F, hz] with z hp hc
  intro hzK
  rw [hp]
  apply Finset.sum_eq_zero
  intro n hn
  rw [hc hzK n, mul_zero]

end
end ImbalancedChen.Part3.CuspUpperBandMixedFourierConvergence20261026b
