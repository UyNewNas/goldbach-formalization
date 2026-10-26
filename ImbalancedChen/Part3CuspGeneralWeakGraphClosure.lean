import ImbalancedChen.Part3CuspPhysicalCutoffRealization
import ImbalancedChen.Part3CuspUpperBandMixedFourierConvergence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The general positive-tail weak horizontal graph is contained in the
closure of actual classical zero-mean pairs in the TWO physical L² norms.
The proof derives local raw coefficient L² from the actual upper-band
measure comparison, identifies the actual finite Fourier projections
with physical coefficient reconstructions, passes to their mixed-norm
limit, and finally uses the same height exhaustion in both coordinates.

There is no graph-closure, approximation, coercivity, Fourier coefficient
equation, or raw convergence premise. The inputs are the genuine tensor
weak equation and the actual horizontal zero mean. This is a literal
period-one cylinder theorem, not an identification of a Gamma quotient
form domain with cusp-coordinate weak pairs.
-/
namespace ImbalancedChen.Part3.CuspGeneralWeakGraphClosure20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a ActualZeroMeanCylinderFourierUnitary20261026a
open ActualCylinderFiniteFourierProjection20261026b
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open CuspPhysicalWeakTailModes20261026b CuspWeakCylinderFourierModes20261026b
open CuspPhysicalHeightExhaustion20261026b CuspHeightCutoffFourierModes20261026b
open CuspPhysicalFourierProjectionIdentification20261026b
open CuspPhysicalCutoffRealization20261026b CuspUpperBandMixedFourierConvergence20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

/-- A genuine weighted L² profile supported at bounded height is also in
raw height L², by the independently proved dy ≤ B² dy/y² inequality. -/
theorem supported_height_raw_memLp {B : ℝ} (hB : 0 < B)
    {f : PositiveHeight → ℂ} (hf : MemLp f 2 heightMeasure)
    (hs : Function.support f ⊆ upperHeight B) :
    MemLp f 2 (volume : Measure PositiveHeight) := by
  have hraw : MemLp f 2 ((volume : Measure PositiveHeight).restrict (upperHeight B)) :=
    (hf.restrict (upperHeight B)).of_measure_le_smul (by simp)
      (raw_height_upper_le_weighted hB)
  have hi := (memLp_indicator_iff_restrict (upperHeight_measurable B)).mpr hraw
  have heq : (upperHeight B).indicator f = f := by
    funext y
    by_cases hy : y ∈ upperHeight B
    · simp [hy]
    · have hz : f y = 0 := by
        by_contra h
        exact hy (hs h)
      simp [hy, hz]
  rwa [heq] at hi

theorem compact_localizedProfile_raw_memLp {A B : ℝ} (hB : 0 < B)
    (F : CylinderL2) (k : ℤ) :
    MemLp (localizedProfile {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B} F k)
      2 (volume : Measure PositiveHeight) := by
  have hK : MeasurableSet {y : PositiveHeight | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B} :=
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).measurableSet
  apply supported_height_raw_memLp hB (localizedProfile_memLp _ hK F k)
  intro y hy
  by_contra hnot
  have hzero : localizedProfile {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B} F k y = 0 := by
    have hyB : ¬ (y : ℝ) ≤ B := hnot
    have hyK : y ∉ {y : PositiveHeight | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B} :=
      fun h => hyB h.2
    simp [localizedProfile, hyK]
  exact hy hzero

private theorem rawCylinder_ac_weighted : rawCylinderMeasure ≪ cylinderMeasure := by
  have hh : (volume : Measure PositiveHeight) ≪ heightMeasure :=
    withDensity_absolutelyContinuous'
      heightDensity_continuous.measurable.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun y => ENNReal.coe_ne_zero.mpr (heightDensity_pos y).ne')
  exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl hh

private theorem localized_zero_outside (K : Set PositiveHeight) (hK : MeasurableSet K)
    (F : CylinderL2) :
    ∀ᵐ z ∂cylinderMeasure, z.2 ∉ K → heightLocalizedCylinder K hK F z = 0 := by
  filter_upwards [indicatorVector_ae (univ ×ˢ K) (MeasurableSet.univ.prod hK) F] with z hz
  intro hnot
  simpa [heightLocalizedCylinder, hnot] using hz

private theorem weak_derivative_mem_zeroMean {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) : G ∈ zeroMeanCylinder := by
  change cylinderCoefficient 0 G = 0
  rw [weak_cylinder_coefficient hweak 0]
  simp [modeFrequency]

private theorem projection_maps_eq_physical {a A B : ℝ} (hB : 0 < B)
    (s : Finset NonzeroMode) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) :
    (valueTailMap a (finiteFourierProjection s (heightLocalizedCylinder
      {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
      (((isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)).measurableSet) F)),
     bandDerivativeMap a B hB (finiteFourierProjection s (heightLocalizedCylinder
      {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
      (((isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)).measurableSet) G))) =
    localizedPhysicalProjection a s {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
      (((isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)).measurableSet)
      hweak (compact_localizedProfile_raw_memLp hB F) := by
  let K : Set PositiveHeight := {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
  have hK : MeasurableSet K :=
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).measurableSet
  have hsupport := finiteFourierProjection_preserves_height_support K hK s
    (heightLocalizedCylinder K hK G) (localized_zero_outside K hK G)
  have hsupportRaw := (hsupport.filter_mono rawCylinder_ac_weighted.ae_le).filter_mono
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le
  apply Prod.ext
  · apply Lp.ext
    exact (Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
      (by simpa only [one_smul] using
        (Measure.restrict_le_self : functionMeasure a ≤ cylinderMeasure)) _).trans
      (((Lp.memLp (finiteFourierProjection s (heightLocalizedCylinder K hK F))).mono_measure
        Measure.restrict_le_self).coeFn_toLp).symm
  · apply Lp.ext
    filter_upwards [bandDerivativeMap_ae a B hB
      (finiteFourierProjection s (heightLocalizedCylinder K hK G)),
      (localized_projection_derivative_memLp a s K hK hweak
        (compact_localizedProfile_raw_memLp hB F)).coeFn_toLp,
      hsupportRaw] with z hmap hphys hs
    rw [hmap, hphys]
    by_cases hz : z ∈ upperCylinder B
    · simp [hz]
    · have hzK : z.2 ∉ K := by
        intro hk
        exact hz ⟨mem_univ _, hk.2⟩
      simp [hz, hs hzK]

/-- A compact height localization of an arbitrary native weighted weak
pair lies in the actual physical graph closure after taking the finite
Fourier net limit in BOTH norms. -/
theorem compact_localized_weak_pair_mem_closed_graph {a A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) {F G : CylinderL2}
    (hweak : HasWeakWeightedCylinderDerivative F G) (hmean : F ∈ zeroMeanCylinder) :
    (valueTailMap a (heightLocalizedCylinder {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
      (((isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)).measurableSet) F),
     bandDerivativeMap a B (hA.trans_le hAB)
      (heightLocalizedCylinder {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
        (((isClosed_le continuous_const continuous_subtype_val).inter
          (isClosed_le continuous_subtype_val continuous_const)).measurableSet) G))
      ∈ closedHorizontalGraph 1 a := by
  let K : Set PositiveHeight := {y | A ≤ (y : ℝ) ∧ (y : ℝ) ≤ B}
  have hK : MeasurableSet K :=
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).measurableSet
  have hF := heightLocalizedCylinder_zero_mean K hK hmean
  have hG := heightLocalizedCylinder_zero_mean K hK (weak_derivative_mem_zeroMean hweak)
  have ht := mixed_finiteFourierProjection_tendsto a B (hA.trans_le hAB)
    ⟨heightLocalizedCylinder K hK F, hF⟩ ⟨heightLocalizedCylinder K hK G, hG⟩
  apply isClosed_closure.mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  rw [projection_maps_eq_physical (hA.trans_le hAB) s hweak]
  exact localizedPhysicalProjection_mem_closed_graph hA hAB s hweak
    (compact_localizedProfile_raw_memLp (hA.trans_le hAB) F)

private theorem valueTailMap_tailValue (a : ℝ) (u : FunctionL2 a) :
    valueTailMap a (tailValue a u) = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (by simp)
      (by simpa only [one_smul] using
        (Measure.restrict_le_self : functionMeasure a ≤ cylinderMeasure)) (tailValue a u),
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq (tailValue_ae a u),
    ae_restrict_mem (strictCylinderTail_measurable a)] with z hmap hvalue hz
  simp only [hmap, hvalue, indicator_of_mem hz]

private theorem bandDerivativeMap_tailDerivative {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (d : DerivativeL2 a) (hs : ∀ᵐ z ∂derivativeMeasure a, z ∉ upperCylinder B → d z = 0) :
    bandDerivativeMap a B hB (tailDerivative a ha d) = d := by
  have hd := (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq
    (rawCylinder_ac_weighted.ae_eq (tailDerivative_ae a ha d))
  apply Lp.ext
  filter_upwards [bandDerivativeMap_ae a B hB (tailDerivative a ha d), hd, hs,
    ae_restrict_mem (strictCylinderTail_measurable a)] with z hmap hd hs hz
  rw [hmap]
  by_cases hu : z ∈ upperCylinder B
  · simp [hu, hd, hz]
  · simp [hu, hs hu]

private theorem tailValue_mem_zeroMean_of_mean (a : ℝ) (u : FunctionL2 a)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    tailValue a u ∈ zeroMeanCylinder := by
  apply (mem_zeroMeanCylinder_iff _).mpr
  have hswap : ∀ᵐ p : PositiveHeight × UnitAddCircle
      ∂heightMeasure.prod (AddCircle.haarAddCircle (T := (1 : ℝ))),
      tailValue a u (p.2, p.1) = (strictCylinderTail a).indicator u (p.2, p.1) :=
    (Measure.measurePreserving_swap.quasiMeasurePreserving).ae (tailValue_ae a u)
  filter_upwards [ae_ae_of_ae_prod hswap, hmean] with y hy hm
  rw [integral_congr_ae hy]
  by_cases ha : a < (y : ℝ)
  · simpa [strictCylinderTail, strictHeightTail, ha] using hm ha
  · simp [strictCylinderTail, strictHeightTail, ha]

/-- The full arbitrary height-dependent physical weak graph inclusion.
The weak equation and literal horizontal zero mean are the only analytic
inputs besides membership in the two physical L² spaces. -/
theorem weak_physical_pair_mem_closed_graph {a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative 1 a u d)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    (u, d) ∈ closedHorizontalGraph 1 a := by
  have hnative : HasWeakWeightedCylinderDerivative (tailValue a u) (tailDerivative a ha d) := by
    simpa only [Complex.ofReal_one, one_smul] using physical_tail_native_weak ha hweak
  have hF := tailValue_mem_zeroMean_of_mean a u hmean
  have hcut (n : ℕ) : physicalHeightCutoff a n (u, d) ∈ closedHorizontalGraph 1 a := by
    have hB : 0 < a + (n : ℝ) + 1 := by positivity
    have hAB : a ≤ a + (n : ℝ) + 1 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hc := compact_localized_weak_pair_mem_closed_graph (a := a) ha hAB hnative hF
    have hdSupport : ∀ᵐ z ∂derivativeMeasure a, z ∉ upperCylinder (a + (n : ℝ) + 1) →
        (physicalHeightCutoff a n (u, d)).2 z = 0 := by
      filter_upwards [indicatorVector_ae (cylinderHeightBand a n)
        (cylinderHeightBand_measurable a n) d] with z hz
      intro hupper
      have hnot : z ∉ cylinderHeightBand a n := by
        intro hband
        exact hupper ⟨mem_univ _, hband.2.2⟩
      simpa [physicalHeightCutoff, hnot] using hz
    rw [← physicalHeightCutoff_value_realization a n (u, d),
      ← physicalHeightCutoff_derivative_realization ha n (u, d),
      valueTailMap_tailValue,
      bandDerivativeMap_tailDerivative ha hB _ hdSupport] at hc
    exact hc
  exact isClosed_closure.mem_of_tendsto (physicalHeightCutoff_tendsto a (u, d))
    (Eventually.of_forall hcut)

/-- Sharp normalized period-one tail estimate for a genuine arbitrary
height-dependent distributional weak pair. -/
theorem weak_physical_pair_sharp_tail {a Y : ℝ} (ha : 0 < a) (hY : 0 < Y)
    (haY : a ≤ Y) {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative 1 a u d)
    (hmean : ∀ᵐ y ∂heightMeasure, a < (y : ℝ) →
      (∫ x : UnitAddCircle, u (x, y) ∂AddCircle.haarAddCircle) = 0) :
    ‖tailRestriction a Y haY u‖^2 ≤ (4 * Real.pi^2 * Y^2)⁻¹ * ‖d‖^2 := by
  simpa only [one_pow, one_div] using
    closed_horizontal_tail_bound (w := 1) (by norm_num) hY haY
      (weak_physical_pair_mem_closed_graph ha hweak hmean)

end
end ImbalancedChen.Part3.CuspGeneralWeakGraphClosure20261026b
