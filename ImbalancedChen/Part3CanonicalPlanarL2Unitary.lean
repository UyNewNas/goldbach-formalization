import ImbalancedChen.Part3MaassWeightedCoordinateL2
import ImbalancedChen.Part3UpperHalfPlaneHyperbolicMeasure
import ImbalancedChen.Part3MaassGradientUpperSupportClosure
import ImbalancedChen.Part3MaassTensorHeightLift
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
An actual complex-linear unitary from canonical hyperbolic L2 to the actual
upper-supported planar L2 subspace. Forward divides by height and extends
by zero; inverse multiplies by height. All MemLp, a.e. transport, and inverse
laws use the actual canonical measure, with no measure/isometry supplier.
-/

noncomputable section

namespace ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly

open MeasureTheory Set
open scoped ComplexInnerProductSpace
open CanonicalTensorHyperbolicLaplacianForm20261024z
open MaassWeightedCoordinateL220261024zz UpperHalfPlaneHyperbolicMeasure20261024z
open MaassWeakOperatorCore20261024zz MaassFiniteCoreResolventCoercivity20261025a
open MaassFiniteCoreL2Graph20261025a MaassFirstGradientWeakLimit20261025a
open MaassGradientUpperSupportClosure20261025a MaassTensorHeightLift20261025a

/-- The literal real-imaginary chart map. -/
def chartMap (z : UpperHalfPlane) : ℝ × ℝ :=
  Complex.measurableEquivRealProd (z : ℂ)

theorem chartMap_measurableEmbedding : MeasurableEmbedding chartMap :=
  Complex.measurableEquivRealProd.measurableEmbedding.comp
    UpperHalfPlane.measurableEmbedding_coe

/-- Actual unweighted measure transport, before the y^-2 density. -/
theorem map_coordinateMeasure :
    Measure.map chartMap coordinateMeasure =
      (volume : Measure (ℝ × ℝ)).restrict upperChart := by
  change Measure.map (Complex.measurableEquivRealProd ∘ UpperHalfPlane.coe)
    ((volume : Measure ℂ).comap UpperHalfPlane.coe) = _
  rw [← Measure.map_map Complex.measurableEquivRealProd.measurable
    UpperHalfPlane.measurableEmbedding_coe.measurable,
    UpperHalfPlane.measurableEmbedding_coe.map_comap,
    range_upperHalfPlane_coe_eq_chart_preimage]
  exact (Complex.volume_preserving_equiv_real_prod.restrict_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding upperChart).map_eq

private theorem coordinate_ac_hyperbolic :
    coordinateMeasure ≪ (volume : Measure UpperHalfPlane) :=
  coordinateMeasure_absolutelyContinuous_hyperbolic

private theorem hyperbolic_ac_coordinate :
    (volume : Measure UpperHalfPlane) ≪ coordinateMeasure :=
  hyperbolicMeasure_absolutelyContinuous_coordinate

theorem chartMap_quasiMeasurePreserving :
    QuasiMeasurePreserving chartMap (volume : Measure UpperHalfPlane)
      (volume : Measure (ℝ × ℝ)) := by
  have h : QuasiMeasurePreserving chartMap coordinateMeasure
      (volume : Measure (ℝ × ℝ)) := by
    refine ⟨chartMap_measurableEmbedding.measurable, ?_⟩
    rw [map_coordinateMeasure]
    exact Measure.restrict_le_self.absolutelyContinuous
  exact h.mono_left hyperbolic_ac_coordinate

private theorem ae_chart_iff (P : ℝ × ℝ → Prop) :
    (∀ᵐ p ∂((volume : Measure (ℝ × ℝ)).restrict upperChart), P p) ↔
      ∀ᵐ z ∂coordinateMeasure, P (chartMap z) := by
  rw [← map_coordinateMeasure]
  exact chartMap_measurableEmbedding.ae_map_iff

/-- Divide by y on the actual chart and zero extend. -/
def forwardFunction (F : UpperHalfPlane → ℂ) : ℝ × ℝ → ℂ :=
  unweightChart (chartPullback F)

theorem forwardFunction_at_upper (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    forwardFunction F (chartMap z) = (z.im⁻¹ : ℝ) • F z := by
  have hz : chartMap z ∈ upperChart := z.im_pos
  unfold forwardFunction unweightChart
  rw [dif_pos hz, chartPullback_at_upper]
  rfl

theorem forwardFunction_zero_outside (F : UpperHalfPlane → ℂ)
    (p : ℝ × ℝ) (hp : p ∉ upperChart) : forwardFunction F p = 0 := by
  simp [forwardFunction, unweightChart, hp]

private theorem forwardFunction_indicator (F : UpperHalfPlane → ℂ) :
    upperChart.indicator (forwardFunction F) = forwardFunction F := by
  funext p
  by_cases hp : p ∈ upperChart
  · simp [hp]
  · simp [hp, forwardFunction_zero_outside F p hp]

/-- Genuine quotient well-definedness under canonical a.e. equality. -/
theorem forwardFunction_congr_ae {F G : UpperHalfPlane → ℂ}
    (h : F =ᵐ[(volume : Measure UpperHalfPlane)] G) :
    forwardFunction F =ᵐ[(volume : Measure (ℝ × ℝ))] forwardFunction G := by
  have hcoord := coordinate_ac_hyperbolic.ae_le h
  have hr : forwardFunction F =ᵐ[(volume : Measure (ℝ × ℝ)).restrict upperChart]
      forwardFunction G := (ae_chart_iff _).2 (by
    filter_upwards [hcoord] with z hz
    rw [forwardFunction_at_upper, forwardFunction_at_upper, hz])
  have hr' := (ae_restrict_iff' upperChart_measurable).1 hr
  filter_upwards [hr'] with p hp
  by_cases hu : p ∈ upperChart
  · exact hp hu
  · rw [forwardFunction_zero_outside F p hu, forwardFunction_zero_outside G p hu]

private theorem density_norm_sq (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    upperDensityNN z • ‖F z‖ ^ 2 = ‖forwardFunction F (chartMap z)‖ ^ 2 := by
  rw [forwardFunction_at_upper, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [upperDensityNN_eq_chartWeight]
  rfl

/-- Actual MemLp transport, not inferred from a possibly nonintegrable
Bochner integral equality. -/
theorem forwardFunction_memLp {F : UpperHalfPlane → ℂ}
    (hF : MemLp F 2 (volume : Measure UpperHalfPlane)) :
    MemLp (forwardFunction F) 2 (volume : Measure (ℝ × ℝ)) := by
  have hFm := hF.aestronglyMeasurable.mono_ac coordinate_ac_hyperbolic
  have hweight : Continuous (fun z : UpperHalfPlane => z.im⁻¹) :=
    UpperHalfPlane.continuous_im.inv₀ (fun z => ne_of_gt z.im_pos)
  have hmcoord : AEStronglyMeasurable (forwardFunction F ∘ chartMap) coordinateMeasure := by
    have hm := hweight.aestronglyMeasurable.smul hFm
    exact hm.congr (Filter.Eventually.of_forall fun z =>
      (forwardFunction_at_upper F z).symm)
  have hmrestrict : AEStronglyMeasurable (forwardFunction F)
      ((volume : Measure (ℝ × ℝ)).restrict upperChart) := by
    rw [← map_coordinateMeasure]
    exact chartMap_measurableEmbedding.aestronglyMeasurable_map_iff.mpr hmcoord
  have hs := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  change Integrable (fun z => ‖F z‖ ^ 2)
    (coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞))) at hs
  have hsw := (integrable_withDensity_iff_integrable_smul upperDensityNN_measurable).1 hs
  have hscoord : Integrable
      ((fun p : ℝ × ℝ => ‖forwardFunction F p‖ ^ 2) ∘ chartMap) coordinateMeasure :=
    hsw.congr (Filter.Eventually.of_forall (density_norm_sq F))
  have hsrestrict : Integrable (fun p : ℝ × ℝ => ‖forwardFunction F p‖ ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict upperChart) := by
    rw [← map_coordinateMeasure]
    exact chartMap_measurableEmbedding.integrable_map_iff.mpr hscoord
  have hlp := (memLp_two_iff_integrable_sq_norm hmrestrict).2 hsrestrict
  have hi := (memLp_indicator_iff_restrict upperChart_measurable).2 hlp
  simpa only [forwardFunction_indicator] using hi

/-- Actual planar quotient class, obtained only after MemLp was proved. -/
def forwardL2 (F : HyperbolicL2) : PlaneL2 :=
  (forwardFunction_memLp (Lp.memLp F)).toLp (forwardFunction F)

theorem forwardL2_coe_ae (F : HyperbolicL2) :
    (forwardL2 F : ℝ × ℝ → ℂ) =ᵐ[volume] forwardFunction F :=
  (forwardFunction_memLp (Lp.memLp F)).coeFn_toLp

theorem forwardL2_mem_upperSupported (F : HyperbolicL2) :
    forwardL2 F ∈ upperSupportedSubmodule := by
  filter_upwards [forwardL2_coe_ae F] with p hp
  intro hu
  rw [hp, forwardFunction_zero_outside F p hu]

private theorem forwardFunction_add (F G : UpperHalfPlane → ℂ) (p : ℝ × ℝ) :
    forwardFunction (fun z => F z + G z) p = forwardFunction F p + forwardFunction G p := by
  by_cases hp : p ∈ upperChart <;>
    simp [forwardFunction, unweightChart, chartPullback, hp, smul_add]

private theorem forwardFunction_smul (c : ℂ) (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) :
    forwardFunction (fun z => c • F z) p = c • forwardFunction F p := by
  by_cases hp : p ∈ upperChart <;>
    simp [forwardFunction, unweightChart, chartPullback, hp,
      Complex.real_smul, smul_eq_mul] <;> ring

private theorem forwardL2_add (F G : HyperbolicL2) :
    forwardL2 (F + G) = forwardL2 F + forwardL2 G := by
  apply Lp.ext
  have hsum := forwardFunction_congr_ae (Lp.coeFn_add F G)
  filter_upwards [forwardL2_coe_ae (F + G), forwardL2_coe_ae F,
    forwardL2_coe_ae G, hsum, Lp.coeFn_add (forwardL2 F) (forwardL2 G)]
    with p hp hF hG hs hout
  change forwardFunction (F + G) p = forwardFunction (fun z => F z + G z) p at hs
  change (forwardL2 F + forwardL2 G) p = forwardL2 F p + forwardL2 G p at hout
  rw [hp, hs, forwardFunction_add, hout, hF, hG]

private theorem forwardL2_smul (c : ℂ) (F : HyperbolicL2) :
    forwardL2 (c • F) = c • forwardL2 F := by
  apply Lp.ext
  have hsmul := forwardFunction_congr_ae (Lp.coeFn_smul c F)
  filter_upwards [forwardL2_coe_ae (c • F), forwardL2_coe_ae F,
    hsmul, Lp.coeFn_smul c (forwardL2 F)] with p hp hF hs hout
  change forwardFunction (c • F) p = forwardFunction (fun z => c • F z) p at hs
  change (c • forwardL2 F) p = c • forwardL2 F p at hout
  rw [hp, hs, forwardFunction_smul, hout, hF]

private theorem integral_norm_sq_lp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

theorem forwardL2_norm (F : HyperbolicL2) : ‖forwardL2 F‖ = ‖F‖ := by
  have hs : ‖forwardL2 F‖ ^ 2 = ‖F‖ ^ 2 := by
    calc
      _ = ∫ p : ℝ × ℝ, ‖forwardL2 F p‖ ^ 2 := (integral_norm_sq_lp _ _).symm
      _ = ∫ p : ℝ × ℝ, ‖forwardFunction F p‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [forwardL2_coe_ae F] with p hp
        rw [hp]
      _ = ∫ z : UpperHalfPlane, ‖F z‖ ^ 2 := (canonicalL2_square_eq_unweight F).symm
      _ = _ := integral_norm_sq_lp _ _
  nlinarith [norm_nonneg (forwardL2 F), norm_nonneg F]

/-- Inverse formula on actual functions. -/
def inverseFunction (G : ℝ × ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℝ) • G (chartMap z)

private theorem inverse_density_norm_sq (G : ℝ × ℝ → ℂ) (z : UpperHalfPlane) :
    upperDensityNN z • ‖inverseFunction G z‖ ^ 2 = ‖G (chartMap z)‖ ^ 2 := by
  rw [upperDensityNN_eq_chartWeight]
  change (z.im⁻¹) ^ 2 * ‖(z.im : ℝ) • G (chartMap z)‖ ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc : (z.im⁻¹) ^ 2 * z.im ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt z.im_pos), one_pow]
  rw [← mul_assoc, hc, one_mul]

/-- Multiplication by y pulls every planar L2 function to canonical L2. -/
theorem inverseFunction_memLp {G : ℝ × ℝ → ℂ}
    (hG : MemLp G 2 (volume : Measure (ℝ × ℝ))) :
    MemLp (inverseFunction G) 2 (volume : Measure UpperHalfPlane) := by
  have hm : AEStronglyMeasurable (inverseFunction G) (volume : Measure UpperHalfPlane) :=
    UpperHalfPlane.continuous_im.aestronglyMeasurable.smul
      (hG.aestronglyMeasurable.comp_quasiMeasurePreserving chartMap_quasiMeasurePreserving)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  change Integrable (fun z => ‖inverseFunction G z‖ ^ 2)
    (coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞)))
  apply (integrable_withDensity_iff_integrable_smul upperDensityNN_measurable).2
  have hs := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).1 hG
  have hsrestrict := hs.mono_measure (Measure.restrict_le_self (s := upperChart))
  have hscoord : Integrable
      ((fun p : ℝ × ℝ => ‖G p‖ ^ 2) ∘ chartMap) coordinateMeasure := by
    apply chartMap_measurableEmbedding.integrable_map_iff.mp
    simpa only [map_coordinateMeasure] using hsrestrict
  exact hscoord.congr (Filter.Eventually.of_forall fun z =>
    (inverse_density_norm_sq G z).symm)

def inverseL2 (G : PlaneL2) : HyperbolicL2 :=
  (inverseFunction_memLp (Lp.memLp G)).toLp (inverseFunction G)

theorem inverseL2_coe_ae (G : PlaneL2) :
    (inverseL2 G : UpperHalfPlane → ℂ) =ᵐ[volume] inverseFunction G :=
  (inverseFunction_memLp (Lp.memLp G)).coeFn_toLp

theorem inverseL2_forwardL2 (F : HyperbolicL2) : inverseL2 (forwardL2 F) = F := by
  apply Lp.ext
  filter_upwards [inverseL2_coe_ae (forwardL2 F),
    chartMap_quasiMeasurePreserving.ae_eq (forwardL2_coe_ae F)] with z hz hp
  change forwardL2 F (chartMap z) = forwardFunction F (chartMap z) at hp
  rw [hz]
  unfold inverseFunction
  rw [hp, forwardFunction_at_upper, smul_smul,
    mul_inv_cancel₀ (ne_of_gt z.im_pos), one_smul]

theorem forwardL2_inverseL2 (G : PlaneL2) (hG : G ∈ upperSupportedSubmodule) :
    forwardL2 (inverseL2 G) = G := by
  apply Lp.ext
  have hicoord := coordinate_ac_hyperbolic.ae_le (inverseL2_coe_ae G)
  have hr : forwardFunction (inverseL2 G) =ᵐ[
      (volume : Measure (ℝ × ℝ)).restrict upperChart] G := (ae_chart_iff _).2 (by
    filter_upwards [hicoord] with z hz
    rw [forwardFunction_at_upper, hz]
    unfold inverseFunction
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt z.im_pos), one_smul])
  have hr' := (ae_restrict_iff' upperChart_measurable).1 hr
  filter_upwards [forwardL2_coe_ae (inverseL2 G), hr', hG] with p hp hu hout
  rw [hp]
  by_cases hin : p ∈ upperChart
  · exact hu hin
  · rw [forwardFunction_zero_outside _ p hin, hout hin]

/-- The genuine quotient-space unitary, using the actual canonical
hyperbolic measure and the already defined upper-supported planar space. -/
def canonicalPlanarUnitary : HyperbolicL2 ≃ₗᵢ[ℂ] upperSupportedSubmodule where
  toFun F := ⟨forwardL2 F, forwardL2_mem_upperSupported F⟩
  invFun G := inverseL2 (G : PlaneL2)
  left_inv := inverseL2_forwardL2
  right_inv G := Subtype.ext (forwardL2_inverseL2 (G : PlaneL2) G.property)
  map_add' F G := Subtype.ext (forwardL2_add F G)
  map_smul' c F := Subtype.ext (forwardL2_smul c F)
  norm_map' := forwardL2_norm

theorem canonicalPlanarUnitary_forward_coe_ae (F : HyperbolicL2) :
    ((canonicalPlanarUnitary F : PlaneL2) : ℝ × ℝ → ℂ) =ᵐ[volume]
      unweightChart (chartPullback F) := forwardL2_coe_ae F

theorem canonicalPlanarUnitary_inverse_coe_ae (G : upperSupportedSubmodule) :
    (canonicalPlanarUnitary.symm G : UpperHalfPlane → ℂ) =ᵐ[volume]
      fun z => (z.im : ℝ) • (G : PlaneL2) (chartMap z) := inverseL2_coe_ae _

/-- The actual planar test tensor belongs to the existing supported space. -/
theorem testL2_mem_upperSupported (T : CompactTensor) : testL2 T ∈ upperSupportedSubmodule := by
  have h := (separated_plane_memLp T.horizontal T.vertical T.horizontal_smooth.continuous
    T.vertical_smooth.continuous T.horizontal_compact T.vertical_compact).coeFn_toLp
  filter_upwards [h] with p hp
  intro hout
  change testL2 T p = tensorFunction T.horizontal T.vertical p at hp
  rw [hp]
  have hv : T.vertical p.2 = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => hout (T.vertical_positive h))
  simp [tensorFunction, hv]

/-- Exact inverse on the actual planar tensor generator, ready for the
canonical actualTensorDomain density pullback. -/
theorem unitary_inverse_testL2 (T : CompactTensor) :
    canonicalPlanarUnitary.symm ⟨testL2 T, testL2_mem_upperSupported T⟩ =
      finiteCoreL2 (Finset.univ : Finset (Fin 1)) (fun _ => heightMultiplyTensor T) := by
  apply Lp.ext
  have ht := (separated_plane_memLp T.horizontal T.vertical T.horizontal_smooth.continuous
    T.vertical_smooth.continuous T.horizontal_compact T.vertical_compact).coeFn_toLp
  have htest := chartMap_quasiMeasurePreserving.ae_eq ht
  have hfinite := (finiteCoreFunction_memLp (Finset.univ : Finset (Fin 1))
    (fun _ => heightMultiplyTensor T)).coeFn_toLp
  filter_upwards [canonicalPlanarUnitary_inverse_coe_ae
    ⟨testL2 T, testL2_mem_upperSupported T⟩, htest, hfinite] with z hi ht' hf
  change testL2 T (chartMap z) = tensorFunction T.horizontal T.vertical (chartMap z) at ht'
  change finiteCoreL2 (Finset.univ : Finset (Fin 1)) (fun _ => heightMultiplyTensor T) z =
    finiteCoreFunction (Finset.univ : Finset (Fin 1)) (fun _ => heightMultiplyTensor T) z at hf
  rw [hi, ht', hf]
  simp only [finiteCoreFunction, Finset.univ_unique, Finset.sum_singleton]
  rw [heightMultiplyTensor_function, Complex.real_smul]
  rfl

end ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
