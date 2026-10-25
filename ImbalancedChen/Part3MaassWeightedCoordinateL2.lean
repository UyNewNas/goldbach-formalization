import ImbalancedChen.Part3CanonicalTensorHyperbolicLaplacianForm
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED, 2026-10-24.

This module supplies the concrete measure and norm transport needed for
the still-open finite-tensor density argument. The canonical hyperbolic
measure becomes a product of real Lebesgue measure and the weighted
positive-height measure. Multiplication by `y⁻¹`, followed by zero
extension, preserves squared L² distance exactly. No density hypothesis
or self-adjointness premise is introduced.

The pinned mathlib smooth-compact approximation theorem is documented
in the checkpoint, but no tensor-product density theorem is claimed.
-/

namespace ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z

def verticalWeight (y : ℝ) : ℝ≥0 :=
  ⟨(y⁻¹) ^ 2, sq_nonneg _⟩

theorem verticalWeight_measurable : Measurable verticalWeight := by
  unfold verticalWeight
  exact Measurable.subtype_mk (measurable_id.inv.pow_const 2)

/-- The positive-height measure `y⁻² dy`, as a measure on the full real
line supported in `y > 0`. -/
def verticalWeightedMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Set.Ioi 0)).withDensity
    (fun y => (verticalWeight y : ℝ≥0∞))

theorem upperChart_eq_product :
    upperChart = (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
  ext p
  simp [upperChart]

/-- Exact product-measure factorization of the chart hyperbolic measure. -/
theorem chartMeasure_eq_product :
    chartMeasure =
      (volume : Measure ℝ).prod verticalWeightedMeasure := by
  have hbase :
      (volume : Measure (ℝ × ℝ)).restrict upperChart =
        (volume : Measure ℝ).prod
          ((volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [upperChart_eq_product]
    change (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      ((Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ))) = _
    rw [← Measure.prod_restrict]
    simp
  unfold chartMeasure verticalWeightedMeasure
  rw [hbase, Measure.prod_withDensity_right]
  · rfl
  · exact verticalWeight_measurable.coe_nnreal_ennreal

/-- The canonical upper-half-plane integral equals the chart integral
for any real-valued coordinate integrand. This proof uses the actual
mathlib hyperbolic measure and both coordinate measure equivalences. -/
theorem canonical_real_integral_eq_chart (F : ℝ × ℝ → ℝ) :
    (∫ z : UpperHalfPlane,
      F (Complex.measurableEquivRealProd (z : ℂ))) =
        ∫ p : ℝ × ℝ, F p ∂chartMeasure := by
  let G : ℝ × ℝ → ℝ := fun p => chartWeight p • F p
  have hvol : (volume : Measure UpperHalfPlane) =
      ((volume : Measure ℂ).comap UpperHalfPlane.coe).withDensity
        (fun z => (upperDensityNN z : ℝ≥0∞)) :=
    UpperHalfPlane.volume_def
  rw [hvol, integral_withDensity_eq_integral_smul
    upperDensityNN_measurable]
  calc
    (∫ z : UpperHalfPlane,
        upperDensityNN z • F (Complex.measurableEquivRealProd (z : ℂ))
        ∂((volume : Measure ℂ).comap UpperHalfPlane.coe)) =
      ∫ z : UpperHalfPlane,
        G (Complex.measurableEquivRealProd (z : ℂ))
        ∂((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by
            simp only [G, upperDensityNN_eq_chartWeight]
    _ = ∫ z : ℂ, G (Complex.measurableEquivRealProd z)
          ∂(((volume : Measure ℂ).comap UpperHalfPlane.coe).map
            UpperHalfPlane.coe) := by
          exact (UpperHalfPlane.measurableEmbedding_coe.integral_map
            (μ := (volume : Measure ℂ).comap UpperHalfPlane.coe)
            (g := fun z : ℂ => G (Complex.measurableEquivRealProd z))).symm
    _ = ∫ z : ℂ in Set.range
          (UpperHalfPlane.coe : UpperHalfPlane → ℂ),
          G (Complex.measurableEquivRealProd z)
          ∂(volume : Measure ℂ) := by
          rw [UpperHalfPlane.measurableEmbedding_coe.map_comap
            (volume : Measure ℂ)]
    _ = ∫ p : ℝ × ℝ in upperChart, G p
          ∂(volume : Measure (ℝ × ℝ)) := by
          rw [range_upperHalfPlane_coe_eq_chart_preimage]
          exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
            Complex.measurableEquivRealProd.measurableEmbedding G upperChart
    _ = ∫ p : ℝ × ℝ, F p ∂chartMeasure := by
          unfold chartMeasure
          rw [integral_withDensity_eq_integral_smul
            chartWeight_measurable]
          rfl

/-- Zero extension and multiplication by `y⁻¹` on the chart. -/
def unweightChart (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if hp : p ∈ upperChart then (p.2⁻¹ : ℝ) • f p else 0

theorem unweightChart_sub (f g : ℝ × ℝ → ℂ) :
    unweightChart (fun p => f p - g p) =
      (fun p => unweightChart f p - unweightChart g p) := by
  funext p
  by_cases hp : p ∈ upperChart
  · simp [unweightChart, hp, smul_sub]
  · simp [unweightChart, hp]

/-- The weighted chart squared norm is exactly the ordinary planar
Lebesgue squared norm of the zero-extended `f/y`. -/
theorem chartL2_square_eq_unweight (f : ℝ × ℝ → ℂ) :
    (∫ p : ℝ × ℝ, ‖f p‖ ^ 2 ∂chartMeasure) =
      ∫ p : ℝ × ℝ, ‖unweightChart f p‖ ^ 2 := by
  unfold chartMeasure
  rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
  change (∫ p in upperChart,
      chartWeight p • ‖f p‖ ^ 2
      ∂(volume : Measure (ℝ × ℝ))) = _
  calc
    (∫ p in upperChart,
      chartWeight p • ‖f p‖ ^ 2
      ∂(volume : Measure (ℝ × ℝ))) =
        ∫ p in upperChart, ‖unweightChart f p‖ ^ 2
          ∂(volume : Measure (ℝ × ℝ)) := by
      apply setIntegral_congr_fun upperChart_measurable
      intro p hp
      change ((p.2⁻¹) ^ 2) * ‖f p‖ ^ 2 =
        ‖unweightChart f p‖ ^ 2
      simp only [unweightChart, dif_pos hp, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
    _ = ∫ p : ℝ × ℝ, ‖unweightChart f p‖ ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      simp [unweightChart, hp]

/-- Squared L² distance is preserved, without assuming integrability or
measurability as a premise. The integrals use mathlib's usual convention
outside the integrable class; the result applies in particular to L²
functions and supplies its norm identity. -/
theorem chartL2_distance_square_eq_unweight
    (f g : ℝ × ℝ → ℂ) :
    (∫ p : ℝ × ℝ, ‖f p - g p‖ ^ 2 ∂chartMeasure) =
      ∫ p : ℝ × ℝ,
        ‖unweightChart f p - unweightChart g p‖ ^ 2 := by
  simpa only [unweightChart_sub, Pi.sub_apply] using
    chartL2_square_eq_unweight (fun p => f p - g p)

/-- Restrict a function on the canonical upper half-plane to chart
coordinates, extended by zero to the nonpositive half-plane. -/
def chartPullback (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℂ :=
  if hp : p ∈ upperChart then F ⟨⟨p.1, p.2⟩, hp⟩ else 0

theorem chartPullback_at_upper (F : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) :
    chartPullback F (Complex.measurableEquivRealProd (z : ℂ)) = F z := by
  have hp : Complex.measurableEquivRealProd (z : ℂ) ∈ upperChart :=
    z.im_pos
  simp only [chartPullback, dif_pos hp]
  congr 1
  apply Subtype.ext
  simp [Complex.measurableEquivRealProd_apply]

/-- The canonical hyperbolic squared norm is the ordinary planar norm
of the zero-extended coordinate function divided by `y`. -/
theorem canonicalL2_square_eq_unweight (F : UpperHalfPlane → ℂ) :
    (∫ z : UpperHalfPlane, ‖F z‖ ^ 2) =
      ∫ p : ℝ × ℝ, ‖unweightChart (chartPullback F) p‖ ^ 2 := by
  calc
    (∫ z : UpperHalfPlane, ‖F z‖ ^ 2) =
      ∫ z : UpperHalfPlane,
        ‖chartPullback F
          (Complex.measurableEquivRealProd (z : ℂ))‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        rw [chartPullback_at_upper]
    _ = ∫ p : ℝ × ℝ,
          ‖chartPullback F p‖ ^ 2 ∂chartMeasure :=
      canonical_real_integral_eq_chart
        (fun p => ‖chartPullback F p‖ ^ 2)
    _ = ∫ p : ℝ × ℝ,
          ‖unweightChart (chartPullback F) p‖ ^ 2 :=
      chartL2_square_eq_unweight (chartPullback F)

theorem canonicalL2_distance_square_eq_unweight
    (F G : UpperHalfPlane → ℂ) :
    (∫ z : UpperHalfPlane, ‖F z - G z‖ ^ 2) =
      ∫ p : ℝ × ℝ,
        ‖unweightChart (chartPullback F) p -
          unweightChart (chartPullback G) p‖ ^ 2 := by
  have hpull : chartPullback (fun z => F z - G z) =
      (fun p => chartPullback F p - chartPullback G p) := by
    funext p
    by_cases hp : p ∈ upperChart
    · simp [chartPullback, hp]
    · simp [chartPullback, hp]
  simpa only [hpull, unweightChart_sub, Pi.sub_apply] using
    canonicalL2_square_eq_unweight (fun z => F z - G z)

/-- A pinned mathlib density endpoint on the unweighted full plane.
The missing step to finite compact tensors is the reduction of these
smooth planar approximants to finite separated-variable sums while
respecting positive-height support. -/
theorem planar_smooth_compact_dense :
    Dense {f : Lp ℂ (2 : ℝ≥0∞)
      (volume : Measure (ℝ × ℝ)) |
      ∃ g : ℝ × ℝ → ℂ,
        f =ᵐ[(volume : Measure (ℝ × ℝ))] g ∧
          HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  exact MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)

end

end ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
