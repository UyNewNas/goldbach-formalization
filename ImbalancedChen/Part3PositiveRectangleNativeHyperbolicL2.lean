import ImbalancedChen.Part3PositiveRectanglePhysicalRellich
import ImbalancedChen.Part3MaassWeightedCoordinateL2
import ImbalancedChen.Part3ActualModularSmoothCuspCutoff
import ImbalancedChen.Part3ActualGamma0MaassDescent

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual positive rectangle seed has compact support and belongs to
L2 of the CANONICAL UpperHalfPlane volume. Its native L2 distances equal
the physical weighted L2 distances exactly. This supplies the missing
native/physical local compactness bridge, without a norm-equivalence or
embedding premise. It does not identify a quotient form domain or prove
an all-cusps tail estimate.
-/

namespace ImbalancedChen.Part3.PositiveRectangleNativeHyperbolicL220261026b
noncomputable section
open Set MeasureTheory Filter Topology Metric
open scoped UpperHalfPlane
open PositiveRectangleAffineNormalization20261026b
open PositiveRectanglePhysicalRellich20261026b
open MaassWeightedCoordinateL220261024zz
open CanonicalTensorHyperbolicLaplacianForm20261024z
open Gamma0CompactTensorPoincareC2Core20261025a
open ActualGamma0MaassDescent20261025a
open ActualModularSmoothCuspCutoff20261025a

def nativeFunction {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ)
    (z : UpperHalfPlane) : ℂ := s.function (z.re,z.im)

theorem nativeFunction_continuous {R : Rectangle} {δ : ℝ} (s : RectangleSeed R δ) :
    Continuous (nativeFunction s) :=
  s.smooth.continuous.comp (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)

theorem nativeFunction_compact {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) : HasCompactSupport (nativeFunction s) := by
  have hc : ContinuousOn chartLift (region R δ) := by
    intro p hp
    exact (chartLift_continuousAt_positive
      (R.bottom_pos.trans_le (region_height hδ hp).1)).continuousWithinAt
  have hk : IsCompact (chartLift '' region R δ) := (region_isCompact R δ).image_of_continuousOn hc
  apply HasCompactSupport.of_support_subset_isCompact hk
  intro z hz
  exact ⟨(z.re,z.im), s.support_subset hz, chartLift_pair z⟩

theorem nativeFunction_memLp {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) : MemLp (nativeFunction s) 2 (volume : Measure UpperHalfPlane) :=
  (nativeFunction_continuous s).memLp_of_hasCompactSupport (nativeFunction_compact hδ s)

def nativeL2 {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ) (s : RectangleSeed R δ) :
    Lp ℂ 2 (volume : Measure UpperHalfPlane) :=
  (nativeFunction_memLp hδ s).toLp (nativeFunction s)

theorem unweight_nativeFunction {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) :
    unweightChart (chartPullback (nativeFunction s)) = weightedFunction s := by
  funext p
  by_cases hs : s.function p = 0
  · by_cases hp : p ∈ upperChart
    · simp only [unweightChart, chartPullback, dif_pos hp, nativeFunction,
        weightedFunction, hs, smul_zero, mul_zero]
    · simp only [unweightChart, dif_neg hp, weightedFunction, hs, mul_zero]
  · have hy := (region_height hδ (s.support_subset hs)).1
    have hp : p ∈ upperChart := R.bottom_pos.trans_le hy
    simp only [unweightChart, chartPullback, dif_pos hp, nativeFunction,
      weightedFunction, weight, max_eq_right hy, Complex.real_smul]

theorem nativeL2_square {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) :
    ‖nativeL2 hδ s‖^2 = ∫ z : UpperHalfPlane, ‖nativeFunction s z‖^2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (nativeL2 hδ s) (nativeL2 hδ s))]
  apply integral_congr_ae
  filter_upwards [(nativeFunction_memLp hδ s).coeFn_toLp] with z hz
  simp only [hz, inner_self_eq_norm_sq_to_K, Complex.ofReal_re]

/-- Exact native hyperbolic L2 mass; no unspecified local norm constant. -/
theorem nativeL2_norm {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s : RectangleSeed R δ) : ‖nativeL2 hδ s‖ = ‖weightedPhysical s‖ := by
  have hsquare : ‖nativeL2 hδ s‖^2 = ‖weightedPhysical s‖^2 := by
    rw [nativeL2_square, canonicalL2_square_eq_unweight, unweight_nativeFunction hδ,
      weightedPhysical_square]
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      simp only [weightedFunction, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, mul_pow, sq_abs])
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

theorem nativeL2_difference {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s t : RectangleSeed R δ) :
    nativeL2 hδ (difference s t) = nativeL2 hδ s - nativeL2 hδ t := by
  apply Lp.ext
  filter_upwards [(nativeFunction_memLp hδ s).coeFn_toLp,
    (nativeFunction_memLp hδ t).coeFn_toLp,
    (nativeFunction_memLp hδ (difference s t)).coeFn_toLp,
    Lp.coeFn_sub (nativeL2 hδ s) (nativeL2 hδ t)] with z hs ht hd hsub
  rw [hd, hsub, hs, ht]
  rfl

/-- The precise distance identity needed by finite actual-chart
reconstruction. The physical weight is the genuine native 1/y weight. -/
theorem nativeL2_distance {R : Rectangle} {δ : ℝ} (hδ : 0 ≤ δ)
    (s t : RectangleSeed R δ) :
    dist (nativeL2 hδ s) (nativeL2 hδ t) =
      dist (weightedPhysical s) (weightedPhysical t) := by
  simpa only [dist_eq_norm, nativeL2_difference hδ, weighted_difference] using
    nativeL2_norm hδ (difference s t)

/-- Genuine fixed-positive-rectangle native hyperbolic L2 compactness,
transported from the proved physical two-derivative energy ball. -/
theorem native_h1Ball_totallyBounded (R : Rectangle) {δ : ℝ} (hδ : 0 < δ)
    (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded (nativeL2 hδ.le '' h1Ball R δ A) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hTsub, hTfin, hTcover⟩ := Metric.finite_approx_of_totallyBounded
    (weighted_h1Ball_totallyBounded R hδ A hA) ε hε
  letI : Fintype T := hTfin.fintype
  let pick : T → RectangleSeed R δ := fun v => Classical.choose (hTsub v.2)
  have hpick (v : T) : pick v ∈ h1Ball R δ A ∧ weightedPhysical (pick v) = v :=
    Classical.choose_spec (hTsub v.2)
  refine ⟨range (fun v : T => nativeL2 hδ.le (pick v)), finite_range _, ?_⟩
  rintro u ⟨s, hs, rfl⟩
  obtain ⟨v, hv, hdist⟩ := mem_iUnion₂.mp (hTcover ⟨s, hs, rfl⟩)
  refine mem_iUnion₂.mpr ⟨nativeL2 hδ.le (pick ⟨v,hv⟩), ⟨⟨v,hv⟩, rfl⟩, ?_⟩
  rw [mem_ball, nativeL2_distance, (hpick ⟨v,hv⟩).2]
  exact hdist

end
end ImbalancedChen.Part3.PositiveRectangleNativeHyperbolicL220261026b
