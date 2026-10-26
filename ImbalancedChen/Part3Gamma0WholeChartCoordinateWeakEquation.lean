import ImbalancedChen.Part3Gamma0WholeSeedAdjointWeakEquation
import ImbalancedChen.Part3ActualPullbackLocalH1Transfer
import ImbalancedChen.Part3MaassFirstGradientWeakLimit
import ImbalancedChen.Part3Gamma0CompactUpperChartExtension

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The whole-H actual adjoint identity becomes a literal ordinary planar
distribution equation against every compact smooth positive-height test.
The test is lifted to a genuinely compact H seed; the canonical y^-2
density is cancelled explicitly. The resulting mass is y^-2 times the
original orbit pullback, not a constant-potential replacement.
-/

namespace ImbalancedChen.Part3.Gamma0WholeChartCoordinateWeakEquation20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane ContDiff Topology
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0SmoothCompactTensorCore20261025a Gamma0CompactUpperChartExtension20261025a
open ProductConvolutionSecondDerivatives20261026a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualMinimalShiftRange20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0WholeSeedAdjointWeakEquation20261026b ActualPullbackLocalH1Transfer20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassFirstGradientWeakLimit20261025a

def coordinateSeed (ψ : Plane → ℂ) (z : UpperHalfPlane) : ℂ := ψ (z.re,z.im)

theorem coordinateSeed_extension {ψ : Plane → ℂ}
    (hs : tsupport ψ ⊆ upperChart) : extendUpper (coordinateSeed ψ) = ψ := by
  funext p
  by_cases hp : 0 < p.2
  · simp [extendUpper, coordinateSeed, hp]
  · have hz : ψ p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hs h))
    simp [extendUpper, hp, hz]

/-- Compactness uses the inverse chart only on the positive compact
support; no globally continuous extension of ofComplex is asserted. -/
theorem coordinateSeed_compact {ψ : Plane → ℂ} (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperChart) : HasCompactSupport (coordinateSeed ψ) := by
  have hcont : ContinuousOn chartLift (tsupport ψ) := by
    intro p hp
    exact ((UpperHalfPlane.contMDiffAt_ofComplex (n := 2) (hs hp)).continuousAt.comp
      complexOfPair_contDiff_infty.continuous.continuousAt).continuousWithinAt
  apply HasCompactSupport.of_support_subset_isCompact (hc.image_of_continuousOn hcont)
  intro z hz
  refine ⟨(z.re,z.im), subset_tsupport _ hz, ?_⟩
  exact chartLift_coordinates z

theorem coordinateSeed_smooth {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ upperChart) :
    ContDiffOn ℝ ∞ (extendUpper (coordinateSeed ψ)) positiveChart := by
  rw [coordinateSeed_extension hs]
  exact hψ.contDiffOn

theorem coordinateSeed_maass {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ upperChart) (z : UpperHalfPlane) :
    upperMaass (coordinateSeed ψ) z =
      -((z.im : ℂ)^2 * euclideanLaplacian ψ (z.re,z.im)) := by
  unfold upperMaass
  rw [coordinateSeed_extension hs]
  rw [euclideanLaplacian_eq_slice hψ]
  rfl

def coordinatePotential (N : ℕ) (f : QuotientL2 N) (p : Plane) : ℂ :=
  (((p.2⁻¹)^2 : ℝ) : ℂ) * actualPlanePullback N f p

theorem coordinatePotential_at_upper (N : ℕ) (f : QuotientL2 N) (z : UpperHalfPlane) :
    coordinatePotential N f (z.re,z.im) =
      (((z.im⁻¹)^2 : ℝ) : ℂ) * f (orbitProjection N z) := by
  rw [coordinatePotential]
  exact congrArg (fun c : ℂ => (((z.im⁻¹)^2 : ℝ) : ℂ) * c)
    (actualPlanePullback_at_upper N f z)

theorem height_inverse_square_cancel (z : UpperHalfPlane) :
    (z.im : ℂ)^2 * (((z.im⁻¹)^2 : ℝ) : ℂ) = 1 := by
  have hr : z.im^2 * (z.im⁻¹)^2 = (1 : ℝ) := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt z.im_pos), one_pow]
  exact_mod_cast hr

/-- The original mass integral in canonical hyperbolic volume is exactly
the ordinary planar inverse-square-potential pairing. -/
theorem canonical_seed_mass_eq_coordinate (N : ℕ) (f : QuotientL2 N)
    (ψ : Plane → ℂ) :
    (∫ z : UpperHalfPlane, star (coordinateSeed ψ z) * f (orbitProjection N z)) =
      ∫ p : Plane, star (ψ p) * coordinatePotential N f p := by
  have hzero : ∀ p ∉ upperChart, coordinatePotential N f p = 0 := by
    intro p hp
    simp [coordinatePotential, actualPlanePullback, hp]
  rw [← canonical_heightSquared_pairing ψ (coordinatePotential N f) hzero]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [heightSquaredLift, Complex.measurableEquivRealProd_apply,
      coordinatePotential_at_upper, coordinateSeed]
    calc
      _ = star (ψ (z.re,z.im)) *
          (((z.im : ℂ)^2 * (((z.im⁻¹)^2 : ℝ) : ℂ)) * f (orbitProjection N z)) := by
        rw [height_inverse_square_cancel, one_mul]
      _ = _ := by ring

/-- The actual Maass output pairing gives the negative ordinary planar
Laplacian pairing. The height-square coefficient is retained until it
cancels against the canonical measure. -/
theorem canonical_seed_output_eq_coordinate (N : ℕ) (f : QuotientL2 N)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ upperChart) :
    (∫ z : UpperHalfPlane, star (upperMaass (coordinateSeed ψ) z) *
      f (orbitProjection N z)) =
        -(∫ p : Plane, star (euclideanLaplacian ψ p) * actualPlanePullback N f p) := by
  have hzero : ∀ p ∉ upperChart, actualPlanePullback N f p = 0 := by
    intro p hp
    simp [actualPlanePullback, hp]
  rw [← canonical_heightSquared_pairing (euclideanLaplacian ψ)
    (actualPlanePullback N f) hzero, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    rw [coordinateSeed_maass hψ hs]
    simp only [heightSquaredLift, Complex.measurableEquivRealProd_apply,
      actualPlanePullback_at_upper, star_neg, star_mul, star_pow,
      Complex.star_def, Complex.conj_ofReal]
    ring

/-- Genuine ordinary-coordinate transpose for the actual adjoint defect.
There is no local carrier, H1, equation or gradient premise. -/
theorem actual_defect_coordinate_transpose (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperChart) :
    (∫ p : Plane, star (euclideanLaplacian ψ p) * actualPlanePullback N f p) =
      ∫ p : Plane, star (ψ p) * coordinatePotential N f p := by
  have hseedc := coordinateSeed_compact hc hs
  have hseeds := coordinateSeed_smooth hψ hs
  have hraw := actual_defect_compact_smooth_weak N f hf (coordinateSeed ψ) hseedc hseeds
  obtain ⟨ho, hi⟩ := compact_smooth_adjoint_products_integrable N
    (coordinateSeed ψ) hseedc hseeds f f
  simp_rw [star_add, add_mul] at hraw
  rw [integral_add ho hi, canonical_seed_output_eq_coordinate N f hψ hs,
    canonical_seed_mass_eq_coordinate N f ψ] at hraw
  have hsub : (∫ p : Plane, star (ψ p) * coordinatePotential N f p) -
      (∫ p : Plane, star (euclideanLaplacian ψ p) * actualPlanePullback N f p) = 0 := by
    simpa only [sub_eq_add_neg, add_comm] using hraw
  exact (sub_eq_zero.mp hsub).symm

end
end ImbalancedChen.Part3.Gamma0WholeChartCoordinateWeakEquation20261026b
