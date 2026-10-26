import ImbalancedChen.Part3GammaNativeGraphCompactTranspose
import ImbalancedChen.Part3Gamma0WholeChartCoordinateWeakEquation
import ImbalancedChen.Part3CompactSeedSmoothPlaneExtension

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual native graph is characterized by literal ordinary-plane
compact smooth positive-chart distributional tests, with output weighted
by the ORIGINAL y^-2 coefficient. Both planar test products are proved L1
from actual compact H pairing integrability and exact density transport.
No adjoint/domain/form/H1/PDE premise is assumed in the reverse direction.
-/
namespace ImbalancedChen.Part3.GammaNativeGraphCoordinateTranspose20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0QuotientCellPushforward20261025a
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassFirstGradientWeakLimit20261025a
open CanonicalPlanarL2UnitarySourceOnly
open ActualPullbackLocalH1Transfer20261026b Gamma0WholeChartCoordinateWeakEquation20261026b
open Gamma0WholeSeedAdjointWeakEquation20261026b GammaNativeGraphCompactTranspose20261026b
open CompactSeedSmoothPlaneExtension20261025a ActualGamma0MaassDescent20261025a

/-- Genuine L1 transport for height-square lifts, not only equality of
possibly default-zero Bochner integrals. -/
theorem heightSquaredLift_integrable_iff (G : Plane → ℂ)
    (hzero : ∀ p ∉ upperChart, G p = 0) :
    Integrable (heightSquaredLift G) (volume : Measure UpperHalfPlane) ↔ Integrable G volume := by
  change Integrable (heightSquaredLift G)
    (coordinateMeasure.withDensity (fun z => (upperDensityNN z : ℝ≥0∞))) ↔ _
  rw [integrable_withDensity_iff_integrable_smul upperDensityNN_measurable]
  have hfun : (fun z : UpperHalfPlane => upperDensityNN z • heightSquaredLift G z) = G ∘ chartMap := by
    funext z
    rw [upperDensityNN_eq_chartWeight]
    simp only [heightSquaredLift,NNReal.smul_def,Complex.real_smul]
    change (((z.im⁻¹)^2 : ℝ) : ℂ) * ((z.im : ℂ)^2 * G (chartMap z)) = G (chartMap z)
    have hc : (((z.im⁻¹)^2 : ℝ) : ℂ) * (z.im : ℂ)^2 = 1 := by
      have hr : (z.im⁻¹)^2 * z.im^2 = (1 : ℝ) := by
        rw [← mul_pow,inv_mul_cancel₀ (ne_of_gt z.im_pos),one_pow]
      exact_mod_cast hr
    rw [← mul_assoc,hc,one_mul]
  rw [hfun]
  have hmap : Integrable G (Measure.map chartMap coordinateMeasure) ↔
      Integrable (G ∘ chartMap) coordinateMeasure := chartMap_measurableEmbedding.integrable_map_iff
  rw [map_coordinateMeasure] at hmap
  have hs : Function.support G ⊆ upperChart := by
    intro p hp
    by_contra hn
    exact hp (hzero p hn)
  exact hmap.symm.trans (integrableOn_iff_integrable_of_support_subset hs)

/-- Both ordinary test products have actual L1 meaning for ANY original
quotient L2 input/output, before the differential equation is imposed. -/
theorem coordinate_transpose_products_integrable (N : ℕ) [NeZero N] (f w : QuotientL2 N)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ upperChart) :
    Integrable (fun p => star (euclideanLaplacian ψ p) * actualPlanePullback N f p) volume ∧
    Integrable (fun p => star (ψ p) * coordinatePotential N w p) volume := by
  let L : Plane → ℂ := fun p => star (euclideanLaplacian ψ p) * actualPlanePullback N f p
  let M : Plane → ℂ := fun p => star (ψ p) * coordinatePotential N w p
  have hLzero : ∀ p ∉ upperChart, L p = 0 := by
    intro p hp
    simp [L,actualPlanePullback,hp]
  have hMzero : ∀ p ∉ upperChart, M p = 0 := by
    intro p hp
    simp [M,coordinatePotential,actualPlanePullback,hp]
  obtain ⟨ho,hi⟩ := compact_smooth_adjoint_products_integrable N (coordinateSeed ψ)
    (coordinateSeed_compact hc hs) (coordinateSeed_smooth hψ hs) f w
  have hLpoint (z : UpperHalfPlane) : heightSquaredLift L z =
      -(star (upperMaass (coordinateSeed ψ) z) * f (orbitProjection N z)) := by
    rw [coordinateSeed_maass hψ hs]
    simp only [heightSquaredLift,L,Complex.measurableEquivRealProd_apply,
      actualPlanePullback_at_upper,star_neg,star_mul,star_pow,Complex.star_def,Complex.conj_ofReal]
    ring
  have hMpoint (z : UpperHalfPlane) : heightSquaredLift M z =
      star (coordinateSeed ψ z) * w (orbitProjection N z) := by
    simp only [heightSquaredLift,M,Complex.measurableEquivRealProd_apply,coordinatePotential_at_upper,coordinateSeed]
    calc
      _ = star (ψ (z.re,z.im)) *
          (((z.im : ℂ)^2 * (((z.im⁻¹)^2 : ℝ) : ℂ)) * w (orbitProjection N z)) := by ring
      _ = _ := by rw [height_inverse_square_cancel,one_mul]
  exact ⟨(heightSquaredLift_integrable_iff L hLzero).mp
      (ho.neg.congr (Eventually.of_forall fun z => (hLpoint z).symm)),
    (heightSquaredLift_integrable_iff M hMzero).mp
      (hi.congr (Eventually.of_forall fun z => (hMpoint z).symm))⟩

def HasCoordinateMaassTranspose (N : ℕ) [NeZero N] (f w : QuotientL2 N) : Prop :=
  ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
    (∫ p, star (euclideanLaplacian ψ p) * actualPlanePullback N f p) =
      -(∫ p, star (ψ p) * coordinatePotential N w p)

/-- Exact equivalence of native compact H tests and ordinary compact
positive-plane tests. The negative Laplacian sign and y^-2 output are
retained, rather than replaced by a constant potential. -/
theorem compact_smooth_transpose_iff_coordinate (N : ℕ) [NeZero N] (f w : QuotientL2 N) :
    HasCompactSmoothTranspose N f w ↔ HasCoordinateMaassTranspose N f w := by
  constructor
  · intro h ψ hψ hc hs
    have ht := h (coordinateSeed ψ) (coordinateSeed_compact hc hs) (coordinateSeed_smooth hψ hs)
    rw [canonical_seed_output_eq_coordinate N f hψ hs,canonical_seed_mass_eq_coordinate N w ψ] at ht
    linear_combination -ht
  · intro h ψ hc hψ
    obtain ⟨hF,hFc,hFs⟩ := extendUpper_compact_cinfty_positive ψ hc hψ
    have ht := h (extendUpper ψ) hF hFc hFs
    have heq : coordinateSeed (extendUpper ψ) = ψ := by
      funext z
      exact extendUpper_pair ψ z
    have ho := canonical_seed_output_eq_coordinate N f hF hFs
    have hi := canonical_seed_mass_eq_coordinate N w (extendUpper ψ)
    rw [heq] at ho hi
    rw [ho,hi]
    linear_combination -ht

/-- Raw ordinary-coordinate characterization of the ACTUAL native closed
operator graph. The existence of global quotient L2 output is essential. -/
theorem actual_closed_graph_iff_coordinate_transpose (N : ℕ) [NeZero N] (f w : QuotientL2 N) :
    (f,w) ∈ (actualClosedGammaMaass N).graph ↔ HasCoordinateMaassTranspose N f w :=
  (actual_closed_graph_iff_compact_smooth_tests N f w).trans
    (compact_smooth_transpose_iff_coordinate N f w)

theorem actual_adjoint_graph_iff_coordinate_transpose (N : ℕ) [NeZero N] (f w : QuotientL2 N) :
    (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph ↔ HasCoordinateMaassTranspose N f w :=
  (actual_adjoint_graph_iff_compact_smooth_tests N f w).trans
    (compact_smooth_transpose_iff_coordinate N f w)

theorem actual_closed_domain_iff_coordinate_output (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ (actualClosedGammaMaass N).domain ↔ ∃ w : QuotientL2 N, HasCoordinateMaassTranspose N f w := by
  rw [actual_closed_domain_iff_compact_smooth_transpose]
  simp_rw [compact_smooth_transpose_iff_coordinate]

end
end ImbalancedChen.Part3.GammaNativeGraphCoordinateTranspose20261026b
