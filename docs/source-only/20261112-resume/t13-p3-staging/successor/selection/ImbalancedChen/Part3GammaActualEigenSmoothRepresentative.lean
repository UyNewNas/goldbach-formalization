import ImbalancedChen.Part3GammaContinuousRawRepresentative
import ImbalancedChen.Part3ClassicalRepresentativeWeakEigenPDE
import ImbalancedChen.Part3ActualEigenAllWeakJets
import ImbalancedChen.Part3UpperChartWeakJetClassicalRepresentative

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
ACTUAL native Maass eigenvectors have SAME-AE smooth representatives.
All weak orders are derived from the native eigen graph, then genuine
compact weak Fourier transport, Sobolev reconstruction and classical AE
patching produce one C-infinity representative. Value AE and continuity
give EXACT Gamma0 invariance. Native C2 slice/Frechet identification and
the genuine distribution equation give the literal upperMaass equation.
No smoothness, higher weak jet or classical eigenfunction is assumed.
-/

namespace ImbalancedChen.Part3.GammaActualEigenSmoothRepresentative20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a
open MaassWeakOperatorCore20261024zz Gamma0CompactGreenProductL120261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open Gamma0WholeChartCoordinateWeakEquation20261026b ActualPoincareMaassLocalFinite20261025a
open GammaContinuousRawRepresentative20261026b ClassicalRepresentativeWeakEigenPDE20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z
open ActualPullbackLocalH1Transfer20261026b ActualEigenAllWeakJets20261026b
open UpperChartWeakJetClassicalRepresentative20261026b

theorem positive_C2_laplacian_eq_slices (F : Plane → ℂ)
    (hF : ContDiffOn ℝ 2 F upperChart) (p : Plane) (hp : p ∈ upperChart) :
    euclideanLaplacian F p =
      deriv (deriv (fun t : ℝ => F (t,p.2))) p.1 +
        deriv (deriv (fun t : ℝ => F (p.1,t))) p.2 := by
  have hdF := hF.differentiableOn (by norm_num)
  have hD (v : Plane) : ContDiffOn ℝ 1 (directional v F) upperChart := by
    have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) upperChart :=
      hF.fderiv_of_isOpen positiveChart_isOpen (by norm_num)
    exact hDF.clm_apply contDiffOn_const
  have hfunx : deriv (fun t : ℝ => F (t,p.2)) =
      fun t => directional xDirection F (t,p.2) := by
    funext t
    exact sliceDx_eq_fderiv F hdF hp
  have hfuny : deriv (fun t : ℝ => F (p.1,t)) =ᶠ[𝓝 p.2]
      fun t => directional yDirection F (p.1,t) := by
    filter_upwards [Ioi_mem_nhds hp] with t ht
    exact sliceDy_eq_fderiv F hdF ht
  have hx : deriv (deriv (fun t : ℝ => F (t,p.2))) p.1 =
      directional xDirection (directional xDirection F) p := by
    rw [hfunx]
    exact sliceDx_eq_fderiv (directional xDirection F)
      ((hD xDirection).differentiableOn (by norm_num)) hp
  have hy : deriv (deriv (fun t : ℝ => F (p.1,t))) p.2 =
      directional yDirection (directional yDirection F) p := by
    rw [hfuny.deriv_eq]
    exact sliceDy_eq_fderiv (directional yDirection F)
      ((hD yDirection).differentiableOn (by norm_num)) hp
  rw [hx,hy]

theorem upperMaass_coordinate_C2 (F : Plane → ℂ)
    (hF : ContDiffOn ℝ 2 F upperChart) (z : UpperHalfPlane) :
    upperMaass (coordinateSeed F) z =
      -((z.im : ℂ)^2*euclideanLaplacian F (z.re,z.im)) := by
  have hlocal : extendUpper (coordinateSeed F) =ᶠ[𝓝 (z.re,z.im)] F := by
    filter_upwards [positiveChart_isOpen.mem_nhds z.im_pos] with p hp
    simp only [extendUpper,coordinateSeed,dif_pos hp]
  have hMaass := chartMaass_eq_of_eventuallyEq hlocal
  change chartMaass (extendUpper (coordinateSeed F)) (z.re,z.im) = _
  rw [hMaass]
  unfold chartMaass
  rw [positive_C2_laplacian_eq_slices F hF (z.re,z.im) z.im_pos]

/-- Native function-level eigen-equation once the SAME-AE C2 value has
been genuinely obtained from the bootstrap, not as an eigen input. -/
theorem derived_C2_representative_upperMaass (N : ℕ) [NeZero N]
    (lambda : ℝ) (f : QuotientL2 N)
    (hEigen : (f,(lambda : ℂ) • f) ∈ (actualClosedGammaMaass N).graph)
    (F : Plane → ℂ) (hF : ContDiffOn ℝ 2 F upperChart)
    (hrep : F =ᵐ[(volume : Measure Plane).restrict upperChart]
      ActualPullbackLocalH1Transfer20261026b.actualPlanePullback N f) :
    ∀ z : UpperHalfPlane, upperMaass (coordinateSeed F) z = (lambda : ℂ)*coordinateSeed F z := by
  intro z
  rw [upperMaass_coordinate_C2 F hF z]
  exact actual_eigen_C2_representative_Maass_equation N lambda f hEigen F hF hrep
    (z.re,z.im) z.im_pos

/-- ACTUAL native eigenvectors have a SAME-AE smooth ordinary-coordinate
representative, with exact Gamma0 invariance and the original classical
Maass equation. No weak jet, smoothness, representative or PDE is assumed. -/
theorem actual_native_eigen_has_smooth_coordinate_representative (N : ℕ) [NeZero N]
    (lambda : ℝ) (f : QuotientL2 N)
    (hEigen : (f,(lambda : ℂ) • f) ∈ (actualClosedGammaMaass N).graph) :
    ∃ F : Plane → ℂ, ContDiffOn ℝ ∞ F upperChart ∧
      (F =ᵐ[(volume : Measure Plane).restrict upperChart] actualPlanePullback N f) ∧
      GammaSmoothMultiplierPeriodization20261026a.IsGammaInvariant N (coordinateSeed F) ∧
      (∀ p ∈ upperChart, -((p.2 : ℂ)^2*euclideanLaplacian F p) = (lambda : ℂ)*F p) := by
  obtain ⟨F,hF,hraw⟩ := upperChart_all_weakJets_smooth_representative
    (actualPlanePullback N f) (actual_native_eigen_all_weak_jets N lambda f hEigen)
  have hrep : F =ᵐ[(volume : Measure Plane).restrict upperChart] actualPlanePullback N f := hraw.symm
  refine ⟨F,hF,hrep,coordinate_classical_representative_gamma0_invariant N f F hF.continuousOn hrep,?_⟩
  exact actual_eigen_C2_representative_Maass_equation N lambda f hEigen F
    (hF.of_le (by simp)) hrep

/-- The SAME representative is a smooth Gamma0-invariant function on
actual H, agrees canonically AE with f, and solves the EXISTING literal
function-level upperMaass equation at every point. -/
theorem actual_native_eigen_has_smooth_upper_representative (N : ℕ) [NeZero N]
    (lambda : ℝ) (f : QuotientL2 N)
    (hEigen : (f,(lambda : ℂ) • f) ∈ (actualClosedGammaMaass N).graph) :
    ∃ Phi : UpperHalfPlane → ℂ, ContDiffOn ℝ ∞ (extendUpper Phi) upperChart ∧
      (Phi =ᵐ[(volume : Measure UpperHalfPlane)] fun z => f (Gamma0QuotientCellPushforward20261025a.orbitProjection N z)) ∧
      GammaSmoothMultiplierPeriodization20261026a.IsGammaInvariant N Phi ∧
      (∀ z : UpperHalfPlane, upperMaass Phi z = (lambda : ℂ)*Phi z) := by
  obtain ⟨F,hF,hrep,hGamma,hPDE⟩ := actual_native_eigen_has_smooth_coordinate_representative N lambda f hEigen
  refine ⟨coordinateSeed F,coordinate_representative_extend_contDiff F ∞ hF,
    coordinate_representative_ae_upper N f F hrep,hGamma,?_⟩
  exact derived_C2_representative_upperMaass N lambda f hEigen F (hF.of_le (by simp)) hrep

end
end ImbalancedChen.Part3.GammaActualEigenSmoothRepresentative20261026b
