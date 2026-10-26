import ImbalancedChen.Part3GammaCompletedPhysicalLocalH1
import ImbalancedChen.Part3Gamma0FriedrichsKernelZeroWeakGradient

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
The genuine compact native completed gradient supplies BOTH ordinary
planar weak partials of the actual physical J pullback. Their full planar
L2 norm squares sum EXACTLY to the native vector gradient norm square.
Canonical y^-2 volume and division by height cancel without an assumed
norm-equivalence constant. Thus the ORIGINAL unshifted closed quotient
form bounds the two weak partials and every compact-band horizontal mass. -/

namespace ImbalancedChen.Part3.GammaCompletedPlanarGradientBudget20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0CompactCoreGradient20261025a
open Gamma0EnergyCompactGradientExtension20261025a
open Gamma0EnergyGeometricWeakGradient20261025a
open Gamma0FriedrichsKernelZeroWeakGradient20261025a
open Gamma0CompactGlobalOverlap20261025a
open GammaCompletedGradientClassicalRepresentative20261026b
open GammaCompletedPhysicalLocalH120261026b
open MaassWeightedCoordinateL220261024zz
open CanonicalPlanarL2UnitarySourceOnly
open CompactC2ProductMollifier20261026a

def physicalPartialL2 (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N) : Lp ℂ 2 (volume : Measure Plane) :=
  (planarCompletedPartial_memLp N hK vertical e).toLp (planarCompletedPartial N hK vertical e)

private theorem l2_square_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : Lp ℂ 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_re])

/-- The scalar weak coordinate field's exact ordinary planar norm. -/
theorem physicalPartialL2_norm_sq (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (vertical : Bool) (e : EnergyCompletion N) :
    ‖physicalPartialL2 N hK vertical e‖^2 =
      ∫ z in K, ‖(completedCompactGradient N hK e) z (firstCoordinate vertical)‖^2 := by
  rw [l2_square_integral]
  have he : (∫ p : Plane, ‖physicalPartialL2 N hK vertical e p‖^2) =
      ∫ p : Plane, ‖planarCompletedPartial N hK vertical e p‖^2 := by
    apply integral_congr_ae
    filter_upwards [(planarCompletedPartial_memLp N hK vertical e).coeFn_toLp] with p hp
    rw [hp]
  rw [he]
  have hcanonical := canonicalL2_square_eq_unweight
    (K.indicator (fun z => (completedCompactGradient N hK e) z (firstCoordinate vertical)))
  change (∫ p : Plane, ‖forwardFunction (K.indicator
    (fun z => (completedCompactGradient N hK e) z (firstCoordinate vertical))) p‖^2) = _
  rw [← hcanonical]
  have hi : (fun z : UpperHalfPlane => ‖K.indicator
      (fun w => (completedCompactGradient N hK e) w (firstCoordinate vertical)) z‖^2) =
      K.indicator (fun z => ‖(completedCompactGradient N hK e) z (firstCoordinate vertical)‖^2) := by
    funext z
    by_cases hz : z ∈ K <;> simp [hz]
  rw [hi,integral_indicator hK.measurableSet]

/-- Both physical weak partials cost precisely the one native vector
gradient, rather than twice its norm or a fabricated coordinate energy. -/
theorem physicalPartials_sum_norm_sq (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (e : EnergyCompletion N) :
    ‖physicalPartialL2 N hK false e‖^2 + ‖physicalPartialL2 N hK true e‖^2 =
      ‖completedCompactGradient N hK e‖^2 := by
  have hi (j : Fin 2) : Integrable (fun z : UpperHalfPlane =>
      ‖(completedCompactGradient N hK e) z j‖^2) ((volume : Measure UpperHalfPlane).restrict K) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) j).comp_memLp (completedCompactGradient N hK e)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  rw [physicalPartialL2_norm_sq,physicalPartialL2_norm_sq]
  change (∫ z in K, ‖(completedCompactGradient N hK e) z 0‖^2) +
    (∫ z in K, ‖(completedCompactGradient N hK e) z 1‖^2) = _
  rw [← integral_add (hi 0) (hi 1)]
  have hnorm : ‖completedCompactGradient N hK e‖^2 =
      ∫ z in K, ‖completedCompactGradient N hK e z‖^2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
      ← integral_re (L2.integrable_inner (completedCompactGradient N hK e)
        (completedCompactGradient N hK e))]
    simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_re]
  rw [hnorm]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two])

/-- Actual unshifted form energy controls the ordinary coordinate weak
derivatives of an arbitrary completed vector; no smooth VALUE assumed. -/
theorem physicalPartials_sum_Dirichlet_budget (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    ‖physicalPartialL2 N hK false e‖^2 + ‖physicalPartialL2 N hK true e‖^2 ≤
      (compactOverlapBound N K : ℝ)*(actualDirichletPair N e e).re := by
  rw [physicalPartials_sum_norm_sq]
  exact completedCompactGradient_sharp_Dirichlet_bound N hK e

theorem physical_horizontal_band_Dirichlet_budget (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) (B : Set Plane) :
    (∫ p in B, ‖physicalPartialL2 N hK false e p‖^2) ≤
      (compactOverlapBound N K : ℝ)*(actualDirichletPair N e e).re := by
  have hi := (physicalPartialL2 N hK false e).memLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hlocal := integral_mono_measure (Measure.restrict_le_self (s := B))
    (Eventually.of_forall (fun p => sq_nonneg ‖physicalPartialL2 N hK false e p‖)) hi
  rw [← l2_square_integral] at hlocal
  exact hlocal.trans ((le_add_of_nonneg_right (sq_nonneg ‖physicalPartialL2 N hK true e‖)).trans
    (physicalPartials_sum_Dirichlet_budget N hK e))

end
end ImbalancedChen.Part3.GammaCompletedPlanarGradientBudget20261026b
