import ImbalancedChen.Part3Gamma0CompactInteriorTensorCover
import ImbalancedChen.Part3PositiveCompactTensorLpApproximation

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Genuine support-preserving LOCAL tensor approximation in the actual
reduced-carrier chart. The target has compact support in one of the actual
interior plateaux. An existing global planar tensor approximation is then
MULTIPLIED by the explicitly constructed interior separated cutoff. Its
support is proved to stay in one fixed compact rectangle wholly inside the
actual carrier. Multiplication preserves the genuine smooth tensor span
and does not enlarge the planar L2 error, since the cutoff has norm <=1.

Thus the unrestricted approximant's support is never assumed to be inside
the carrier. Global compact localization/weighted L2 transport and full
quotient density remain separate obligations.
-/

namespace ImbalancedChen.Part3.Gamma0LocalInteriorTensorApproximation20261025a

noncomputable section
open Set Metric MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0InteriorSmoothTensorBumps20261025a
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a

def localPositiveTensor (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) : SmoothPositiveTensor where
  horizontal := smallCoordinateBump z.re r hr
  vertical := smallCoordinateBump z.im r hr
  horizontal_smooth := (smallCoordinateBump z.re r hr).contDiff
  vertical_smooth := (smallCoordinateBump z.im r hr).contDiff
  horizontal_compact := (smallCoordinateBump z.re r hr).hasCompactSupport
  vertical_compact := (smallCoordinateBump z.im r hr).hasCompactSupport
  vertical_positive := by
    intro y hy
    have hdy := smallCoordinateBump_distance z.im r hr hy
    have hh : dist (z.re,y) (z.re,z.im)<r := by
      rw [Prod.dist_eq]
      simp only [dist_self,max_zero_left]
      exact hdy.trans_lt (by linarith)
    exact (hball (z.re,y) hh).1

def localSupportRectangle (z : UpperHalfPlane) (r : ℝ) : Set (ℝ×ℝ) :=
  closedBall z.re (r/2) ×ˢ closedBall z.im (r/2)

theorem localSupportRectangle_isCompact (z : UpperHalfPlane) (r : ℝ) :
    IsCompact (localSupportRectangle z r) := isCompact_closedBall.prod isCompact_closedBall

theorem localSupportRectangle_inside (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) :
    ∀ p∈localSupportRectangle z r,0<p.2 ∧ chartLift p∈reducedCarrier N := by
  intro p hp
  have hd : dist p (z.re,z.im)<r := by
    rw [Prod.dist_eq]
    exact (max_le hp.1 hp.2).trans_lt (by linarith)
  exact hball p hd

theorem localPositiveTensor_tsupport_subset (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) :
    tsupport (planeTensor (localPositiveTensor N z r hr hball))⊆localSupportRectangle z r := by
  apply closure_minimal _ (isClosed_closedBall.prod isClosed_closedBall)
  intro p hp
  have hx : p.1∈tsupport (smallCoordinateBump z.re r hr) := by
    by_contra hh
    exact hp (by simp [planeTensor,localPositiveTensor,image_eq_zero_of_notMem_tsupport hh])
  have hy : p.2∈tsupport (smallCoordinateBump z.im r hr) := by
    by_contra hh
    exact hp (by simp [planeTensor,localPositiveTensor,image_eq_zero_of_notMem_tsupport hh])
  exact ⟨smallCoordinateBump_distance z.re r hr hx,
    smallCoordinateBump_distance z.im r hr hy⟩

theorem localPositiveTensor_norm_le_one (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) (p : ℝ×ℝ) :
    ‖planeTensor (localPositiveTensor N z r hr hball) p‖≤1 := by
  simp only [planeTensor,localPositiveTensor,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (smallCoordinateBump z.re r hr).nonneg
    (smallCoordinateBump z.im r hr).nonneg)]
  nlinarith [(smallCoordinateBump z.re r hr).nonneg (x:=p.1),
    (smallCoordinateBump z.re r hr).le_one (x:=p.1),
    (smallCoordinateBump z.im r hr).nonneg (x:=p.2),
    (smallCoordinateBump z.im r hr).le_one (x:=p.2)]

theorem localPositiveTensor_one_on_innerBall (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N)
    (p : ℝ×ℝ) (hp : p∈Metric.ball (z.re,z.im) (r/4)) :
    planeTensor (localPositiveTensor N z r hr hball) p=1 := by
  have hh : max (dist p.1 z.re) (dist p.2 z.im)<r/4 := by
    simpa only [Metric.mem_ball,Prod.dist_eq] using hp
  have hx : smallCoordinateBump z.re r hr p.1=1 := by
    apply (smallCoordinateBump z.re r hr).one_of_mem_closedBall
    exact (le_max_left _ _).trans hh.le
  have hy : smallCoordinateBump z.im r hr p.2=1 := by
    apply (smallCoordinateBump z.im r hr).one_of_mem_closedBall
    exact (le_max_right _ _).trans hh.le
  simp only [planeTensor,localPositiveTensor,hx,hy,one_mul,Complex.ofReal_one]

/-- Actual local interior approximation with a common compact support
rectangle. Both the support and the small error are conclusions. -/
theorem exists_local_interior_tensor_L2_approx
    (N : ℕ) [NeZero N] (z : UpperHalfPlane) (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N)
    (F : (ℝ×ℝ)→ℂ) (hFcont : Continuous F) (hFc : HasCompactSupport F)
    (hFsupp : tsupport F⊆Metric.ball (z.re,z.im) (r/4))
    (epsilon : ℝ≥0∞) (hepsilon : 0<epsilon) :
    ∃ H∈planeTensorSpan,
      tsupport H⊆localSupportRectangle z r ∧
      (∀ p∈tsupport H,0<p.2 ∧ chartLift p∈reducedCarrier N) ∧
      eLpNorm (F-H) 2 volume<epsilon := by
  have hFpos : tsupport F⊆upperChart := by
    intro p hp
    exact (hball p ((hFsupp hp).trans (by linarith))).1
  obtain ⟨G,hG,herr⟩ := exists_plane_tensor_L2_approx F hFcont hFc hFpos epsilon hepsilon.ne'
  let B := planeTensor (localPositiveTensor N z r hr hball)
  let H := B*G
  have hH : H∈planeTensorSpan := tensor_mul_span_mem _ hG
  have hHsupport : tsupport H⊆localSupportRectangle z r :=
    tsupport_mul_subset_left.trans (localPositiveTensor_tsupport_subset N z r hr hball)
  have hBF : B*F=F := by
    funext p
    by_cases hp : F p=0
    · simp only [Pi.mul_apply,hp,mul_zero]
    · have hin : p∈Metric.ball (z.re,z.im) (r/4) := hFsupp (subset_tsupport _ hp)
      have hone := localPositiveTensor_one_on_innerBall N z r hr hball p hin
      simp only [Pi.mul_apply,B,hone,one_mul]
  refine ⟨H,hH,hHsupport,?_,?_⟩
  · intro p hp
    exact localSupportRectangle_inside N z r hr hball p (hHsupport hp)
  · have heq : F-H=B*(F-G) := by
      rw [mul_sub,hBF]
      rfl
    rw [heq]
    apply (eLpNorm_mono (fun p => ?_)).trans_lt herr
    rw [Pi.mul_apply,norm_mul]
    exact (mul_le_mul_of_nonneg_right (localPositiveTensor_norm_le_one N z r hr hball p)
      (norm_nonneg _)).trans_eq (one_mul _)

end
end ImbalancedChen.Part3.Gamma0LocalInteriorTensorApproximation20261025a
