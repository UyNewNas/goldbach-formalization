import ImbalancedChen.Part3Gamma0ReducedSeedReconstruction
import ImbalancedChen.Part3Gamma0SmoothCompactTensorCore
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual support-localized smooth tensor seeds inside the genuine open
reduced Gamma0 carrier. At every actual reduced representative this
constructs a separated C-infinity compact positive-height tensor, equal
to one at that point, whose ENTIRE compact support rectangle stays inside
the actual reduced carrier. Its actual Poincare value therefore also
equals one there, by the reconstruction theorem.

This supplies localized seeds for open-domain approximation; it does not
claim that unrestricted whole-plane approximants retain this support, or
that the resulting family is already proved quotient dense.
-/

namespace ImbalancedChen.Part3.Gamma0InteriorSmoothTensorBumps20261025a

noncomputable section
open Set Filter Topology Metric
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ReducedSeedReconstruction20261025a

def smallCoordinateBump (c r : ℝ) (hr : 0<r) : ContDiffBump c where
  rIn := r/4
  rOut := r/2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem smallCoordinateBump_distance (c r : ℝ) (hr : 0<r)
    {x : ℝ} (hx : x∈tsupport (smallCoordinateBump c r hr)) :
    dist x c≤r/2 := by
  rw [(smallCoordinateBump c r hr).tsupport_eq,Metric.mem_closedBall] at hx
  exact hx

theorem smallCoordinateBump_center (c r : ℝ) (hr : 0<r) :
    smallCoordinateBump c r hr c=1 := by
  apply (smallCoordinateBump c r hr).one_of_mem_closedBall
  simp only [Metric.mem_closedBall,dist_self]
  change (0:ℝ)≤r/4
  positivity

private theorem positive_chartLift_continuousAt {p : ℝ×ℝ} (hp : 0<p.2) :
    ContinuousAt chartLift p :=
  (UpperHalfPlane.contMDiffAt_ofComplex (n:=2) hp).continuousAt.comp
    complexOfPair_contDiff_infty.continuous.continuousAt

/-- Actual reduced representatives have a positive coordinate ball
whose every point still represents a point inside the actual carrier. -/
theorem exists_positive_coordinate_ball (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) (hz : z∈reducedCarrier N) :
    ∃ r : ℝ,0<r ∧ ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N := by
  have hp : 0<(z.re,z.im).2 := z.im_pos
  have heq : chartLift (z.re,z.im)=z := by
    rw [chartLift_of_positive hp]
    apply UpperHalfPlane.ext
    ext <;> rfl
  have hred : chartLift ⁻¹' reducedCarrier N∈𝓝 (z.re,z.im) := by
    apply (positive_chartLift_continuousAt hp).preimage_mem_nhds
    rw [heq]
    exact (reducedCarrier_isOpen N).mem_nhds hz
  have hpos : {p : ℝ×ℝ | 0<p.2}∈𝓝 (z.re,z.im) :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds hp
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hpos hred)
  exact ⟨r,hr,fun p hpball => hball hpball⟩

/-- A literal C-infinity separated seed built from two one-dimensional
bumps, with vertical positivity derived from the actual coordinate ball. -/
def interiorTensor (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) : SmoothCompactTensor where
  horizontal := Complex.ofRealCLM ∘ smallCoordinateBump z.re r hr
  vertical := Complex.ofRealCLM ∘ smallCoordinateBump z.im r hr
  horizontal_smooth :=
    (Complex.ofRealCLM.contDiff.comp (smallCoordinateBump z.re r hr).contDiff).of_le (by simp)
  vertical_smooth :=
    (Complex.ofRealCLM.contDiff.comp (smallCoordinateBump z.im r hr).contDiff).of_le (by simp)
  horizontal_compact := (smallCoordinateBump z.re r hr).hasCompactSupport.comp_left rfl
  vertical_compact := (smallCoordinateBump z.im r hr).hasCompactSupport.comp_left rfl
  vertical_positive := by
    apply (tsupport_comp_subset rfl _).trans
    intro y hy
    have hdy := smallCoordinateBump_distance z.im r hr hy
    have hdist : dist (z.re,y) (z.re,z.im)<r := by
      rw [Prod.dist_eq]
      simp only [dist_self,max_zero_left]
      exact hdy.trans_lt (by linarith)
    exact (hball (z.re,y) hdist).1
  horizontal_cinfty := Complex.ofRealCLM.contDiff.comp (smallCoordinateBump z.re r hr).contDiff
  vertical_cinfty := Complex.ofRealCLM.contDiff.comp (smallCoordinateBump z.im r hr).contDiff

/-- The entire compact positive-coordinate rectangle is confined to the
ACTUAL carrier; this support condition is proved, never assumed of an
unrestricted whole-plane tensor approximant. -/
theorem interiorTensor_supportK_subset (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) :
    compactTensorSupportK (interiorTensor N z r hr hball).toCompactTensor⊆reducedCarrier N := by
  intro w hw
  have hx : w.re∈tsupport (smallCoordinateBump z.re r hr) :=
    tsupport_comp_subset rfl _ hw.1
  have hy : w.im∈tsupport (smallCoordinateBump z.im r hr) :=
    tsupport_comp_subset rfl _ hw.2
  have hdx := smallCoordinateBump_distance z.re r hr hx
  have hdy := smallCoordinateBump_distance z.im r hr hy
  have hdist : dist (w.re,w.im) (z.re,z.im)<r := by
    rw [Prod.dist_eq]
    exact (max_le hdx hdy).trans_lt (by linarith)
  have hh := (hball (w.re,w.im) hdist).2
  have heq : chartLift (w.re,w.im)=w := by
    rw [chartLift_of_positive w.im_pos]
    apply UpperHalfPlane.ext
    ext <;> rfl
  simpa only [heq] using hh

theorem interiorTensor_value_at_center (N : ℕ) [NeZero N] (z : UpperHalfPlane)
    (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) :
    tensorFunctionH (interiorTensor N z r hr hball).horizontal
      (interiorTensor N z r hr hball).vertical z=1 := by
  rw [tensorFunctionH_eq]
  change ((smallCoordinateBump z.re r hr z.re:ℝ):ℂ)*
    ((smallCoordinateBump z.im r hr z.im:ℝ):ℂ)=1
  rw [smallCoordinateBump_center,smallCoordinateBump_center]
  norm_num

/-- A genuinely smooth compact interior tensor through every ACTUAL
reduced representative, with its exact central value and support control. -/
theorem exists_smooth_interior_tensor (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) (hz : z∈reducedCarrier N) :
    ∃ T : SmoothCompactTensor,
      compactTensorSupportK T.toCompactTensor⊆reducedCarrier N ∧
      tensorFunctionH T.horizontal T.vertical z=1 := by
  obtain ⟨r,hr,hball⟩ := exists_positive_coordinate_ball N z hz
  exact ⟨interiorTensor N z r hr hball,
    interiorTensor_supportK_subset N z r hr hball,
    interiorTensor_value_at_center N z r hr hball⟩

/-- The localized seed belongs to the ACTUAL smooth automorphic family,
whose genuine effective periodization has value one at this representative. -/
theorem exists_smooth_interior_poincare_one (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) (hz : z∈reducedCarrier N) :
    ∃ T : SmoothCompactTensor,
      compactTensorSupportK T.toCompactTensor⊆reducedCarrier N ∧
      smoothFinitePoincare N (Finset.univ : Finset (Fin 1)) (fun _ => T) z=1 := by
  obtain ⟨T,hK,hvalue⟩ := exists_smooth_interior_tensor N z hz
  have hsupp : Function.support
      (finiteCoreFunction (Finset.univ : Finset (Fin 1)) (fun _ => T.toCompactTensor))⊆
      reducedCarrier N := by
    apply (finiteCoreFunction_support_subset _ _).trans
    intro w hw
    obtain ⟨i,hi⟩ := mem_iUnion.mp hw
    exact hK hi
  refine ⟨T,hK,?_⟩
  have hh := poincare_eq_seed_on_reduced N (Finset.univ : Finset (Fin 1))
    (fun _ => T.toCompactTensor) hsupp hz
  change finiteCompactTensorPoincare N (Finset.univ : Finset (Fin 1))
    (fun _ => T.toCompactTensor) z=1
  rw [hh]
  simpa only [finiteCoreFunction,Fin.sum_univ_one] using hvalue

end
end ImbalancedChen.Part3.Gamma0InteriorSmoothTensorBumps20261025a
