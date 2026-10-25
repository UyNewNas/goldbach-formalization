import ImbalancedChen.Part3Gamma0InteriorSmoothTensorBumps
import Mathlib.Topology.Compactness.Compact

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Every compact set inside the actual open reduced Gamma0 carrier has a
FINITE cover by open tensor plateaux. Each plateau is supported by an
actual smooth separated seed equal to one throughout that plateau, with
its entire compact support rectangle still inside the SAME actual carrier.

This is genuine compact-interior localization for subsequent weighted L2
approximation. No partition, approximation, dense range or quotient dense
core is assumed or inferred from this finite-cover statement alone.
-/

namespace ImbalancedChen.Part3.Gamma0CompactInteriorTensorCover20261025a

noncomputable section
open Set Metric
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0InteriorSmoothTensorBumps20261025a

def coordinatePlateau (z : UpperHalfPlane) (r : ℝ) : Set UpperHalfPlane :=
  {w | dist (w.re,w.im) (z.re,z.im)<r/4}

theorem coordinatePlateau_isOpen (z : UpperHalfPlane) (r : ℝ) :
    IsOpen (coordinatePlateau z r) := by
  exact isOpen_ball.preimage (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)

theorem mem_coordinatePlateau_center (z : UpperHalfPlane) (r : ℝ) (hr : 0<r) :
    z∈coordinatePlateau z r := by
  change dist (z.re,z.im) (z.re,z.im)<r/4
  rw [dist_self]
  positivity

theorem coordinatePlateau_subset_reduced (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N) :
    coordinatePlateau z r⊆reducedCarrier N := by
  intro w hw
  have hdist : dist (w.re,w.im) (z.re,z.im)<r :=
    hw.trans (by linarith)
  have hh := (hball (w.re,w.im) hdist).2
  have heq : chartLift (w.re,w.im)=w := by
    rw [chartLift_of_positive w.im_pos]
    apply UpperHalfPlane.ext
    ext <;> rfl
  simpa only [heq] using hh

/-- Both one-dimensional bumps equal one throughout the same open
coordinate plateau. This is stronger than a nonzero value at its center. -/
theorem interiorTensor_one_on_plateau (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) (r : ℝ) (hr : 0<r)
    (hball : ∀ p∈Metric.ball (z.re,z.im) r,
      0<p.2 ∧ chartLift p∈reducedCarrier N)
    (w : UpperHalfPlane) (hw : w∈coordinatePlateau z r) :
    tensorFunctionH (interiorTensor N z r hr hball).horizontal
      (interiorTensor N z r hr hball).vertical w=1 := by
  have hmax : max (dist w.re z.re) (dist w.im z.im)<r/4 := by
    simpa only [coordinatePlateau,Set.mem_setOf_eq,Prod.dist_eq] using hw
  have hx : smallCoordinateBump z.re r hr w.re=1 := by
    apply (smallCoordinateBump z.re r hr).one_of_mem_closedBall
    exact (le_max_left _ _).trans hmax.le
  have hy : smallCoordinateBump z.im r hr w.im=1 := by
    apply (smallCoordinateBump z.im r hr).one_of_mem_closedBall
    exact (le_max_right _ _).trans hmax.le
  rw [tensorFunctionH_eq]
  change ((smallCoordinateBump z.re r hr w.re:ℝ):ℂ)*
    ((smallCoordinateBump z.im r hr w.im:ℝ):ℂ)=1
  rw [hx,hy]
  norm_num

theorem exists_smooth_interior_tensor_patch (N : ℕ) [NeZero N]
    (z : UpperHalfPlane) (hz : z∈reducedCarrier N) :
    ∃ (T : SmoothCompactTensor) (U : Set UpperHalfPlane),
      IsOpen U ∧ z∈U ∧ U⊆reducedCarrier N ∧
      compactTensorSupportK T.toCompactTensor⊆reducedCarrier N ∧
      ∀ w∈U,tensorFunctionH T.horizontal T.vertical w=1 := by
  obtain ⟨r,hr,hball⟩ := exists_positive_coordinate_ball N z hz
  exact ⟨interiorTensor N z r hr hball,coordinatePlateau z r,
    coordinatePlateau_isOpen z r,mem_coordinatePlateau_center z r hr,
    coordinatePlateau_subset_reduced N z r hr hball,
    interiorTensor_supportK_subset N z r hr hball,
    interiorTensor_one_on_plateau N z r hr hball⟩

/-- Actual compact-interior FINITE tensor cover. The finite indices are
points of the given compact set, while every chosen tensor has independently
proved compact support inside the exact original reduced carrier. -/
theorem exists_finite_smooth_tensor_plateau_cover (N : ℕ) [NeZero N]
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hinside : K⊆reducedCarrier N) :
    ∃ (S : Finset K) (T : K→SmoothCompactTensor) (U : K→Set UpperHalfPlane),
      K⊆⋃ i∈S,U i ∧
      (∀ i∈S,IsOpen (U i) ∧ U i⊆reducedCarrier N ∧
        compactTensorSupportK (T i).toCompactTensor⊆reducedCarrier N ∧
        ∀ w∈U i,tensorFunctionH (T i).horizontal (T i).vertical w=1) := by
  have hlocal : ∀ z : K,∃ (T : SmoothCompactTensor) (U : Set UpperHalfPlane),
      IsOpen U ∧ (z:UpperHalfPlane)∈U ∧ U⊆reducedCarrier N ∧
      compactTensorSupportK T.toCompactTensor⊆reducedCarrier N ∧
      ∀ w∈U,tensorFunctionH T.horizontal T.vertical w=1 :=
    fun z => exists_smooth_interior_tensor_patch N z (hinside z.property)
  choose T U hdata using hlocal
  have hcover : K⊆⋃ i : K,U i := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,(hdata ⟨z,hz⟩).2.1⟩
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover U (fun i => (hdata i).1) hcover
  refine ⟨S,T,U,hS,?_⟩
  intro i _
  exact ⟨(hdata i).1,(hdata i).2.2.1,(hdata i).2.2.2.1,(hdata i).2.2.2.2⟩

end
end ImbalancedChen.Part3.Gamma0CompactInteriorTensorCover20261025a
