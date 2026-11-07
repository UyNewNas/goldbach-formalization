import ImbalancedChen.Part3Gamma0LocalWeightedTensorApproximation
import Mathlib.Topology.PartitionOfUnity

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Global compact localization on the ACTUAL reduced-carrier chart. Every
continuous compactly supported target confined to that actual chart is
EXACTLY a finite sum of continuous compactly supported pieces. Each piece
has topological support inside an actual positive coordinate ball's INNER
plateau, where the preceding weighted tensor approximation theorem applies.

The partition of unity is constructed by the pinned compact open-cover
theorem, rather than supplied as a field or assumed from a density target.
No quotient-dense conclusion is claimed merely from this localization.
-/

namespace ImbalancedChen.Part3.Gamma0CompactInteriorLocalization20261025a

noncomputable section
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane BigOperators
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0InteriorSmoothTensorBumps20261025a

theorem exists_actual_coordinate_ball (N : ℕ) [NeZero N] (p : ℝ×ℝ)
    (hp : 0<p.2) (hred : chartLift p∈reducedCarrier N) :
    ∃ r : ℝ,0<r ∧ ∀ q∈Metric.ball p r,
      0<q.2 ∧ chartLift q∈reducedCarrier N := by
  obtain ⟨r,hr,hball⟩ := exists_positive_coordinate_ball N (chartLift p) hred
  have heq : ((chartLift p).re,(chartLift p).im)=p := by
    rw [chartLift_of_positive hp]
    rfl
  exact ⟨r,hr,by simpa only [heq] using hball⟩

/-- A genuine finite partition into targets to which the support-preserving
weighted LOCAL tensor approximation applies. The index set is a finite
subset of the actual topological support of F; empty support is included. -/
theorem exists_finite_actual_interior_localization
    (N : ℕ) [NeZero N] (F : (ℝ×ℝ)→ℂ)
    (hFcont : Continuous F) (hFc : HasCompactSupport F)
    (hinside : ∀ p∈tsupport F,0<p.2 ∧ chartLift p∈reducedCarrier N) :
    ∃ (S : Finset (tsupport F)) (r : tsupport F→ℝ)
      (G : {i : tsupport F // i∈S}→((ℝ×ℝ)→ℂ)),
      (∀ i∈S,0<r i ∧ ∀ q∈Metric.ball (i:ℝ×ℝ) (r i),
        0<q.2 ∧ chartLift q∈reducedCarrier N) ∧
      (∀ i,Continuous (G i) ∧ HasCompactSupport (G i) ∧
        tsupport (G i)⊆Metric.ball (i.1:ℝ×ℝ) (r i.1/4)) ∧
      F=∑ i,G i := by
  classical
  have hlocal : ∀ i : tsupport F,∃ r : ℝ,0<r ∧
      ∀ q∈Metric.ball (i:ℝ×ℝ) r,0<q.2 ∧ chartLift q∈reducedCarrier N := by
    intro i
    exact exists_actual_coordinate_ball N i (hinside i i.property).1 (hinside i i.property).2
  choose r hr hball using hlocal
  have hcover : tsupport F⊆⋃ i : tsupport F,Metric.ball (i:ℝ×ℝ) (r i/4) := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p,hp⟩,?_⟩
    change dist p p<r ⟨p,hp⟩/4
    rw [dist_self]
    exact div_pos (hr _) (by norm_num)
  obtain ⟨S,hS⟩ := hFc.elim_finite_subcover
    (fun i : tsupport F => Metric.ball (i:ℝ×ℝ) (r i/4))
    (fun _ => Metric.isOpen_ball) hcover
  let I := {i : tsupport F // i∈S}
  let U : I→Set (ℝ×ℝ) := fun i => Metric.ball (i.1:ℝ×ℝ) (r i.1/4)
  have hIU : tsupport F⊆⋃ i : I,U i := by
    intro p hp
    obtain ⟨i,hi,hpU⟩ := mem_iUnion₂.mp (hS hp)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hpU⟩
  obtain ⟨psi,hsub,hcompact⟩ :=
    PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
      hFc U (fun _ => Metric.isOpen_ball) (locallyFinite_of_finite _) hIU
  let G : I→((ℝ×ℝ)→ℂ) := fun i p => ((psi i p:ℝ):ℂ)*F p
  refine ⟨S,r,G,?_,?_,?_⟩
  · intro i _
    exact ⟨hr i,hball i⟩
  · intro i
    have hcont : Continuous (G i) :=
      (Complex.continuous_ofReal.comp (psi i).continuous).mul hFcont
    have hcomp : HasCompactSupport (G i) := hFc.mul_left
    have hsupp : tsupport (G i)⊆U i := by
      apply tsupport_mul_subset_left.trans
      exact (tsupport_comp_subset rfl _).trans (hsub i)
    exact ⟨hcont,hcomp,hsupp⟩
  · funext p
    by_cases hp : p∈tsupport F
    · have hsum := psi.sum_eq_one' p hp
      rw [finsum_eq_sum (fun i : I => psi i p)
        (Finite.subset finite_univ (subset_univ (Function.support (fun i : I => psi i p))))] at hsum
      rw [Fintype.sum_subset (by simp)] at hsum
      symm
      change (∑ i : I,((psi i p:ℝ):ℂ)*F p)=F p
      calc
        _ = ((∑ i : I,psi i p:ℝ):ℂ)*F p := by push_cast; rw [Finset.sum_mul]
        _ = F p := by rw [hsum]; simp only [Complex.ofReal_one,one_mul]
    · have hz : F p=0 := image_eq_zero_of_notMem_tsupport hp
      simp only [Finset.sum_apply,G,hz,mul_zero,Finset.sum_const_zero]

end
end ImbalancedChen.Part3.Gamma0CompactInteriorLocalization20261025a
