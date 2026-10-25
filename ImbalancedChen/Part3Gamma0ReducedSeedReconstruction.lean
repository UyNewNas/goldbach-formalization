import ImbalancedChen.Part3Gamma0CompactTensorQuotientL2Core
import ImbalancedChen.Part3Gamma0QuotientL2Equivalence

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The reconstruction step for actual quotient core density. A finite compact
positive-height tensor seed supported inside the ACTUAL null-boundary-reduced
Gamma0 carrier is recovered exactly by its genuine effective-group Poincare
sum at every reduced representative. Distinct effective carrier cells are
literally disjoint, so all terms except the identity vanish; no factor two
from the central scalar kernel is introduced.

The actual quotient L2 pullback then equals the seed's actual reduced-carrier
L2 class, and approximation distances are identical. This is not itself a
density assertion. Approximating every reduced-carrier L2 vector by seeds
whose compact support stays inside that carrier remains a separate OPEN
geometric approximation obligation. Whole-plane tensor density is not used.
-/

namespace ImbalancedChen.Part3.Gamma0ReducedSeedReconstruction20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0FiniteCarrierExactMeasure20261024zz
open ImbalancedChen.Part3.Gamma0CarrierInteriorUniqueness20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0QuotientL2Equivalence20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a

/-- Removing all actual translated boundaries leaves EXACTLY the union
of the actual open modular cells, not merely an arbitrary conull set. -/
theorem reducedCarrier_eq_openCarrier (N : ℕ) [NeZero N] :
    reducedCarrier N=gamma0OpenCarrier N := by
  apply Subset.antisymm (reducedCarrier_subset_open N)
  intro z hz
  obtain ⟨q,hq⟩ := mem_iUnion.mp hz
  have hclosed : z∈inverseClassRep N q • modularFD := by
    apply mem_smul_set_iff_inv_smul_mem.mpr
    exact ModularGroup.fdo_subset_fd (mem_smul_set_iff_inv_smul_mem.mp hq)
  refine ⟨mem_iUnion.mpr ⟨q,hclosed⟩,?_⟩
  intro hb
  obtain ⟨r,hr⟩ := mem_iUnion.mp hb
  have hrclosed : z∈inverseClassRep N r • modularFD := by
    apply mem_smul_set_iff_inv_smul_mem.mpr
    exact (mem_smul_set_iff_inv_smul_mem.mp hr).1
  have hqr : q=r := (gamma0_between_open_closed_cells N q r 1 hq
    (by simpa only [one_smul] using hrclosed)).1
  subst r
  have ho := mem_smul_set_iff_inv_smul_mem.mp hq
  have hn := (mem_smul_set_iff_inv_smul_mem.mp hr).2
  exact hn ho

/-- The precise actual reduced representative domain is open. This
geometric fact is what permits compact-interior approximation later. -/
theorem reducedCarrier_isOpen (N : ℕ) [NeZero N] : IsOpen (reducedCarrier N) := by
  rw [reducedCarrier_eq_openCarrier]
  unfold gamma0OpenCarrier
  apply isOpen_iUnion
  intro q
  change IsOpen ((SpecialLinearGroup.mapGL ℝ (inverseClassRep N q)) • ModularGroup.fdo)
  exact ModularGroup.isOpen_fdo.smul _

/-- The representative selected for the identity effective class really
acts as identity, even if its integral matrix representative is -I. -/
theorem effectiveMatrixAction_one (N : ℕ) (z : UpperHalfPlane) :
    effectiveMatrixAction N (1:effectiveGamma0 N) z=z := by
  change effectiveRepresentative N (1:effectiveGamma0 N) • z=z
  have hc : (QuotientGroup.mk (effectiveRepresentative N (1:effectiveGamma0 N)) :
      effectiveGamma0 N)=QuotientGroup.mk (1:CongruenceSubgroup.Gamma0 N) := by
    simpa using effectiveRepresentative_class N (1:effectiveGamma0 N)
  simpa only [one_smul] using same_effective_class_action N
    (effectiveRepresentative N (1:effectiveGamma0 N)) 1 hc z

theorem effectiveCell_one (N : ℕ) [NeZero N] :
    effectiveCell N (1:effectiveGamma0 N)=reducedCarrier N := by
  ext z
  simp only [effectiveCell,mem_image]
  constructor
  · rintro ⟨w,hw,heq⟩
    rw [effectiveMatrixAction_one] at heq
    exact heq ▸ hw
  · intro hz
    exact ⟨z,hz,effectiveMatrixAction_one N z⟩

/-- A nonidentity effective translate of a reduced representative cannot
return to the support of a seed confined to the actual reduced carrier. -/
theorem translated_seed_zero_of_ne_one (N : ℕ) [NeZero N]
    (f : UpperHalfPlane→ℂ) (hsupp : Function.support f⊆reducedCarrier N)
    {z : UpperHalfPlane} (hz : z∈reducedCarrier N)
    (q : effectiveGamma0 N) (hq : q≠1) :
    f (effectiveMatrixAction N q z)=0 := by
  by_contra hnonzero
  have hqcell : effectiveMatrixAction N q z∈effectiveCell N q := ⟨z,hz,rfl⟩
  have h1cell : effectiveMatrixAction N q z∈effectiveCell N 1 := by
    rw [effectiveCell_one]
    exact hsupp hnonzero
  exact (Set.disjoint_left.mp (effectiveCell_disjoint N hq)) hqcell h1cell

/-- Exact reconstruction on ALL actual reduced representatives, not just
an almost-everywhere assertion on a replacement carrier. -/
theorem poincare_eq_seed_on_reduced (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι→CompactTensor)
    (hsupp : Function.support (finiteCoreFunction s T)⊆reducedCarrier N)
    {z : UpperHalfPlane} (hz : z∈reducedCarrier N) :
    finiteCompactTensorPoincare N s T z=finiteCoreFunction s T z := by
  unfold finiteCompactTensorPoincare
  rw [tsum_eq_single (1:effectiveGamma0 N)]
  · rw [effectiveMatrixAction_one]
  · intro q hq
    exact translated_seed_zero_of_ne_one N (finiteCoreFunction s T) hsupp hz q hq

theorem quotientTensorPoincare_reducedProjection (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι→CompactTensor)
    (hsupp : Function.support (finiteCoreFunction s T)⊆reducedCarrier N)
    (z : reducedCarrier N) :
    quotientTensorPoincare N s T (reducedProjection N z)=finiteCoreFunction s T z := by
  rw [show reducedProjection N z=orbitProjection N z from rfl,
    quotientTensorPoincare_projection]
  exact poincare_eq_seed_on_reduced N s T hsupp z.property

/-- The seed's L2 membership on the actual reduced subtype is derived
from the actual quotient measure-preserving pullback and reconstruction. -/
theorem reducedSeed_memLp_two (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι→CompactTensor)
    (hsupp : Function.support (finiteCoreFunction s T)⊆reducedCarrier N) :
    MemLp (fun z : reducedCarrier N => finiteCoreFunction s T z) 2
      (reducedCarrierMeasure N) := by
  have hp := (quotientTensorPoincare_memLp_two N s T).comp_measurePreserving
    (reducedProjection_measurePreserving N)
  apply hp.congr
  exact Eventually.of_forall (quotientTensorPoincare_reducedProjection N s T hsupp)

def reducedSeedL2 (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι→CompactTensor)
    (hsupp : Function.support (finiteCoreFunction s T)⊆reducedCarrier N) :
    Lp ℂ 2 (reducedCarrierMeasure N) :=
  (reducedSeed_memLp_two N s T hsupp).toLp (fun z => finiteCoreFunction s T z)

/-- Actual quotient L2 reconstruction uses precisely the already proved
canonical quotient/carrier linear isometry, with its original measures. -/
theorem quotientTensorPoincareL2_pullback_eq_seed (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι→CompactTensor)
    (hsupp : Function.support (finiteCoreFunction s T)⊆reducedCarrier N) :
    quotientL2ReducedCarrierEquiv N (quotientTensorPoincareL2 N s T)=
      reducedSeedL2 N s T hsupp := by
  change Lp.compMeasurePreserving (reducedProjection N)
    (reducedProjection_measurePreserving N)
    ((quotientTensorPoincare_memLp_two N s T).toLp (quotientTensorPoincare N s T)) = _
  rw [Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  exact ((quotientTensorPoincare_memLp_two N s T).comp_measurePreserving
    (reducedProjection_measurePreserving N)).coeFn_toLp.trans
      ((Eventually.of_forall (quotientTensorPoincare_reducedProjection N s T hsupp)).trans
        (reducedSeed_memLp_two N s T hsupp).coeFn_toLp.symm)

/-- Quantitative approximation identity for the ACTUAL quotient. A later
compact-interior approximation can use this equality without a norm loss,
an assumed dense range, or a whole-plane-to-quotient substitution. -/
theorem quotient_distance_eq_reduced_seed_distance (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι→CompactTensor)
    (hsupp : Function.support (finiteCoreFunction s T)⊆reducedCarrier N)
    (F : Lp ℂ 2 (carrierPushforward N)) :
    dist (quotientTensorPoincareL2 N s T) F =
      dist (reducedSeedL2 N s T hsupp) (quotientL2ReducedCarrierEquiv N F) := by
  calc
    _ = dist (quotientL2ReducedCarrierEquiv N (quotientTensorPoincareL2 N s T))
        (quotientL2ReducedCarrierEquiv N F) :=
      ((quotientL2ReducedCarrierEquiv N).isometry.dist_eq _ _).symm
    _ = _ := by rw [quotientTensorPoincareL2_pullback_eq_seed]

end
end ImbalancedChen.Part3.Gamma0ReducedSeedReconstruction20261025a
