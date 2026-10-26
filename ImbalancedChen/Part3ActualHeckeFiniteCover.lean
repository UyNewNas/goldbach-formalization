import ImbalancedChen.Part3ActualHeckeBranchTransitivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
An exact finite relative cover of the ACTUAL group Gamma0(N) by its
concrete subgroup Gamma0(N*p). Representatives are actual matrices
reaching the proved Hecke branches. Every original Gamma0 matrix has a
unique subgroup-factor/branch pair, supplied as an actual equivalence.
No subgroup index, coset bijection, domain decomposition or cover measure
is supplied as an assumption. Quotient measure transport is still separate.
-/

namespace ImbalancedChen.Part3.ActualHeckeFiniteCover20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualHeckeIntersectionSubgroup20261026b ActualHeckeBranchTransitivity20261026b

def coverRepresentative (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) :
    CongruenceSubgroup.Gamma0 N := Classical.choose (every_branch_reached N p hp hpN j)

theorem coverRepresentative_branch (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (j : Branch p) :
    branchImage N p hp hpN (coverRepresentative N p hp hpN j)
      (coverRepresentative N p hp hpN j).property none = j :=
  Classical.choose_spec (every_branch_reached N p hp hpN j)

def branchLabel (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CongruenceSubgroup.Gamma0 N) : Branch p := branchImage N p hp hpN g g.property none

/-- The exact original group element left after choosing the actual
branch representative lies in the concrete subgroup Gamma0(N*p). -/
theorem coverFactor_mem (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CongruenceSubgroup.Gamma0 N) :
    g*(coverRepresentative N p hp hpN (branchLabel N p hp hpN g))⁻¹ ∈ heckeIntersection N p := by
  apply (heckeIntersection_mem_iff_fixed N p hp hpN _).mpr
  let r := coverRepresentative N p hp hpN (branchLabel N p hp hpN g)
  change branchImage N p hp hpN (g*r⁻¹) (g*r⁻¹).property none = none
  calc
    _ = branchImage N p hp hpN r⁻¹ (r⁻¹).property
        (branchImage N p hp hpN g g.property none) := branchImage_mul N p hp hpN g r⁻¹ none
    _ = branchImage N p hp hpN r⁻¹ (r⁻¹).property
        (branchImage N p hp hpN r r.property none) := by
      congr 1
      exact (coverRepresentative_branch N p hp hpN (branchLabel N p hp hpN g)).symm
    _ = none := branchImage_inverse N p hp hpN r r.property none

theorem branchLabel_subgroup_mul_representative (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (h : heckeIntersection N p) (j : Branch p) :
    branchLabel N p hp hpN ((h : CongruenceSubgroup.Gamma0 N)*coverRepresentative N p hp hpN j) = j := by
  unfold branchLabel
  rw [branchImage_mul,
    (heckeIntersection_mem_iff_fixed N p hp hpN (h : CongruenceSubgroup.Gamma0 N)).mp h.property]
  exact coverRepresentative_branch N p hp hpN j

/-- Concrete finite relative covering bijection. Its first coordinate is
the ACTUAL Gamma0(N*p) subgroup inside Gamma0(N), its second p+1 branches. -/
def actualFiniteCoverEquiv (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    (heckeIntersection N p) × Branch p ≃ CongruenceSubgroup.Gamma0 N where
  toFun q := (q.1 : CongruenceSubgroup.Gamma0 N)*coverRepresentative N p hp hpN q.2
  invFun g := (⟨g*(coverRepresentative N p hp hpN (branchLabel N p hp hpN g))⁻¹,
    coverFactor_mem N p hp hpN g⟩, branchLabel N p hp hpN g)
  left_inv := by
    rintro ⟨h,j⟩
    have hlabel := branchLabel_subgroup_mul_representative N p hp hpN h j
    apply Prod.ext
    · apply Subtype.ext
      change (((h : CongruenceSubgroup.Gamma0 N)*coverRepresentative N p hp hpN j) *
        (coverRepresentative N p hp hpN
          (branchLabel N p hp hpN ((h : CongruenceSubgroup.Gamma0 N)*coverRepresentative N p hp hpN j)))⁻¹) = h
      rw [hlabel]
      group
    · exact hlabel
  right_inv := by
    intro g
    change (g*(coverRepresentative N p hp hpN (branchLabel N p hp hpN g))⁻¹) *
      coverRepresentative N p hp hpN (branchLabel N p hp hpN g) = g
    group

/-- Exact reindexing of an actual summable group seed by concrete
subgroup factor and finite Hecke branch, before any quotient integral. -/
theorem actualFiniteCover_hasSum (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (F : CongruenceSubgroup.Gamma0 N → ℂ) (s : ℂ) (hF : HasSum F s) :
    HasSum (fun q : (heckeIntersection N p) × Branch p =>
      F ((q.1 : CongruenceSubgroup.Gamma0 N)*coverRepresentative N p hp hpN q.2)) s :=
  (actualFiniteCoverEquiv N p hp hpN).hasSum_iff.mpr hF

end
end ImbalancedChen.Part3.ActualHeckeFiniteCover20261026b
