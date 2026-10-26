import ImbalancedChen.Part3ActualHeckeCorrespondenceCarrier
import ImbalancedChen.Part3Gamma0NonnegativePoincareUnfolding

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual finite correspondence carrier is a true conull fundamental
carrier for Gamma0(N*p): its prime-level translates cover conullly, and
every prime-level return lies in the actual full action kernel +/-I.
Both facts are derived from the proved finite group cover and original
canonical reduced-carrier uniqueness. No fundamental-domain or measure
comparison premise is inserted.
-/

namespace ImbalancedChen.Part3.ActualHeckeCarrierFundamental20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualHeckeIntersectionSubgroup20261026b ActualHeckeFiniteCover20261026b
open ActualHeckeCorrespondenceCarrier20261026b Gamma0ActualCuspsSourceOnly
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierInteriorUniqueness20261025a
open Gamma0NonnegativePoincareUnfolding20261025a Gamma0QuotientCellPushforward20261025a

def includePrimeLevel (N p : ℕ) (g : CongruenceSubgroup.Gamma0 (N*p)) :
    CongruenceSubgroup.Gamma0 N := ⟨g, by
  rw [gamma0_mem_iff_level_dvd_c]
  exact dvd_trans (by exact_mod_cast (dvd_mul_right N p))
    ((gamma0_mem_iff_level_dvd_c (N*p) g).mp g.property)⟩

def subgroupToPrimeLevel (N p : ℕ) (h : heckeIntersection N p) :
    CongruenceSubgroup.Gamma0 (N*p) := ⟨h.val, h.property⟩

theorem includePrimeLevel_mem_intersection (N p : ℕ) (g : CongruenceSubgroup.Gamma0 (N*p)) :
    includePrimeLevel N p g ∈ heckeIntersection N p := g.property

theorem actionKernel_mem_intersection (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CongruenceSubgroup.Gamma0 N) (hg : g ∈ gamma0ActionKernel N) :
    g ∈ heckeIntersection N p :=
  (heckeIntersection_mem_iff_fixed N p hp hpN g).mpr
    (actionKernel_branch_trivial N p hp hpN g hg none)

/-- An actual prime-level matrix returning to the finite correspondence
carrier must be a genuine scalar action-kernel element. -/
theorem correspondence_return_mem_kernel (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (g : CongruenceSubgroup.Gamma0 (N*p))
    {z : ℍ} (hz : z ∈ correspondenceCarrier N p hp hpN)
    (hgz : g • z ∈ correspondenceCarrier N p hp hpN) : g ∈ gamma0ActionKernel (N*p) := by
  obtain ⟨k, y, hy, hyz⟩ := mem_iUnion.mp hz
  obtain ⟨j, x, hx, hxz⟩ := mem_iUnion.mp hgz
  let a := coverRepresentative N p hp hpN j
  let b := coverRepresentative N p hp hpN k
  let G := includePrimeLevel N p g
  let r : CongruenceSubgroup.Gamma0 N := a⁻¹*G*b
  have hmove : r • y = x := by
    change (a⁻¹*G*b) • y = x
    rw [mul_smul, mul_smul]
    change b • y = z at hyz
    change a • x = g • z at hxz
    rw [hyz]
    change a⁻¹ • (g • z) = x
    rw [← hxz, inv_smul_smul]
  have hr : r ∈ gamma0ActionKernel N :=
    gamma0_open_to_closed_mem_kernel N r (reducedCarrier_subset_open N hy)
      (by rw [hmove]; exact hx.1)
  have hrH := actionKernel_mem_intersection N p hp hpN r hr
  have hGH := includePrimeLevel_mem_intersection N p g
  have hcentral : r*a = a*r := by
    apply Subtype.ext
    rcases (gamma0_actionKernel_iff N r).mp hr with hpos | hneg
    · simp [hpos]
    · simp [hneg]
  have hfactor : r*a = G*b := by
    rw [hcentral]
    dsimp [r]
    group
  have hpair : ((⟨r,hrH⟩ : heckeIntersection N p),j) =
      ((⟨G,hGH⟩ : heckeIntersection N p),k) :=
    (actualFiniteCoverEquiv N p hp hpN).injective hfactor
  have hjk : j = k := congrArg Prod.snd hpair
  have hab : a = b := congrArg (coverRepresentative N p hp hpN) hjk
  have hconj : (g : SL(2, ℤ)) =
      (a : SL(2, ℤ))*(r : SL(2, ℤ))*(a : SL(2, ℤ))⁻¹ := by
    change (G : SL(2, ℤ)) = _
    have hconjG : G = a*r*a⁻¹ := by
      dsimp [r]
      rw [← hab]
      group
    exact congrArg (fun q : CongruenceSubgroup.Gamma0 N => (q : SL(2, ℤ))) hconjG
  apply (gamma0_actionKernel_iff (N*p) g).mpr
  apply (sl2_fixed_all_iff (g : SL(2, ℤ))).mp
  intro w
  have hfix := (sl2_fixed_all_iff (r : SL(2, ℤ))).mpr ((gamma0_actionKernel_iff N r).mp hr)
    ((a : SL(2, ℤ))⁻¹ • w)
  rw [hconj]
  simpa only [mul_smul, smul_inv_smul] using congrArg (fun u : ℍ => (a : SL(2, ℤ)) • u) hfix

theorem correspondenceProjection_injOn (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    InjOn (orbitProjection (N*p)) (correspondenceCarrier N p hp hpN) := by
  intro z hz w hw hzw
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hzw)
  have hker := correspondence_return_mem_kernel N p hp hpN g hw (by rw [hg]; exact hz)
  have hfix := (sl2_fixed_all_iff (g : SL(2, ℤ))).mpr
    ((gamma0_actionKernel_iff (N*p) g).mp hker) w
  exact hg.symm.trans hfix

def allCorrespondenceTranslates (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : ¬ p ∣ N) : Set ℍ :=
  ⋃ g : CongruenceSubgroup.Gamma0 (N*p), g • correspondenceCarrier N p hp hpN

/-- The genuine finite cover of the original group supplies every
original reduced-carrier translate as a prime-level correspondence translate. -/
theorem allEffectiveCells_subset_correspondenceTranslates (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    allEffectiveCells N ⊆ allCorrespondenceTranslates N p hp hpN := by
  intro z hz
  obtain ⟨q, x, hx, hxz⟩ := mem_iUnion.mp hz
  let a := effectiveRepresentative N q
  let pair := (actualFiniteCoverEquiv N p hp hpN).symm a
  have hfactor : (pair.1 : CongruenceSubgroup.Gamma0 N)*coverRepresentative N p hp hpN pair.2 = a :=
    (actualFiniteCoverEquiv N p hp hpN).apply_symm_apply a
  refine mem_iUnion.mpr ⟨subgroupToPrimeLevel N p pair.1, ?_⟩
  refine ⟨coverAction N p hp hpN pair.2 x, mem_iUnion.mpr ⟨pair.2, ⟨x,hx,rfl⟩⟩, ?_⟩
  calc
    _ = a • x := by
      change (pair.1 : CongruenceSubgroup.Gamma0 N) •
        (coverRepresentative N p hp hpN pair.2 • x) = a • x
      rw [← mul_smul, hfactor]
    _ = z := hxz

/-- Actual prime-level translates of the finite correspondence carrier
cover conullly; its omitted set is contained in the original explicit null set. -/
theorem allCorrespondenceTranslates_ae (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ∀ᵐ z ∂(volume : Measure ℍ), z ∈ allCorrespondenceTranslates N p hp hpN :=
  (allEffectiveCells_ae N).mono (fun z hz =>
    allEffectiveCells_subset_correspondenceTranslates N p hp hpN hz)

end
end ImbalancedChen.Part3.ActualHeckeCarrierFundamental20261026b
