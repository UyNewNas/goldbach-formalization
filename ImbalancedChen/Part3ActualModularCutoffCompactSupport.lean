import ImbalancedChen.Part3ActualModularSmoothCutoffL2Tail
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Compact support of the ACTUAL global modular cutoff on the genuine
Gamma0 quotient. The existing quotientCutoff is reused unchanged; it is
the full modular cutoff pulled to the finite Gamma0 cover, not a single
infinity-cusp cutoff. A truncated actual modular fundamental domain is
compact, using its genuine positive height floor. All actual Gamma0 coset
translates are retained in a finite compact carrier.

Every nonzero cutoff point has an actual Gamma0 translate in that concrete
compact carrier, and hence an actual effective-Gamma0 translate there.
The quotient support is contained in its compact quotient image. Native
properness makes the actual quotient Hausdorff, so this proves genuine
HasCompactSupport, without a supplied compact-lift/core-membership premise.
No membership in the finite tensor core or completed form is asserted.
-/

namespace ImbalancedChen.Part3.ActualModularCutoffCompactSupport20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups UpperHalfPlane Pointwise
open ModularFundamentalFiniteMeasure20261024z Gamma0FiniteMeasureCarrier20261024z
open Gamma0QuotientCellPushforward20261025a Gamma0ModularFiniteCoverMeasure20261025a
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open ActualParabolicHighSeedLocalFinite20261025a ActualModularSmoothCuspCutoff20261025a
open ActualModularSmoothCutoffL2Tail20261025a

/-- The literal closed classical modular cell truncated at a finite height. -/
def truncatedModularFD (H : ℝ) : Set UpperHalfPlane := modularFD∩{z | z.im≤H}

theorem truncatedModularFD_isClosed (H : ℝ) : IsClosed (truncatedModularFD H) :=
  modularFD_isClosed.inter (isClosed_le UpperHalfPlane.continuous_im continuous_const)

/-- Compactness uses the actual FD's height floor; being merely bounded
in the complex plane would not suffice near the real boundary of H. -/
theorem truncatedModularFD_isCompact (H : ℝ) : IsCompact (truncatedModularFD H) := by
  let B := closedHeightStrip (1/2) H
  have hB : IsCompact B := closedHeightStrip_isCompact (1/2) H (by norm_num)
  have htranslated : IsCompact ((fun z : UpperHalfPlane => (-(1/2):ℝ)+ᵥz) '' B) :=
    hB.image (continuous_const_vadd _)
  apply htranslated.of_isClosed_subset (truncatedModularFD_isClosed H)
  intro z hz
  refine ⟨((1/2):ℝ)+ᵥz,?_,?_⟩
  · have hre := abs_le.mp (modularFD_real_bound hz.1)
    have him := (modularFD_half_lt_im hz.1).le
    change (((1/2):ℝ)+ᵥz).re∈Icc (0:ℝ) 1 ∧
      (((1/2):ℝ)+ᵥz).im∈Icc (1/2:ℝ) H
    simp only [UpperHalfPlane.vadd_re,UpperHalfPlane.vadd_im]
    exact ⟨⟨by linarith [hre.1],by linarith [hre.2]⟩,him,hz.2⟩
  · simp only [vadd_vadd,neg_add_cancel,zero_vadd]

/-- Every actual Gamma0 class is retained in this finite translated
truncation; this is not just the standard infinity-cusp strip. -/
def truncatedGammaCarrier (N : ℕ) [NeZero N] (H : ℝ) : Set UpperHalfPlane :=
  ⋃ q : gamma0Classes N,inverseClassRep N q • truncatedModularFD H

theorem truncatedGammaCarrier_isCompact (N : ℕ) [NeZero N] (H : ℝ) :
    IsCompact (truncatedGammaCarrier N H) := by
  letI : Fintype (gamma0Classes N) :=
    (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex
  exact isCompact_iUnion fun q => (truncatedModularFD_isCompact H).smul (inverseClassRep N q)

theorem orbitProjection_continuous (N : ℕ) : Continuous (orbitProjection N) :=
  continuous_quotient_mk'

/-- The topology is the actual orbit quotient topology. Its Hausdorff
property follows from the already proved genuine proper Gamma0 action. -/
theorem quotient_t2 (N : ℕ) : T2Space (Gamma0OrbitSpace N) := by
  letI := gamma0_properSMul N
  infer_instance

def quotientTruncatedCarrier (N : ℕ) [NeZero N] (H : ℝ) : Set (Gamma0OrbitSpace N) :=
  orbitProjection N '' truncatedGammaCarrier N H

theorem quotientTruncatedCarrier_isCompact (N : ℕ) [NeZero N] (H : ℝ) :
    IsCompact (quotientTruncatedCarrier N H) :=
  (truncatedGammaCarrier_isCompact N H).image (orbitProjection_continuous N)

/-- Above height 2Y the identity parabolic coset already contributes one.
Actual uniqueness of high-profile contributions makes the global low
cutoff zero, independently of the chosen coset representative. -/
theorem globalCutoff_zero_of_two_mul_le_im (Y : ℝ) (hY : 1≤Y)
    (z : UpperHalfPlane) (hz : 2*Y≤z.im) : globalCutoff Y z=0 := by
  let q : GammaInfinityCosets 1 := Quotient.mk'' (levelOneMatrix (1:SL(2,ℤ)))
  have hrep := periodicProfile_eq_representative 1 Y z q
  change periodicSeedOnCosets 1 (fun w => highProfile Y w.im) (highProfile_periodic 1 Y)
    z (Quotient.mk'' (levelOneMatrix (1:SL(2,ℤ))))=_ at hrep
  rw [periodicSeedOnCosets_mk] at hrep
  have hidentity : highProfile Y ((levelOneMatrix (1:SL(2,ℤ))) • z).im=
      highProfile Y z.im := by change highProfile Y ((1:SL(2,ℤ)) • z).im=_; simp
  rw [hidentity] at hrep
  have hone : highProfile Y (parabolicRepresentative 1 q • z).im=1 :=
    hrep.symm.trans (highProfile_eq_one Y (lt_of_lt_of_le (by norm_num) hY) z.im hz)
  rw [globalCutoff,highTrace_eq_single_of_nonzero 1 Y hY q z (by rw [hone];norm_num),
    hone,sub_self]

theorem globalCutoff_nonzero_height_lt (Y : ℝ) (hY : 1≤Y)
    (z : UpperHalfPlane) (hz : globalCutoff Y z≠0) : z.im<2*Y :=
  lt_of_not_ge fun h => hz (globalCutoff_zero_of_two_mul_le_im Y hY z h)

/-- Concrete compact lifting cover, obtained from the real finite Gamma0
carrier and the global modular invariance. No lifting existence is input. -/
theorem globalCutoff_nonzero_compact_gamma_cover (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1≤Y) (z : UpperHalfPlane) (hz : globalCutoff Y z≠0) :
    ∃ γ : CongruenceSubgroup.Gamma0 N,γ • z∈truncatedGammaCarrier N (2*Y) := by
  obtain ⟨γ,hγ⟩ := exists_gamma0_smul_mem_carrier N z
  obtain ⟨q,hq⟩ := mem_iUnion.mp hγ
  obtain ⟨w,hw,hweq⟩ := hq
  have hcutγ := globalCutoff_sl2_invariant Y (γ:SL(2,ℤ)) z
  have hcutw := globalCutoff_sl2_invariant Y (inverseClassRep N q) w
  rw [hweq] at hcutw
  have hwcut : globalCutoff Y w≠0 := by rw [← hcutw,hcutγ];exact hz
  have hwheight : w.im≤2*Y := (globalCutoff_nonzero_height_lt Y hY w hwcut).le
  refine ⟨γ,mem_iUnion.mpr ⟨q,?_⟩⟩
  exact ⟨w,⟨hw,hwheight⟩,hweq⟩

/-- The genuine effective-action version consumed by compact-seed
Poincare reconstruction. Central signs are handled by the existing action. -/
theorem globalCutoff_nonzero_compact_effective_cover (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1≤Y) (z : UpperHalfPlane) (hz : globalCutoff Y z≠0) :
    ∃ q : effectiveGamma0 N,effectiveMatrixAction N q z∈truncatedGammaCarrier N (2*Y) := by
  obtain ⟨γ,hγ⟩ := globalCutoff_nonzero_compact_gamma_cover N Y hY z hz
  refine ⟨QuotientGroup.mk γ,?_⟩
  simpa only [effectiveMatrixAction_mk_gamma] using hγ

/-- Exact support container for the existing canonical quotient cutoff. -/
theorem quotientCutoff_support_subset (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1≤Y) :
    Function.support (quotientCutoff N Y)⊆quotientTruncatedCarrier N (2*Y) := by
  intro u hu
  revert hu
  refine Quotient.inductionOn u (fun z hz => ?_)
  have hglobal : globalCutoff Y z≠0 := by simpa only [quotientCutoff_projection] using hz
  obtain ⟨γ,hγ⟩ := globalCutoff_nonzero_compact_gamma_cover N Y hY z hglobal
  exact ⟨γ • z,hγ,orbitProjection_smul N γ z⟩

/-- Genuine compact support on the actual Hausdorff quotient; membership
in an analytic core or completed energy domain is a separate next bridge. -/
theorem quotientCutoff_hasCompactSupport (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1≤Y) :
    HasCompactSupport (quotientCutoff N Y) := by
  letI := quotient_t2 N
  exact HasCompactSupport.of_support_subset_isCompact
    (quotientTruncatedCarrier_isCompact N (2*Y)) (quotientCutoff_support_subset N Y hY)

end
end ImbalancedChen.Part3.ActualModularCutoffCompactSupport20261025a
