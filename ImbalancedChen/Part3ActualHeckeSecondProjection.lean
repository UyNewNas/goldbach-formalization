import ImbalancedChen.Part3ActualPrimeHeckePhysicalFourier
import ImbalancedChen.Part3ActualHeckeForgetCoverMeasure

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The second physical Hecke correspondence projection from Gamma0(N*p)\H
to Gamma0(N)\H, induced by z->p*z, is actually well defined and measurable.
Its original p+1 cover branches identify the native Hecke trace exactly.
Whole-H canonical volume preservation of the inducing SL2(R) matrix is
proved separately; no quotient pushforward or adjoint measure is assumed.
-/

namespace ImbalancedChen.Part3.ActualHeckeSecondProjection20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualPrimeHeckeRealBranch20261026b ActualPrimeHeckeQuotientDescent20261026b
open ActualPrimeHeckePhysicalFourier20261026b ActualHeckeFiniteCover20261026b
open ActualHeckeCorrespondenceCarrier20261026b ActualHeckeCarrierFundamental20261026b
open ActualHeckeIntersectionSubgroup20261026b ActualHeckeForgetCoverMeasure20261026b
open Gamma0QuotientCellPushforward20261025a ActualPoincareSpectralCoefficient20261026a

theorem primeLevel_dilation_deck (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (g : CongruenceSubgroup.Gamma0 (N*p)) :
    ∃ h : CongruenceSubgroup.Gamma0 N, ∀ z : ℍ,
      branchSL p hp.pos none • (g • z) = h • (branchSL p hp.pos none • z) := by
  let G := includePrimeLevel N p g
  have hfix := (heckeIntersection_mem_iff_fixed N p hp hpN G).mp
    (includePrimeLevel_mem_intersection N p g)
  obtain ⟨h,hh,hact⟩ := actual_branch_action_factor N p hp hpN G G.property none
  refine ⟨⟨h,hh⟩, fun z => ?_⟩
  have hz := hact z
  change branchSL p hp.pos none • (g • z) =
    h • (branchSL p hp.pos (branchImage N p hp hpN G G.property none) • z) at hz
  simpa only [hfix] using hz

def secondProjection (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Gamma0OrbitSpace (N*p) → Gamma0OrbitSpace N :=
  Quotient.lift (fun z : ℍ => orbitProjection N (branchSL p hp.pos none • z)) (by
    intro z w hzw
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hzw
    obtain ⟨h,hh⟩ := primeLevel_dilation_deck N p hp hpN g
    calc
      _ = orbitProjection N (branchSL p hp.pos none • (g • w)) :=
        congrArg (fun u : ℍ => orbitProjection N (branchSL p hp.pos none • u)) hg.symm
      _ = orbitProjection N (h • (branchSL p hp.pos none • w)) := congrArg (orbitProjection N) (hh w)
      _ = _ := orbitProjection_smul N h _)

theorem secondProjection_projection (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) (z : ℍ) :
    secondProjection N p hp hpN (orbitProjection (N*p) z) =
      orbitProjection N (branchSL p hp.pos none • z) := rfl

theorem secondProjection_measurable (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Measurable (secondProjection N p hp hpN) := by
  apply measurable_from_quotient.mpr
  exact (orbitProjection_measurable N).comp (continuous_const_smul (branchSL p hp.pos none)).measurable

/-- Whole upper-half-plane volume preservation of the actual inducing
matrix. This theorem does not assert a quotient pushforward relation. -/
theorem dilation_wholeH_measurePreserving (p : ℕ) (hp : 0 < p) :
    MeasurePreserving (fun z : ℍ => branchSL p hp none • z)
      (volume : Measure ℍ) (volume : Measure ℍ) := by
  change MeasurePreserving (fun z : ℍ => SpecialLinearGroup.mapGL ℝ (branchSL p hp none) • z) _ _
  exact measurePreserving_smul _ _

/-- Each actual finite cover representative reaches precisely the
corresponding native physical Hecke branch under the second projection. -/
theorem secondProjection_cover_branch (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (j : Branch p) (z : ℍ) :
    secondProjection N p hp hpN (orbitProjection (N*p) (coverAction N p hp hpN j z)) =
      orbitProjection N (branchSL p hp.pos j • z) := by
  let g := coverRepresentative N p hp hpN j
  obtain ⟨h,hh,hact⟩ := actual_branch_action_factor N p hp hpN g g.property none
  have hbranch : branchPermutation N p hp hpN g g.property none = j :=
    coverRepresentative_branch N p hp hpN j
  rw [secondProjection_projection]
  change orbitProjection N (branchSL p hp.pos none • (g • z)) = _
  rw [hact z, hbranch]
  exact orbitProjection_smul N ⟨h,hh⟩ _

/-- Exact physical Hecke trace as the sum of actual second-projection
values over the actual finite cover branches; no measure is assumed. -/
theorem nativeHecke_correspondence (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (z : ℍ) :
    nativeHecke p hp.pos (testLift N U) z =
      letI : NeZero p := ⟨hp.ne_zero⟩
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ * ∑ j : Branch p,
        U (secondProjection N p hp hpN (orbitProjection (N*p) (coverAction N p hp hpN j z))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ * (∑ j : Branch p, testLift N U (branchSL p hp.pos j • z)) = _
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg U (secondProjection_cover_branch N p hp hpN j z).symm

end
end ImbalancedChen.Part3.ActualHeckeSecondProjection20261026b
