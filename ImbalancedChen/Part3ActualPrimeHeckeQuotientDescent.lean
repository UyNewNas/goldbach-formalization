import ImbalancedChen.Part3ActualPrimeHeckeRealBranch
import ImbalancedChen.Part3ActualPoincareSpectralCoefficient

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The native normalized prime-Hecke trace is genuinely Gamma0(N) invariant
when p is prime and does not divide N. Invariance is derived from the
actual branch permutation and actual native action factors. Therefore an
arbitrary original quotient function produces an actual new quotient
function. No Hecke-automorphy premise, quotient L2 bound, or spectral
realization is inserted as an assumption.
-/

namespace ImbalancedChen.Part3.ActualPrimeHeckeQuotientDescent20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualPrimeHeckeRealBranch20261026b ActualPoincareSpectralCoefficient20261026a
open Gamma0QuotientCellPushforward20261025a

def nativeHecke (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (z : ℍ) : ℂ :=
  letI : NeZero p := ⟨hp.ne'⟩
  (Real.sqrt (p : ℝ) : ℂ)⁻¹ * ∑ j : Branch p, f (branchSL p hp j • z)

theorem nativeHecke_continuous (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ)
    (hf : Continuous f) : Continuous (nativeHecke p hp f) := by
  letI : NeZero p := ⟨hp.ne'⟩
  apply continuous_const.mul
  exact continuous_finset_sum _ (fun j hj => hf.comp (continuous_const_smul _))

/-- Original Gamma invariance of f and the proved actual permutation
imply Gamma invariance of its physical prime-Hecke trace. -/
theorem nativeHecke_gamma_invariant (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ℍ → ℂ)
    (hf : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, f (g • z) = f z)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    nativeHecke p hp.pos f (g • z) = nativeHecke p hp.pos f z := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  change (Real.sqrt (p : ℝ) : ℂ)⁻¹ * (∑ j : Branch p, f (branchSL p hp.pos j • (g • z))) =
    (Real.sqrt (p : ℝ) : ℂ)⁻¹ * ∑ j : Branch p, f (branchSL p hp.pos j • z)
  congr 1
  calc
    _ = ∑ j : Branch p, f (branchSL p hp.pos (branchPermutation N p hp hpN g hg j) • z) := by
      apply Finset.sum_congr rfl
      intro j hj
      obtain ⟨h, hh, haction⟩ := actual_branch_action_factor N p hp hpN g hg j
      rw [haction z, hf h hh]
    _ = _ := (branchPermutation N p hp hpN g hg).sum_comp
      (fun j => f (branchSL p hp.pos j • z))

def quotientHecke (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) : Gamma0OrbitSpace N → ℂ :=
  Quotient.lift (nativeHecke p hp.pos (testLift N U)) (by
    intro z w hzw
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hzw
    calc
      nativeHecke p hp.pos (testLift N U) z =
          nativeHecke p hp.pos (testLift N U) (g • w) := congrArg _ hg.symm
      _ = nativeHecke p hp.pos (testLift N U) w :=
        nativeHecke_gamma_invariant N p hp hpN (testLift N U)
          (fun h hh u => testLift_invariant N U ⟨h,hh⟩ u) g g.property w)

/-- The actual descended quotient function has exactly the native
physical trace as its lift, without an automorphy assumption. -/
theorem quotientHecke_lift (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) :
    testLift N (quotientHecke N p hp hpN U) = nativeHecke p hp.pos (testLift N U) := rfl

theorem quotientHecke_lift_continuous (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U)) :
    Continuous (testLift N (quotientHecke N p hp hpN U)) := by
  rw [quotientHecke_lift]
  exact nativeHecke_continuous p hp.pos (testLift N U) hU

end
end ImbalancedChen.Part3.ActualPrimeHeckeQuotientDescent20261026b
