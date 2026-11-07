import ImbalancedChen.Part3ActualHeckeBranchTransitivity
import ImbalancedChen.Part3ActualPrimeHeckeRealBranch
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod
import ImbalancedChen.Part3Gamma0QuotientCellPushforward
import Mathlib.GroupTheory.OrderOfElement

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
For EVERY original normalized integral rational-cusp frame, the actual
p+1 normalized-real Hecke branches admit a COMMON POSITIVE INTEGER period
modulo actual Gamma0(N). The original frame's explicit width-multiple unit
deck is used; its true finite branch permutation supplies the period by
its finite order. The branch deck factors and the quotient branch periods
are derived from actual factorization, not an assumed finite correspondence
or period. No all-frame cusp preservation, frame affine factorization,
constant-term transfer, Hecke SA or spectral conclusion is asserted yet.
-/

namespace ImbalancedChen.Part3.ActualHeckeAllFrameCommonPeriod20261026b
noncomputable section
open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeBranchPermutation20261026b
open ActualHeckeBranchTransitivity20261026b ActualPrimeHeckeRealBranch20261026b
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open Gamma0QuotientCellPushforward20261025a ActualCuspFourierSectionSourceOnly

variable (N p : ℕ) (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

/-- The literal ORIGINAL width-multiple stabilizer implementing a unit
translation in this actual normalized frame. -/
def frameUnitDeck (g : SL(2, ℤ)) : CongruenceSubgroup.Gamma0 N :=
  ⟨g*ModularGroup.T^((cuspWidth N g : ℤ)*1)*g⁻¹,width_multiple_mem_gamma0 N hN g 1⟩

theorem frameUnitDeck_action (g : SL(2, ℤ)) (z : ℍ) :
    frameUnitDeck N hN g • (normalizedScaling N hN g • z) =
      normalizedScaling N hN g • ((1 : ℝ)+ᵥ z) := by
  simpa only [frameUnitDeck,ModularGroup.modular_T_zpow_smul,Int.cast_one] using
    normalizedScaling_deck_action N hN g 1 z

theorem frameUnitDeck_pow_action (g : SL(2, ℤ)) (n : ℕ) (z : ℍ) :
    (frameUnitDeck N hN g)^n • (normalizedScaling N hN g • z) =
      normalizedScaling N hN g • ((n : ℝ)+ᵥ z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,mul_smul,frameUnitDeck_action,ih]
    simp only [Nat.cast_add,Nat.cast_one,vadd_vadd]

private theorem branchImage_one (j : Branch p) :
    branchImage N p hp hpN 1 (1 : CongruenceSubgroup.Gamma0 N).property j=j := by
  obtain ⟨a,ha,heq⟩ := branchImage_factor N p hp hpN 1 (1 : CongruenceSubgroup.Gamma0 N).property j
  have hbranch := branch_eq_of_left_integral p hp j
    (branchImage N p hp hpN 1 (1 : CongruenceSubgroup.Gamma0 N).property j) a
      (by simpa only [Subgroup.coe_one,coe_one,Matrix.mul_one] using heq)
  exact hbranch.symm

/-- Powers of the ACTUAL right branch action equal powers of its ACTUAL
finite permutation; anti-composition agrees on powers of one element. -/
theorem branchImage_pow (a : CongruenceSubgroup.Gamma0 N) (n : ℕ) (j : Branch p) :
    branchImage N p hp hpN (a^n) (a^n).property j =
      (branchPermutation N p hp hpN a a.property)^n j := by
  induction n generalizing j with
  | zero => simpa using branchImage_one N p hp hpN j
  | succ n ih =>
    rw [pow_succ',branchImage_mul,ih,pow_succ]
    rfl

def frameBranchPeriod (g : SL(2, ℤ)) : ℕ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  orderOf (branchPermutation N p hp hpN (frameUnitDeck N hN g) (frameUnitDeck N hN g).property)

theorem frameBranchPeriod_pos (g : SL(2, ℤ)) : 0 < frameBranchPeriod N p hN hp hpN g := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact orderOf_pos _

theorem frame_branch_power_fixed (g : SL(2, ℤ)) (j : Branch p) :
    branchImage N p hp hpN ((frameUnitDeck N hN g)^(frameBranchPeriod N p hN hp hpN g))
      ((frameUnitDeck N hN g)^(frameBranchPeriod N p hN hp hpN g)).property j=j := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [branchImage_pow]
  change ((branchPermutation N p hp hpN (frameUnitDeck N hN g)
    (frameUnitDeck N hN g).property)^orderOf (branchPermutation N p hp hpN
      (frameUnitDeck N hN g) (frameUnitDeck N hN g).property)) j=j
  rw [pow_orderOf_eq_one]
  rfl

/-- For every physical branch a genuine original Gamma0 deck pays the
same positive integer input-frame translation, including all widths. -/
theorem frame_branch_common_period_deck (g : SL(2, ℤ)) (j : Branch p) :
    ∃ a : CongruenceSubgroup.Gamma0 N, ∀ z : ℍ,
      branchSL p hp.pos j • (normalizedScaling N hN g •
        ((frameBranchPeriod N p hN hp hpN g : ℝ)+ᵥ z)) =
          a • (branchSL p hp.pos j • (normalizedScaling N hN g • z)) := by
  let G := (frameUnitDeck N hN g)^(frameBranchPeriod N p hN hp hpN g)
  obtain ⟨a,ha,hact⟩ := actual_branch_action_factor N p hp hpN G G.property j
  refine ⟨⟨a,ha⟩,fun z => ?_⟩
  have hz := hact (normalizedScaling N hN g • z)
  change branchSL p hp.pos j •
    ((frameUnitDeck N hN g)^(frameBranchPeriod N p hN hp hpN g) • (normalizedScaling N hN g • z)) =
      a • (branchSL p hp.pos (branchImage N p hp hpN
        ((frameUnitDeck N hN g)^(frameBranchPeriod N p hN hp hpN g))
          ((frameUnitDeck N hN g)^(frameBranchPeriod N p hN hp hpN g)).property j) •
            (normalizedScaling N hN g • z)) at hz
  rw [frameUnitDeck_pow_action,frame_branch_power_fixed] at hz
  exact hz

/-- Actual quotient branch periodicity at every physical height, with
no restriction on the original quotient function or its spectral type. -/
theorem frame_branch_quotient_periodic (g : SL(2, ℤ)) (j : Branch p)
    (U : Gamma0OrbitSpace N → ℂ) (y : ℝ) (hy : 0 < y) :
    Function.Periodic (fun x => U (orbitProjection N
      (branchSL p hp.pos j • (normalizedScaling N hN g • horizontal y hy x))))
        (frameBranchPeriod N p hN hp hpN g : ℝ) := by
  obtain ⟨a,ha⟩ := frame_branch_common_period_deck N p hN hp hpN g j
  intro x
  have hshift : horizontal y hy (x+(frameBranchPeriod N p hN hp hpN g : ℝ)) =
      (frameBranchPeriod N p hN hp hpN g : ℝ)+ᵥ horizontal y hy x := by
    apply UpperHalfPlane.ext
    simp [horizontal,UpperHalfPlane.coe_vadd,add_comm]
  rw [hshift,ha,orbitProjection_smul]

end
end ImbalancedChen.Part3.ActualHeckeAllFrameCommonPeriod20261026b
