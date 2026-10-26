import ImbalancedChen.Part3InfinityZeroActualFiberFourier

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

Partition the ORIGINAL signed GammaInfinity-left-coset quotient by its
nonnegative lower-right denominator. Negative rows are explicitly moved
to their actual central-negative representatives. The exceptional zero
fiber exists exactly at level one, where it is a single actual S class.
No canonical-series replacement, assumed dictionary, or sum is used.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.InfinityZeroActualAllDenominatorAssembly20261026b

open Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.InfinityZeroActualDenominatorFiber20261026a
open ImbalancedChen.Part3.InfinityZeroActualFiberFourier20261026a
open ImbalancedChen.Part3.ActualCompactPoincareFourier20261025a
open ImbalancedChen.Part3.CompactParabolicNormalIndex20261025a
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open Set

/-- The central negative is still an actual matrix at the original level. -/
def centralNegative (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    CongruenceSubgroup.Gamma0 N :=
  ⟨-(g : SL(2, ℤ)), by
    apply (gamma0_membership_signed_bottomRow N (g : SL(2, ℤ)) (-(g : SL(2, ℤ)))
      (Or.inr (bottomRow_neg _))).mpr g.property⟩

/-- Negative rows represent the SAME actual parabolic left coset. -/
theorem centralNegative_same_coset (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (Quotient.mk'' (centralNegative N g) : GammaInfinityCosets N) = Quotient.mk'' g := by
  apply Quotient.sound
  apply (bottomRowClass_eq_iff_orbit N (centralNegative N g) g).mp
  exact Quotient.sound (Or.inr (bottomRow_neg _))

/-- The absolute lower-right entry is independent of an actual representative. -/
theorem lowerRight_natAbs_eq_of_coset_eq (N : ℕ)
    (g h : CongruenceSubgroup.Gamma0 N)
    (heq : (Quotient.mk'' g : GammaInfinityCosets N) = Quotient.mk'' h) :
    ((g : SL(2, ℤ)) 1 1).natAbs = ((h : SL(2, ℤ)) 1 1).natAbs := by
  have hr := congrArg (parabolicRowMap N) heq
  have hs : bottomRow (g : SL(2, ℤ)) = bottomRow (h : SL(2, ℤ)) ∨
      bottomRow (g : SL(2, ℤ)) = -bottomRow (h : SL(2, ℤ)) := Quotient.exact hr
  rcases hs with hs | hs
  · exact congrArg Int.natAbs (congrFun hs 1)
  · have hd : (g : SL(2, ℤ)) 1 1 = -(h : SL(2, ℤ)) 1 1 := congrFun hs 1
    simp only [hd, Int.natAbs_neg]

/-- Every original signed coset has an ACTUAL nonnegative denominator
representative. A negative representative is changed by the actual center. -/
theorem exists_nonnegative_representative (N : ℕ) (q : GammaInfinityCosets N) :
    ∃ (g : CongruenceSubgroup.Gamma0 N) (d : ℕ),
      Quotient.mk'' g = q ∧ (g : SL(2, ℤ)) 1 1 = (d : ℤ) := by
  refine Quotient.inductionOn q ?_
  intro g
  by_cases hg : 0 ≤ (g : SL(2, ℤ)) 1 1
  · refine ⟨g, ((g : SL(2, ℤ)) 1 1).toNat, rfl, ?_⟩
    exact (Int.toNat_of_nonneg hg).symm
  · refine ⟨centralNegative N g, (-(g : SL(2, ℤ)) 1 1).toNat,
      centralNegative_same_coset N g, ?_⟩
    change -(g : SL(2, ℤ)) 1 1 = _
    have hneg : 0 ≤ -(g : SL(2, ℤ)) 1 1 := by omega
    exact (Int.toNat_of_nonneg hneg).symm

theorem denominator_fibers_disjoint (N d e : ℕ)
    (q : ZeroDenominatorCosets N d) (r : ZeroDenominatorCosets N e)
    (hqr : q.1 = r.1) : d = e := by
  obtain ⟨g, hg, hd⟩ := q.property
  obtain ⟨h, hh, he⟩ := r.property
  have habs := lowerRight_natAbs_eq_of_coset_eq N g h (hg.trans (hqr.trans hh.symm))
  simpa only [hd, he, Int.natAbs_natCast] using habs

/-- All denominator fibers, INCLUDING zero, form a genuine disjoint
partition of the original actual parabolic quotient. -/
def allDenominatorCosetEquiv (N : ℕ) :
    (Σ d : ℕ, ZeroDenominatorCosets N d) ≃ GammaInfinityCosets N :=
  Equiv.ofBijective (fun p => p.2.1) ⟨by
    rintro ⟨d, q⟩ ⟨e, r⟩ heq
    have hde := denominator_fibers_disjoint N d e q r heq
    subst e
    have hqr : q = r := Subtype.ext heq
    cases hqr
    rfl, by
    intro q
    obtain ⟨g, d, hg, hd⟩ := exists_nonnegative_representative N q
    exact ⟨⟨d, q, g, hg, hd⟩, rfl⟩⟩

/-- A zero lower-right entry forces level one, by the actual determinant
and level divisibility. This also rules out a hidden zero class at N>1. -/
theorem level_eq_one_of_zero_denominator (N : ℕ) (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) (hd : (g : SL(2, ℤ)) 1 1 = 0) : N = 1 := by
  have hdet : -((g : SL(2, ℤ)) 0 1) * (g : SL(2, ℤ)) 1 0 = 1 := by
    have h := (g : SL(2, ℤ)).det_coe
    simpa only [Matrix.det_fin_two, hd, mul_zero, zero_sub, neg_mul] using h
  have hc : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 :=
    (gamma0_mem_iff_level_dvd_c N (g : SL(2, ℤ))).mp g.property
  have hone : (N : ℤ) ∣ 1 := by
    rw [← hdet]
    exact dvd_mul_of_dvd_right hc _
  obtain ⟨k, hk⟩ := hone
  have hunit := Int.eq_one_or_neg_one_of_mul_eq_one' hk.symm
  rcases hunit with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

def exceptionalWeylGamma : CongruenceSubgroup.Gamma0 1 :=
  ⟨ModularGroup.S, by rw [gamma0_mem_iff_level_dvd_c]; simp⟩

def exceptionalWeylCoset : ZeroDenominatorCosets 1 0 :=
  ⟨Quotient.mk'' exceptionalWeylGamma,
    exceptionalWeylGamma, rfl, by simp [exceptionalWeylGamma, ModularGroup.S]⟩

/-- Exactly one class, rather than two central signs, at d=0 and N=1. -/
theorem zero_denominator_class_unique (q : ZeroDenominatorCosets 1 0) :
    q = exceptionalWeylCoset := by
  obtain ⟨g, hg, hd⟩ := q.property
  have hdet : -((g : SL(2, ℤ)) 0 1) * (g : SL(2, ℤ)) 1 0 = 1 := by
    have h := (g : SL(2, ℤ)).det_coe
    simpa only [Matrix.det_fin_two, hd, Int.cast_zero, mul_zero, zero_sub, neg_mul] using h
  have hc : (g : SL(2, ℤ)) 1 0 = 1 ∨ (g : SL(2, ℤ)) 1 0 = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have hr : bottomRow (g : SL(2, ℤ)) = bottomRow (exceptionalWeylGamma : SL(2, ℤ)) ∨
      bottomRow (g : SL(2, ℤ)) = -bottomRow (exceptionalWeylGamma : SL(2, ℤ)) := by
    rcases hc with hc | hc
    · left
      funext j
      fin_cases j <;> simp [bottomRow, exceptionalWeylGamma, ModularGroup.S, hc, hd]
    · right
      funext j
      fin_cases j <;> simp [bottomRow, exceptionalWeylGamma, ModularGroup.S, hc, hd]
  apply Subtype.ext
  exact hg.symm.trans (Quotient.sound ((bottomRowClass_eq_iff_orbit 1 g
    exceptionalWeylGamma).mp (Quotient.sound hr)))

theorem zero_denominator_isEmpty (N : ℕ) (hN : 0 < N) (hN1 : N ≠ 1) :
    IsEmpty (ZeroDenominatorCosets N 0) := by
  refine ⟨fun q => ?_⟩
  obtain ⟨g, _, hd⟩ := q.property
  exact hN1 (level_eq_one_of_zero_denominator N hN g (by simpa using hd))

/-- Grouping the ORIGINAL sum is justified by its already proved
absolute convergence at the actual scaled point, before sigma grouping. -/
theorem actualPoincare_zeroChart_eq_all_fibers (N : ℕ) (hN : 0 < N)
    (m : ℤ) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (z : UpperHalfPlane) :
    actualCompactPoincare N m ψ (zeroSL N hN • z) =
      ∑' d : ℕ, actualZeroFiber N hN d m ψ z := by
  let w := zeroSL N hN • z
  have hw : horizontalPoint w.im w.im_pos w.re = w := by
    apply UpperHalfPlane.ext
    ext <;> rfl
  have hs := (actualCompactPoincare_norm_summable N w.im w.im_pos m ψ hψ hcψ hposψ w.re).of_norm
  rw [hw] at hs
  have hgroup := (allDenominatorCosetEquiv N).summable_iff.mpr hs
  rw [actualCompactPoincare, ← (allDenominatorCosetEquiv N).tsum_eq, hgroup.tsum_sigma]
  rfl

end ImbalancedChen.Part3.InfinityZeroActualAllDenominatorAssembly20261026b
