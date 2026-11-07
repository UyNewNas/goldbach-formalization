import ImbalancedChen.Part3PrimeCrossCuspHeightBound
import ImbalancedChen.Part3Gamma0ActualHighCuspTail
import ImbalancedChen.Part3ActualFrickeQuotientMeasure

/-! Actual high quotient neighborhoods of infinity and normalized Fricke
zero are disjoint at every strict height Y>=1. Same-chart identifications
are exactly the actual integer-translation/parabolic decks. The claims
use original Gamma0 orbit projection and native quotient Fricke action.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.PrimeCrossCuspHeightBound20261026b
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly
open ImbalancedChen.Part3.Gamma0ParabolicBottomRow20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ActualHighCuspTail20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b

namespace ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b

/-- On one strict high chart, the actual spatial orbit relation is
exactly integral horizontal translation, including the trivial central sign. -/
theorem high_projection_eq_iff_translation (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (z w : UpperHalfPlane) (hz : Y < z.im) (hw : Y < w.im) :
    orbitProjection N z = orbitProjection N w ↔ ∃ k : ℤ, z = translate k w := by
  constructor
  · intro hq
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hq)
    have hc : (g : SL(2, ℤ)) 1 0 = 0 := by
      by_contra hne
      have hbound := im_smul_mul_im_le_one (g : SL(2, ℤ)) hne w
      change (g • w).im * w.im ≤ 1 at hbound
      rw [hg] at hbound
      have hz1 := hY.trans_lt hz
      have hw1 := hY.trans_lt hw
      have hprod : 1 < z.im * w.im := hw1.trans
        (by simpa only [one_mul] using mul_lt_mul_of_pos_right hz1 w.im_pos)
      exact (not_lt_of_ge hbound) hprod
    obtain ⟨k, hk⟩ := parabolic_action_integer N (⟨g, hc⟩ : gammaInfinity N)
    exact ⟨k, hg.symm.trans (hk w)⟩
  · rintro ⟨k, rfl⟩
    exact orbitProjection_smul N
      (⟨ModularGroup.T ^ k, translation_mem_gamma0 N k⟩ : CongruenceSubgroup.Gamma0 N) w

/-- The same exact parabolic-deck statement in the normalized zero chart,
using the genuine involutive quotient Fricke map. -/
theorem fricke_high_projection_eq_iff_translation (N : ℕ) (hN : 0 < N)
    (Y : ℝ) (hY : 1 ≤ Y) (z w : UpperHalfPlane) (hz : Y < z.im) (hw : Y < w.im) :
    orbitProjection N (frickeSL N hN • z) = orbitProjection N (frickeSL N hN • w) ↔
      ∃ k : ℤ, z = translate k w := by
  constructor
  · intro hq
    have he := congrArg (quotientFricke N hN) hq
    simp only [quotientFricke_projection, frickeSL_action_involutive N hN] at he
    exact (high_projection_eq_iff_translation N Y hY z w hz hw).mp he
  · intro h
    have he := (high_projection_eq_iff_translation N Y hY z w hz hw).mpr h
    have hq := congrArg (quotientFricke N hN) he
    simpa only [quotientFricke_projection] using hq

theorem high_cross_projection_ne {p : ℕ} (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) (z w : UpperHalfPlane) (hz : Y < z.im) (hw : Y < w.im) :
    orbitProjection p z ≠ orbitProjection p (frickeSL p hp.pos • w) := by
  intro hq
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hq)
  have hbound := gamma0_fricke_height_product hp g w
  rw [hg] at hbound
  have hz1 := hY.trans_lt hz
  have hw1 := hY.trans_lt hw
  have hprod : 1 < z.im * w.im := hw1.trans
    (by simpa only [one_mul] using mul_lt_mul_of_pos_right hz1 w.im_pos)
  exact (not_lt_of_ge hbound) hprod

def infinityHighNeighborhood (N : ℕ) (Y : ℝ) : Set (Gamma0OrbitSpace N) :=
  orbitProjection N '' strictHeightHalfSpace Y

def zeroHighNeighborhood (p : ℕ) (hp : p.Prime) (Y : ℝ) : Set (Gamma0OrbitSpace p) :=
  (fun z : UpperHalfPlane => orbitProjection p (frickeSL p hp.pos • z)) '' strictHeightHalfSpace Y

/-- Literal two-cusp neighborhoods are disjoint in the actual quotient,
with no pairing or disjoint-support assumption. The threshold Y=1 is included. -/
theorem prime_high_neighborhoods_disjoint {p : ℕ} (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    Disjoint (infinityHighNeighborhood p Y) (zeroHighNeighborhood p hp Y) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
  exact high_cross_projection_ne hp Y hY z w hz hw he.symm

end ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
