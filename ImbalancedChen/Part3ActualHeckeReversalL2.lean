import ImbalancedChen.Part3ActualHeckeReversalMeasure
import ImbalancedChen.Part3ActualHeckeSecondL2
import Mathlib.Analysis.InnerProductSpace.LinearMap

-- SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT, 2026-10-27.
-- Native L2 pullback by the actual partial Atkin-Lehner involution.
-- It exchanges the original two correspondence projections, hence proves
-- their exact Hermitian pairing swap without a Hecke SA hypothesis.

namespace ImbalancedChen.Part3.ActualHeckeReversalL220261027
noncomputable section
open MeasureTheory
open ActualHeckeReversalMeasure20261027 ActualHeckeReversalInvolution20261026b
open ActualHeckeForgetL220261026b ActualHeckeSecondL220261026b
open ActualHeckeForgetCoverMeasure20261026b ActualHeckeSecondProjection20261026b
open Gamma0QuotientCellPushforward20261025a

variable (N p : ℕ) [NeZero (N*p)] (hp : p.Prime) (hpN : ¬ p ∣ N)

def reversalL2 :
    Lp ℂ 2 (carrierPushforward (N*p)) →ₗᵢ[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (quotientReversal N p hp hpN)
    (quotientReversal_measurePreserving N p hp hpN)

theorem reversalL2_coe (F : Lp ℂ 2 (carrierPushforward (N*p))) :
    (reversalL2 N p hp hpN F : Gamma0OrbitSpace (N*p) → ℂ) =ᵐ[carrierPushforward (N*p)]
      F ∘ quotientReversal N p hp hpN :=
  Lp.coeFn_compMeasurePreserving F (quotientReversal_measurePreserving N p hp hpN)

theorem reversalL2_involutive : Function.Involutive (reversalL2 N p hp hpN) := by
  intro F
  apply Lp.ext
  have hcomp := (quotientReversal_measurePreserving N p hp hpN).quasiMeasurePreserving.ae_eq_comp
    (reversalL2_coe N p hp hpN F)
  filter_upwards [reversalL2_coe N p hp hpN (reversalL2 N p hp hpN F),hcomp] with q houter hinner
  change _ = F q
  calc
    _ = reversalL2 N p hp hpN F (quotientReversal N p hp hpN q) := houter
    _ = F (quotientReversal N p hp hpN (quotientReversal N p hp hpN q)) := hinner
    _ = F q := congrArg F (quotientReversal_involutive N p hp hpN q)

-- Surjectivity here is constructive: the same actual reversal is inverse.
def reversalL2Equiv :
    Lp ℂ 2 (carrierPushforward (N*p)) ≃ₗᵢ[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) :=
  { reversalL2 N p hp hpN with
    invFun := reversalL2 N p hp hpN
    left_inv := reversalL2_involutive N p hp hpN
    right_inv := reversalL2_involutive N p hp hpN }

variable [NeZero N] (hN : 0 < N)

-- Every representative equality is pulled back through an independently
-- proved measure-preserving map before using the pointwise projection law.
theorem reversalL2_firstPullback (U : Lp ℂ 2 (carrierPushforward N)) :
    reversalL2 N p hp hpN (rawPullback N p hp hpN U) =
      rawSecondPullbackLinear N p hN hp hpN U := by
  apply Lp.ext
  have hcomp := (quotientReversal_measurePreserving N p hp hpN).quasiMeasurePreserving.ae_eq_comp
    (rawPullback_coe N p hp hpN U)
  filter_upwards [reversalL2_coe N p hp hpN (rawPullback N p hp hpN U),
    hcomp,rawSecondPullback_coe N p hN hp hpN U] with q houter hinner hsecond
  calc
    _ = rawPullback N p hp hpN U (quotientReversal N p hp hpN q) := houter
    _ = U (forgetPrimeLevel N p (quotientReversal N p hp hpN q)) := hinner
    _ = U (secondProjection N p hp hpN q) := congrArg U (firstProjection_reversal N p hp hpN q)
    _ = _ := hsecond.symm

theorem reversalL2_secondPullback (U : Lp ℂ 2 (carrierPushforward N)) :
    reversalL2 N p hp hpN (rawSecondPullbackLinear N p hN hp hpN U) =
      rawPullback N p hp hpN U := by
  rw [← reversalL2_firstPullback N p hp hpN hN U]
  exact reversalL2_involutive N p hp hpN (rawPullback N p hp hpN U)

-- Actual inverse-branch correspondence pairing symmetry, on the native
-- canonical quotient L2 spaces with no whole-operator SA assumption.
theorem rawPullback_inner_swap (U V : Lp ℂ 2 (carrierPushforward N)) :
    inner ℂ (rawPullback N p hp hpN U) (rawSecondPullbackLinear N p hN hp hpN V) =
      inner ℂ (rawSecondPullbackLinear N p hN hp hpN U) (rawPullback N p hp hpN V) := by
  calc
    _ = inner ℂ (reversalL2 N p hp hpN (rawPullback N p hp hpN U))
        (reversalL2 N p hp hpN (rawSecondPullbackLinear N p hN hp hpN V)) :=
      ((reversalL2 N p hp hpN).inner_map_map _ _).symm
    _ = _ := by
      rw [reversalL2_firstPullback N p hp hpN hN U,
        reversalL2_secondPullback N p hp hpN hN V]

end
end ImbalancedChen.Part3.ActualHeckeReversalL220261027
