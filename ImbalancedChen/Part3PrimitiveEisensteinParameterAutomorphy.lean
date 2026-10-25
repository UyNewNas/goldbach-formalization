import ImbalancedChen.Part3PrimitiveEisensteinParameterAnalytic
import ImbalancedChen.Part3PrimitiveRealEisensteinAutomorphy

/-!
# Modular automorphy of the actual complex-parameter primitive Eisenstein family

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

The existing literal integer-pair permutation and real-seed Mobius
identity at exponent one identify the actual positive bases themselves.
Applying exp(s*log(base)) proves the genuine complex-s summand identity,
including the logarithmic factor in its actual first s derivative.
Reindexing the proved absolutely convergent primitive sums then gives
full SL(2,Z) automorphy throughout Re(s)>1, both for the series and its
parameter derivative. The resulting functions of s are analytic and agree
on that same initial half plane.

There is no coordinate C2 chain or assumed automorphy supplier for the
complex family, and no continuation to Re(s)=1/2 is asserted.
-/

namespace ImbalancedChen.Part3.PrimitiveEisensteinParameterAutomorphy

noncomputable section

open Complex UpperHalfPlane EisensteinSeries Matrix Set
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic

/-- The already constructed permutation acts on the actual integer pair
by ordinary row-vector multiplication by the modular matrix. -/
theorem primitivePairEquiv_value (gamma : SL(2, ℤ)) (v : PrimitivePair) :
    ((primitivePairEquiv gamma) v).1 =
      v.1 ᵥ* (gamma : Matrix (Fin 2) (Fin 2) ℤ) := by
  simp [primitivePairEquiv, EisensteinSeries.gammaSetEquiv]

/-- Exact invariance of the positive base after the existing primitive
integer-pair relabelling. Exponent one extracts it from the real identity. -/
theorem positiveBase_SL2_apply (gamma : SL(2, ℤ)) (z : ℍ) (v : PrimitivePair) :
    positiveBase (gamma • z) v = positiveBase z ((primitivePairEquiv gamma) v) := by
  have hleft : positiveBase (gamma • z) v = seed 1 (gamma • z) v.1 := by
    simpa only [Real.rpow_one] using positiveBase_rpow_eq_seed 1 (gamma • z) v
  have hright : positiveBase z ((primitivePairEquiv gamma) v) =
      seed 1 z (v.1 ᵥ* (gamma : Matrix (Fin 2) (Fin 2) ℤ)) := by
    simpa only [Real.rpow_one, primitivePairEquiv_value] using
      positiveBase_rpow_eq_seed 1 z ((primitivePairEquiv gamma) v)
  exact hleft.trans ((seed_SL2_apply 1 v.1 gamma z).trans hright.symm)

/-- Every actual complex-s summand transforms by that same literal
integer permutation. The logarithm is applied only after exact base equality. -/
theorem complexSeed_SL2_apply (s : ℂ) (gamma : SL(2, ℤ)) (z : ℍ) (v : PrimitivePair) :
    complexSeed (gamma • z) v s = complexSeed z ((primitivePairEquiv gamma) v) s := by
  unfold complexSeed
  rw [positiveBase_SL2_apply gamma z v]

/-- The actual first parameter derivative has the identical permutation
law, including its log(base) factor. -/
theorem complexSeedDerivative_SL2_apply
    (s : ℂ) (gamma : SL(2, ℤ)) (z : ℍ) (v : PrimitivePair) :
    complexSeedDerivative (gamma • z) v s =
      complexSeedDerivative z ((primitivePairEquiv gamma) v) s := by
  unfold complexSeedDerivative
  rw [positiveBase_SL2_apply gamma z v, complexSeed_SL2_apply s gamma z v]

/-- Modular automorphy of the actual absolutely convergent complex
primitive Eisenstein sum, with its original classical 1/2 normalization. -/
theorem primitiveComplexEisenstein_SL2_invariant
    (s : ℂ) (hs : 1 < s.re) (gamma : SL(2, ℤ)) (z : ℍ) :
    primitiveComplexEisenstein s (gamma • z) = primitiveComplexEisenstein s z := by
  have hsum : (∑' v : PrimitivePair, complexSeed (gamma • z) v s) =
      ∑' v : PrimitivePair, complexSeed z v s := by
    calc
      _ = ∑' v : PrimitivePair, complexSeed z ((primitivePairEquiv gamma) v) s :=
        tsum_congr (fun v => complexSeed_SL2_apply s gamma z v)
      _ = ∑' v : PrimitivePair, complexSeed z v s :=
        (primitivePairEquiv gamma).tsum_eq (fun v : PrimitivePair => complexSeed z v s)
  have habs : Summable (fun v : PrimitivePair => complexSeed z v s) :=
    complexSeed_summable z s hs
  have habs_transformed : Summable (fun v : PrimitivePair => complexSeed (gamma • z) v s) :=
    complexSeed_summable (gamma • z) s hs
  simpa only [primitiveComplexEisenstein] using congrArg ((1 / 2 : ℂ) * ·) hsum

/-- The convergent derivative sum is invariant by the same actual
primitive-pair reindexing, rather than by assuming an invariant derivative. -/
theorem primitive_parameter_derivative_tsum_SL2_invariant
    (s : ℂ) (hs : 1 < s.re) (gamma : SL(2, ℤ)) (z : ℍ) :
    (∑' v : PrimitivePair, complexSeedDerivative (gamma • z) v s) =
      ∑' v : PrimitivePair, complexSeedDerivative z v s := by
  have habs : Summable (fun v : PrimitivePair => complexSeedDerivative z v s) :=
    complexSeedDerivative_summable z s hs
  calc
    _ = ∑' v : PrimitivePair, complexSeedDerivative z ((primitivePairEquiv gamma) v) s :=
      tsum_congr (fun v => complexSeedDerivative_SL2_apply s gamma z v)
    _ = ∑' v : PrimitivePair, complexSeedDerivative z v s :=
      (primitivePairEquiv gamma).tsum_eq (fun v : PrimitivePair => complexSeedDerivative z v s)

/-- The actual complex derivative of the normalized primitive series
retains full modular automorphy on the initial half plane. -/
theorem deriv_primitiveComplexEisenstein_SL2_invariant
    (s : ℂ) (hs : 1 < s.re) (gamma : SL(2, ℤ)) (z : ℍ) :
    deriv (fun w : ℂ => primitiveComplexEisenstein w (gamma • z)) s =
      deriv (fun w : ℂ => primitiveComplexEisenstein w z) s := by
  rw [(primitiveComplexEisenstein_hasDerivAt (gamma • z) s hs).deriv,
    (primitiveComplexEisenstein_hasDerivAt z s hs).deriv,
    primitive_parameter_derivative_tsum_SL2_invariant s hs gamma z]

/-- The same two actual functions of s are analytic and equal throughout
Re(s)>1. No meromorphic continuation is inserted into this equality. -/
theorem primitiveComplexEisenstein_SL2_analytic_eqOn (gamma : SL(2, ℤ)) (z : ℍ) :
    AnalyticOnNhd ℂ (fun s => primitiveComplexEisenstein s (gamma • z)) {s : ℂ | 1 < s.re} ∧
    AnalyticOnNhd ℂ (fun s => primitiveComplexEisenstein s z) {s : ℂ | 1 < s.re} ∧
    EqOn (fun s => primitiveComplexEisenstein s (gamma • z))
      (fun s => primitiveComplexEisenstein s z) {s : ℂ | 1 < s.re} := by
  exact ⟨primitiveComplexEisenstein_analyticOnNhd (gamma • z),
    primitiveComplexEisenstein_analyticOnNhd z,
    fun s hs => primitiveComplexEisenstein_SL2_invariant s hs gamma z⟩

end

end ImbalancedChen.Part3.PrimitiveEisensteinParameterAutomorphy