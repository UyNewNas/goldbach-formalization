import ImbalancedChen.Part3CharacterMiddleCuspGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual primitive-pair bijection at the middle cusp, with derived signs:
(c,e)->(a*c+e,-c), inverse(m,n)->(-n,m+a*n). The actual character weight
is transported to chi(-n)*chi(m+a*n), including zero values. Positive bases
and individual complex seeds are identified by native SL2 row covariance.
No sum, asymptotic, nonzero or character-automorphy theorem is asserted. -/

noncomputable section
open Matrix Complex EisensteinSeries
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAnalytic
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.PrimitiveEisensteinParameterAutomorphy
open ImbalancedChen.Part3.CharacterEisensteinRowAction
open ImbalancedChen.Part3.CharacterEisensteinSeries
open ImbalancedChen.Part3.CharacterMiddleCuspGeometry20261026b

namespace ImbalancedChen.Part3.CharacterMiddlePrimitiveRows20261026b

def middleRowEquiv (a : ℤ) : PrimitivePair ≃ PrimitivePair :=
  primitivePairEquiv (middleChartMatrix a)

theorem middleRowEquiv_value (a : ℤ) (v : PrimitivePair) :
    (middleRowEquiv a v).1 = ![a * v.1 0 + v.1 1, -(v.1 0)] := by
  rw [middleRowEquiv, primitivePairEquiv_value]
  ext i
  fin_cases i <;>
    simp [middleChartMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      SpecialLinearGroup.coe_mul, Matrix.mul_fin_two, ModularGroup.coe_T_zpow,
      ModularGroup.coe_S] <;> ring

theorem middleRowEquiv_symm_value (a : ℤ) (w : PrimitivePair) :
    ((middleRowEquiv a).symm w).1 = ![-(w.1 1), w.1 0 + a * w.1 1] := by
  have h := middleRowEquiv_value a ((middleRowEquiv a).symm w)
  rw [Equiv.apply_symm_apply] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  ext i
  fin_cases i
  · simp only [Matrix.cons_val_zero]
    omega
  · simp only [Matrix.cons_val_one]
    linear_combination -h0 - a * h1

def middleTransportWeight {q : ℕ} (chi : DirichletCharacter ℂ q)
    (a : ℤ) (w : PrimitivePair) : ℂ :=
  characterWeight chi (-(w.1 1)) (w.1 0 + a * w.1 1)

theorem middleTransportWeight_literal {q : ℕ} (chi : DirichletCharacter ℂ q)
    (a : ℤ) (w : PrimitivePair) :
    middleTransportWeight chi a w =
      chi (-(w.1 1) : ZMod q) * chi (w.1 0 + a * w.1 1 : ZMod q) := by
  simp only [middleTransportWeight, characterWeight, Int.cast_neg, Int.cast_add, Int.cast_mul]

theorem primitiveWeight_middle_symm {q : ℕ} (chi : DirichletCharacter ℂ q)
    (a : ℤ) (w : PrimitivePair) :
    primitiveWeight chi ((middleRowEquiv a).symm w) = middleTransportWeight chi a w := by
  rw [primitiveWeight, middleRowEquiv_symm_value]
  rfl

theorem primitiveWeight_middle_transport {q : ℕ} (chi : DirichletCharacter ℂ q)
    (a : ℤ) (v : PrimitivePair) :
    primitiveWeight chi v = middleTransportWeight chi a (middleRowEquiv a v) := by
  simpa only [Equiv.symm_apply_apply] using
    primitiveWeight_middle_symm chi a (middleRowEquiv a v)

theorem positiveBase_middle_transport (p : ℕ) (hp : 0 < p)
    (sigma : SL(2, ℤ)) (hc : sigma 1 0 = (p : ℤ)) (z : UpperHalfPlane) (v : PrimitivePair) :
    positiveBase (scaledPoint p hp (sigma • z)) v =
      positiveBase (middleAffinePoint p hp sigma z) (middleRowEquiv (sigma 0 0) v) := by
  rw [scaled_middle_eq_chart_affine p hp sigma hc z]
  exact positiveBase_SL2_apply (middleChartMatrix (sigma 0 0)) _ v

/-- This identifies each ORIGINAL character seed; no infinite reindexing
or interchange is part of this finite dictionary. -/
theorem characterSeed_middle_transport (p : ℕ) (hp : 0 < p) (chi : DirichletCharacter ℂ p)
    (sigma : SL(2, ℤ)) (hc : sigma 1 0 = (p : ℤ))
    (z : UpperHalfPlane) (v : PrimitivePair) (s : ℂ) :
    characterSeed hp chi (sigma • z) v s =
      middleTransportWeight chi (sigma 0 0) (middleRowEquiv (sigma 0 0) v) *
        complexSeed (middleAffinePoint p hp sigma z) (middleRowEquiv (sigma 0 0) v) s := by
  rw [characterSeed, primitiveWeight_middle_transport chi (sigma 0 0), complexSeed,
    positiveBase_middle_transport p hp sigma hc z v]
  rfl

end ImbalancedChen.Part3.CharacterMiddlePrimitiveRows20261026b
