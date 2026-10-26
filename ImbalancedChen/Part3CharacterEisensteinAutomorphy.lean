import ImbalancedChen.Part3CharacterEisensteinSeries
import ImbalancedChen.Part3PrimitiveEisensteinHorizontalContinuity
import ImbalancedChen.Part3Gamma0QuotientCellPushforward

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual square-level automorphy of the new character-weighted series.
The existing genuine degeneracy conjugacy acts on the actual upper half
plane, its actual primitive row permutation preserves signed character
weights, and reindexing gives Gamma0(q^2) invariance. The series descends
to the native orbit quotient and has period one from actual T membership.
Only Re(s)>1 is used as a convergent-series domain. No newform, nonzero,
continued/scattering identity or channel completeness is asserted.
-/
namespace ImbalancedChen.Part3.CharacterEisensteinAutomorphy
noncomputable section
open Set Filter Topology Complex UpperHalfPlane EisensteinSeries Matrix
open scoped UpperHalfPlane MatrixGroups
open Gamma0ActualCuspsSourceOnly Gamma0DegeneracyMapSourceOnly
open PrimitiveEisensteinParameterAnalytic PrimitiveRealEisensteinAutomorphy
open PrimitiveEisensteinParameterAutomorphy PrimitiveEisensteinFourierParameterAnalytic
open PrimitiveEisensteinHorizontalContinuity Gamma0QuotientCellPushforward20261025a
open CharacterEisensteinRowAction CharacterEisensteinSeries

private def castIntegral (g : SL(2, ℤ)) : SL(2, ℝ) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g

private theorem castIntegral_smul (g : SL(2, ℤ)) (z : ℍ) : castIntegral g • z = g • z := rfl

/-- Native action intertwining, extracted from the existing ACTUAL integral
conjugation theorem, not postulated as a scaling action law. -/
theorem scaledPoint_square_action (q : ℕ) (hq : 0 < q)
    (gamma : CongruenceSubgroup.Gamma0 (q^2)) (z : ℍ) :
    scaledPoint q hq ((gamma : SL(2, ℤ)) • z) =
      squareConjugate q hq gamma • scaledPoint q hq z := by
  have hreal : castIntegral (squareConjugate q hq gamma) =
      degeneracyDiagonal q hq * castIntegral (gamma : SL(2, ℤ)) * (degeneracyDiagonal q hq)⁻¹ := by
    exact (Classical.choose_spec (exists_gamma0_degeneracy_matrix q q hq hq (gamma : SL(2, ℤ))
      (by simpa only [pow_two] using gamma.property))).2.2.2.2.2
  have hcomm : degeneracyDiagonal q hq * castIntegral (gamma : SL(2, ℤ)) =
      castIntegral (squareConjugate q hq gamma) * degeneracyDiagonal q hq := by
    rw [hreal]
    group
  change degeneracyDiagonal q hq • ((gamma : SL(2, ℤ)) • z) =
    squareConjugate q hq gamma • (degeneracyDiagonal q hq • z)
  rw [← castIntegral_smul (gamma : SL(2, ℤ)) z,← mul_smul,hcomm,mul_smul,castIntegral_smul]

/-- Actual weighted summand transformation under the square-level subgroup. -/
theorem characterSeed_square_apply {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (s : ℂ) (gamma : CongruenceSubgroup.Gamma0 (q^2)) (z : ℍ) (v : PrimitivePair) :
    characterSeed hq chi ((gamma : SL(2, ℤ)) • z) v s =
      characterSeed hq chi z (squareRowEquiv q hq gamma v) s := by
  unfold characterSeed
  rw [scaledPoint_square_action,complexSeed_SL2_apply,primitiveWeight_squareRowEquiv hq chi gamma v]
  rfl

/-- Genuine Gamma0(q^2) automorphy of the absolutely convergent series. -/
theorem characterEisenstein_square_invariant {q : ℕ} (hq : 0 < q)
    (chi : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re)
    (gamma : CongruenceSubgroup.Gamma0 (q^2)) (z : ℍ) :
    characterEisenstein hq chi s ((gamma : SL(2, ℤ)) • z) = characterEisenstein hq chi s z := by
  have habs := characterSeed_summable hq chi z s hs
  have habsTransformed := characterSeed_summable hq chi ((gamma : SL(2, ℤ)) • z) s hs
  have hsum : (∑' v : PrimitivePair, characterSeed hq chi ((gamma : SL(2, ℤ)) • z) v s) =
      ∑' v : PrimitivePair, characterSeed hq chi z v s := by
    calc
      _ = ∑' v : PrimitivePair, characterSeed hq chi z (squareRowEquiv q hq gamma v) s :=
        tsum_congr (fun v => characterSeed_square_apply hq chi s gamma z v)
      _ = _ := (squareRowEquiv q hq gamma).tsum_eq (fun v => characterSeed hq chi z v s)
  exact congrArg ((1/2 : ℂ)*·) hsum

/-- The actual simultaneous sign action on primitive pairs is -I. -/
theorem minusOne_primitive_value (v : PrimitivePair) :
    (primitivePairEquiv (-1 : SL(2, ℤ)) v).1 = -v.1 := by
  rw [primitivePairEquiv_value]
  simp

/-- Full summand sign invariance, including chi(-1)^2=1, without assuming
that the individual character is even. -/
theorem characterSeed_simultaneous_sign {q : ℕ} (hq : 0 < q)
    (chi : DirichletCharacter ℂ q) (z : ℍ) (v : PrimitivePair) (s : ℂ) :
    characterSeed hq chi z (primitivePairEquiv (-1 : SL(2, ℤ)) v) s = characterSeed hq chi z v s := by
  have hw : primitiveWeight chi (primitivePairEquiv (-1 : SL(2, ℤ)) v) = primitiveWeight chi v := by
    unfold primitiveWeight
    rw [minusOne_primitive_value]
    simpa only [Pi.neg_apply] using characterWeight_neg chi (v.1 0) (v.1 1)
  have hpoint : (-1 : SL(2, ℤ)) • scaledPoint q hq z = scaledPoint q hq z := by
    simpa only [one_smul] using ModularGroup.SL_neg_smul (1 : SL(2, ℤ)) (scaledPoint q hq z)
  have hseed := complexSeed_SL2_apply s (-1 : SL(2, ℤ)) (scaledPoint q hq z) v
  rw [hpoint] at hseed
  rw [characterSeed,characterSeed,hw,hseed]

/-- The actual square-level quotient, reused from the existing native
Gamma0 orbit-space construction, receives this new convergent function. -/
def quotientCharacterEisenstein {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (s : {s : ℂ // 1 < s.re}) : Gamma0OrbitSpace (q^2) → ℂ :=
  Quotient.lift (characterEisenstein hq chi s.1) (by
    intro z w hzw
    obtain ⟨gamma,hgamma⟩ := MulAction.orbitRel_apply.mp hzw
    rw [← hgamma]
    exact characterEisenstein_square_invariant hq chi s.1 s.2 gamma w)

@[simp] theorem quotientCharacterEisenstein_projection {q : ℕ} (hq : 0 < q)
    (chi : DirichletCharacter ℂ q) (s : {s : ℂ // 1 < s.re}) (z : ℍ) :
    quotientCharacterEisenstein hq chi s (orbitProjection (q^2) z) = characterEisenstein hq chi s.1 z := rfl

/-- Period one follows from the actual modular T element of Gamma0(q^2). -/
theorem characterEisenstein_T_invariant {q : ℕ} (hq : 0 < q)
    (chi : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) (z : ℍ) :
    characterEisenstein hq chi s (ModularGroup.T • z) = characterEisenstein hq chi s z := by
  let gamma : CongruenceSubgroup.Gamma0 (q^2) :=
    ⟨ModularGroup.T,by simpa only [zpow_one] using translation_mem_gamma0 (q^2) 1⟩
  exact characterEisenstein_square_invariant hq chi s hs gamma z

theorem characterEisenstein_horizontal_periodic {q : ℕ} (hq : 0 < q)
    (chi : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => characterEisenstein hq chi s (horizontalPoint y hy x)) 1 := by
  intro x
  rw [horizontalPoint_add_one]
  exact characterEisenstein_T_invariant hq chi s hs (horizontalPoint y hy x)
end
end ImbalancedChen.Part3.CharacterEisensteinAutomorphy
