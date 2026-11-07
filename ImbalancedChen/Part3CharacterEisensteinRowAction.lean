import ImbalancedChen.Part3Gamma0DegeneracyMap
import ImbalancedChen.Part3PrimitiveEisensteinParameterAutomorphy
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual signed integer character weights and square-level row arithmetic.
The genuine integral conjugate is REUSED from the existing positive-level
degeneracy theorem; no determinant/conjugacy assumption or row permutation
is introduced. The new character calculation works with zero character
values and q=1, and never replaces a signed integer by natAbs.
-/
namespace ImbalancedChen.Part3.CharacterEisensteinRowAction
noncomputable section
open Matrix Matrix.SpecialLinearGroup EisensteinSeries
open scoped MatrixGroups UpperHalfPlane
open Gamma0ActualCuspsSourceOnly Gamma0DegeneracyMapSourceOnly
open PrimitiveEisensteinParameterAnalytic PrimitiveRealEisensteinAutomorphy
open PrimitiveEisensteinParameterAutomorphy

/-- Signed integer evaluation through the ACTUAL map Z -> ZMod q. -/
def characterWeight {q : ℕ} (chi : DirichletCharacter ℂ q) (c d : ℤ) : ℂ :=
  chi (c : ZMod q)*chi (d : ZMod q)

def primitiveWeight {q : ℕ} (chi : DirichletCharacter ℂ q) (v : PrimitivePair) : ℂ :=
  characterWeight chi (v.1 0) (v.1 1)

theorem characterWeight_norm_le_one {q : ℕ} (chi : DirichletCharacter ℂ q) (c d : ℤ) :
    ‖characterWeight chi c d‖ ≤ 1 := by
  rw [characterWeight,norm_mul]
  exact (mul_le_mul (chi.norm_le_one (c : ZMod q)) (chi.norm_le_one (d : ZMod q))
    (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem characterWeight_neg {q : ℕ} (chi : DirichletCharacter ℂ q) (c d : ℤ) :
    characterWeight chi (-c) (-d) = characterWeight chi c d := by
  have hminus : chi (-1 : ZMod q)*chi (-1 : ZMod q) = 1 := by
    rw [← map_mul]
    simp
  have hc : ((-c : ℤ) : ZMod q) = (-1)*(c : ZMod q) := by push_cast; ring
  have hd : ((-d : ℤ) : ZMod q) = (-1)*(d : ZMod q) := by push_cast; ring
  rw [characterWeight,characterWeight,hc,hd,map_mul,map_mul]
  calc
    _ = (chi (-1 : ZMod q)*chi (-1 : ZMod q))*(chi (c : ZMod q)*chi (d : ZMod q)) := by ring
    _ = _ := by rw [hminus,one_mul]

/-- Existing actual integral conjugate at N=d=q, selected without any
new determinant or conjugacy premise. Its lower entry is exactly C/q. -/
def squareConjugate (q : ℕ) (hq : 0 < q) (gamma : CongruenceSubgroup.Gamma0 (q^2)) : SL(2, ℤ) :=
  Classical.choose (exists_gamma0_degeneracy_matrix q q hq hq (gamma : SL(2, ℤ))
    (by simpa only [pow_two] using gamma.property))

theorem squareConjugate_data (q : ℕ) (hq : 0 < q) (gamma : CongruenceSubgroup.Gamma0 (q^2)) :
    squareConjugate q hq gamma ∈ CongruenceSubgroup.Gamma0 q ∧
      squareConjugate q hq gamma 0 0 = (gamma : SL(2, ℤ)) 0 0 ∧
      squareConjugate q hq gamma 0 1 = (q : ℤ)*(gamma : SL(2, ℤ)) 0 1 ∧
      (q : ℤ)*squareConjugate q hq gamma 1 0 = (gamma : SL(2, ℤ)) 1 0 ∧
      squareConjugate q hq gamma 1 1 = (gamma : SL(2, ℤ)) 1 1 := by
  have h := Classical.choose_spec (exists_gamma0_degeneracy_matrix q q hq hq (gamma : SL(2, ℤ))
    (by simpa only [pow_two] using gamma.property))
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

theorem squareConjugate_lower_eq_div (q : ℕ) (hq : 0 < q)
    (gamma : CongruenceSubgroup.Gamma0 (q^2)) :
    squareConjugate q hq gamma 1 0 = (gamma : SL(2, ℤ)) 1 0/(q : ℤ) := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  calc
    _ = ((q : ℤ)*squareConjugate q hq gamma 1 0)/(q : ℤ) :=
      (Int.mul_ediv_cancel_left _ hqZ).symm
    _ = _ := by rw [(squareConjugate_data q hq gamma).2.2.2.1]

/-- The primitive gcd condition and inverse permutation are Mathlib's
actual SL2 integer row equivalence for the genuine conjugate matrix. -/
def squareRowEquiv (q : ℕ) (hq : 0 < q) (gamma : CongruenceSubgroup.Gamma0 (q^2)) :
    PrimitivePair ≃ PrimitivePair := primitivePairEquiv (squareConjugate q hq gamma)

theorem squareRowEquiv_value (q : ℕ) (hq : 0 < q)
    (gamma : CongruenceSubgroup.Gamma0 (q^2)) (v : PrimitivePair) :
    (squareRowEquiv q hq gamma v).1 =
      ![v.1 0*(gamma : SL(2, ℤ)) 0 0+v.1 1*((gamma : SL(2, ℤ)) 1 0/(q : ℤ)),
        v.1 0*((q : ℤ)*(gamma : SL(2, ℤ)) 0 1)+v.1 1*(gamma : SL(2, ℤ)) 1 1] := by
  rw [squareRowEquiv,primitivePairEquiv_value]
  have h := squareConjugate_data q hq gamma
  ext i
  fin_cases i <;> simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,h.2.1,h.2.2.1,h.2.2.2.2,
    squareConjugate_lower_eq_div q hq gamma]

/-- Any actual determinant-one integer matrix diagonal modulo q preserves
chi(c)chi(d). The determinant proves chi(a)chi(d_gamma)=1 directly, so no
nonzero/unit-value division or nontrivial-modulus assumption is used. -/
theorem characterWeight_vecMul {q : ℕ} (chi : DirichletCharacter ℂ q)
    (g : SL(2, ℤ)) (hb : (q : ℤ) ∣ g 0 1) (hc : (q : ℤ) ∣ g 1 0) (v : Fin 2 → ℤ) :
    characterWeight chi ((v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ)) 0)
      ((v ᵥ* (g : Matrix (Fin 2) (Fin 2) ℤ)) 1) = characterWeight chi (v 0) (v 1) := by
  have hb0 : (g 0 1 : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hb
  have hc0 : (g 1 0 : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hc
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hmod := congrArg (fun t : ℤ => (t : ZMod q)) hdet
  push_cast at hmod
  have hdiag : (g 0 0 : ZMod q)*(g 1 1 : ZMod q) = 1 := by simpa only [hb0,hc0,zero_mul,sub_zero] using hmod
  have hchi : chi (g 0 0 : ZMod q)*chi (g 1 1 : ZMod q) = 1 := by
    simpa only [map_mul,map_one] using congrArg chi hdiag
  simp only [characterWeight,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
    Int.cast_add,Int.cast_mul,hb0,hc0,mul_zero,zero_mul,add_zero,zero_add]
  rw [map_mul,map_mul]
  calc
    _ = (chi (g 0 0 : ZMod q)*chi (g 1 1 : ZMod q))*(chi (v 0 : ZMod q)*chi (v 1 : ZMod q)) := by ring
    _ = _ := by rw [hchi,one_mul]

/-- New actual character preservation for the square-level row map. -/
theorem primitiveWeight_squareRowEquiv {q : ℕ} (hq : 0 < q)
    (chi : DirichletCharacter ℂ q) (gamma : CongruenceSubgroup.Gamma0 (q^2)) (v : PrimitivePair) :
    primitiveWeight chi (squareRowEquiv q hq gamma v) = primitiveWeight chi v := by
  have h := squareConjugate_data q hq gamma
  have hb : (q : ℤ) ∣ squareConjugate q hq gamma 0 1 :=
    ⟨(gamma : SL(2, ℤ)) 0 1,h.2.2.1⟩
  have hc : (q : ℤ) ∣ squareConjugate q hq gamma 1 0 :=
    (gamma0_mem_iff_level_dvd_c q _).mp h.1
  change characterWeight chi ((squareRowEquiv q hq gamma v).1 0)
    ((squareRowEquiv q hq gamma v).1 1) = characterWeight chi (v.1 0) (v.1 1)
  rw [squareRowEquiv,primitivePairEquiv_value]
  exact characterWeight_vecMul chi (squareConjugate q hq gamma) hb hc v.1
end
end ImbalancedChen.Part3.CharacterEisensteinRowAction
