import ImbalancedChen.Part3OriginalHolomorphicCuspFilter
import ImbalancedChen.P3FiniteKloostermanUnitScaling
import Mathlib.Data.ZMod.Units

namespace ImbalancedChen.Part3.OriginalPeterssonCuspOneArithmetic20261112

noncomputable section
open Matrix
open scoped MatrixGroups
open OriginalHolomorphicCuspFilter20261112 OriginalSmoothPoissonTail
open OriginalNonzeroCuspOneSource20261102 Gamma0ActualCuspsSourceOnly

private theorem gate_unit {N C : ℕ} [NeZero N] [NeZero C] {u : ZMod C} (hu : IsUnit u)
    (j : ZMod N) (h : (N:ℤ)∣(C:ℤ)-Dval C u j) : N.Coprime C := by
  have hd : IsCoprime (C:ℤ) (Dval C u j) :=
    (ZMod.coe_int_isUnit_iff_isCoprime (Dval C u j) C).mp (by simpa [Dval] using hu)
  obtain ⟨a,b,hb⟩ := hd
  obtain ⟨l,hl⟩ := h
  apply Nat.isCoprime_iff_coprime.mp
  refine ⟨-b*l,a+b,?_⟩
  linear_combination hb+b*hl

theorem bad_modulus {N C : ℕ} [NeZero N] [NeZero C] (h : ¬N.Coprime C) (m n : ℤ) :
    cuspSum N C cuspOneMatrix m n=0 := by
  unfold cuspSum
  apply Finset.sum_eq_zero;intro u _
  split_ifs with hu
  · apply Finset.sum_eq_zero;intro j _
    have hd : ¬(N:ℤ)∣(C:ℤ)-Dval C u j := fun hh => h (gate_unit hu j hh)
    simp [cuspOneMatrix,hd]
  · rfl

theorem good_modulus {N C : ℕ} [NeZero N] [NeZero C] (h : N.Coprime C) (m n : ℤ) :
    cuspSum N C cuspOneMatrix m n=cuspOneMatrixSum N C h m n := by
  classical
  let t : ZMod N := (n:ZMod N)*(C:ZMod N)⁻¹
  have hC : IsUnit (C:ZMod N) := (ZMod.isUnit_iff_coprime C N).mpr h.symm
  have hN : IsUnit (N:ZMod C) := (ZMod.isUnit_iff_coprime N C).mpr h
  have solv (u : ZMod N) : (N:ℤ)∣freq N C cuspOneMatrix n u ↔ u=t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [freq,cuspOneMatrix,Int.cast_sub,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,
      Matrix.of_apply,Matrix.cons_val_one,Matrix.cons_val_zero,mul_one,sub_eq_zero]
    constructor
    · intro hu
      dsimp [t]
      rw [hu,mul_assoc,ZMod.mul_inv_of_unit _ hC,mul_one]
    · rintro rfl
      dsimp [t]
      rw [mul_assoc,ZMod.inv_mul_of_unit _ hC,mul_one]
  let q := freq N C cuspOneMatrix n t/(N:ℤ)
  have hv : q*(N:ℤ)=n-(t.val:ℤ)*C := by
    simpa [q,freq,cuspOneMatrix] using Int.ediv_mul_cancel ((solv t).mpr rfl)
  have phase : chi N ((t.val:ℤ)*C)=chi N n := by
    rw [chi_eq,chi_eq]
    congr 1
    simp only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,t,mul_assoc,
      ZMod.inv_mul_of_unit _ hC,mul_one]
  have hq : (q:ZMod C)=((n*inverseResidue C N:ℤ):ZMod C) := by
    have hq' := congrArg (fun v : ℤ => (v:ZMod C)) hv
    push_cast at hq'
    simp only [ZMod.natCast_self,mul_zero,sub_zero] at hq'
    simp only [Int.cast_mul,inverseResidue,Int.cast_natCast,ZMod.natCast_zmod_val]
    rw [← hq',mul_assoc,ZMod.mul_inv_of_unit _ hN,mul_one]
  have hk : kloosterman C q m=kloosterman C (n*inverseResidue C N) m := by
    simp only [Physical.kloosterman_eq_zmod,hq]
  have hI : IsUnit ((inverseResidue C N:ℤ):ZMod C) := by
    simpa only [inverseResidue,Int.cast_natCast,ZMod.natCast_zmod_val] using hN.inv
  rw [cuspSum_eq,Finset.sum_eq_single t]
  · rw [if_pos ((solv t).mpr rfl),cuspOneMatrixSum_eq_phase_mul_kloosterman N C (NeZero.pos N) h]
    simp only [cuspOneMatrix,Matrix.of_apply,Matrix.cons_val_one,Matrix.cons_val_zero,mul_one]
    rw [phase,hk,kloosterman_unit_scaling n m _ hI,inverse_swap C]
    rfl
  · intro u _ hu;rw [if_neg (fun h' => hu ((solv u).mp h'))]
  · simp

end
end ImbalancedChen.Part3.OriginalPeterssonCuspOneArithmetic20261112
