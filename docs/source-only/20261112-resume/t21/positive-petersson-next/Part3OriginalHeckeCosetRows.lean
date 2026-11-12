import ImbalancedChen.Part3OriginalHolomorphicPoincare
import Mathlib.Logic.Equiv.Fin.Basic

namespace ImbalancedChen.Part3.OriginalHeckeCosetRows20261112

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane ModularForm
open Gamma0ParabolicBottomRow20261025a Gamma0ParabolicCosetRows20261025a
open Gamma0ParabolicEffectiveDecomposition20261025a OriginalHolomorphicCuspFilter20261112

def positive (v : Fin 2 → ℤ) : Prop := 0<v 0 ∨ v 0=0 ∧ 0<v 1

/-- The central sign is taken exactly once, also at the zero denominator. -/
abbrev Row (N : ℕ) (g : SL(2,ℤ)) :=
  {v : Fin 2→ℤ // IsCoprime (v 0) (v 1) ∧ (N:ℤ)∣v 0*g 1 1-v 1*g 1 0 ∧ positive v}

private theorem oriented {v : Fin 2→ℤ} (h : IsCoprime (v 0) (v 1)) :
    positive v ∨ positive (-v) := by
  obtain ⟨a,b,h⟩ := h
  by_cases hc : v 0=0
  · have hd : v 1≠0 := by intro hd; simp [hc,hd] at h
    simp only [positive,Pi.neg_apply,hc,lt_irrefl,neg_zero,true_and,false_or]
    omega
  · simp only [positive,Pi.neg_apply]
    omega

private theorem orientation_unique {v w : Fin 2→ℤ} (hv : positive v) (hw : positive w)
    (h : v=w ∨ v= -w) : v=w := by
  rcases h with h|h
  · exact h
  · rw [h] at hv
    simp only [positive,Pi.neg_apply] at hv hw
    omega

private theorem completion {v : Fin 2→ℤ} (h : IsCoprime (v 0) (v 1)) :
    ∃ M : SL(2,ℤ), bottomRow M=v := by
  obtain ⟨u,a,ha⟩ := h
  let M : SL(2,ℤ) := ⟨!![a,-u;v 0,v 1],by simp [Matrix.det_fin_two_of];linear_combination ha⟩
  exact ⟨M,by funext j;fin_cases j <;>rfl⟩

def matrix {N : ℕ} {g : SL(2,ℤ)} (v : Row N g) : SL(2,ℤ) :=
  (completion v.property.1).choose

@[simp] theorem row_matrix {N : ℕ} {g : SL(2,ℤ)} (v : Row N g) :
    bottomRow (matrix v)=v.val := (completion v.property.1).choose_spec

def gamma {N : ℕ} {g : SL(2,ℤ)} (v : Row N g) : CongruenceSubgroup.Gamma0 N :=
  ⟨matrix v*g⁻¹,(integral_cusp_gate N _ _).mpr (by
    change (N:ℤ)∣bottomRow (matrix v) 0*g 1 1-bottomRow (matrix v) 1*g 1 0
    rw [row_matrix];exact v.property.2.1)⟩

def coset {N : ℕ} {g : SL(2,ℤ)} (v : Row N g) : GammaInfinityCosets N :=
  Quotient.mk'' (gamma v)

theorem covariant_relation {N : ℕ} (g : SL(2,ℤ)) (a b : CongruenceSubgroup.Gamma0 N) :
    ((Quotient.mk'' a : GammaInfinityCosets N)=Quotient.mk'' b) ↔
    (bottomRow ((a:SL(2,ℤ))*g)=bottomRow ((b:SL(2,ℤ))*g) ∨
     bottomRow ((a:SL(2,ℤ))*g)= -bottomRow ((b:SL(2,ℤ))*g)) := by
  rw [Quotient.eq,parabolic_orbit_iff_relative,gammaInfinity_left_relation_iff,
    signed_bottomRow_iff_left_signed_translation,signed_bottomRow_iff_left_signed_translation]
  constructor
  · rintro ⟨t,h|h⟩
    · exact ⟨t,Or.inl (by rw [h,mul_assoc])⟩
    · exact ⟨t,Or.inr (by rw [h,neg_mul,mul_assoc])⟩
  · rintro ⟨t,h|h⟩
    · exact ⟨t,Or.inl (mul_right_cancel (by simpa only [mul_assoc] using h))⟩
    · exact ⟨t,Or.inr (mul_right_cancel (by simpa only [neg_mul,mul_assoc] using h))⟩

@[simp] theorem gamma_frame {N : ℕ} {g : SL(2,ℤ)} (v : Row N g) :
    (gamma v : SL(2,ℤ))*g=matrix v := by change matrix v*g⁻¹*g=_;group

theorem coset_bijective (N : ℕ) (g : SL(2,ℤ)) : Function.Bijective (coset (N:=N) (g:=g)) := by
  constructor
  · intro v w h
    apply Subtype.ext
    have H := (covariant_relation g (gamma v) (gamma w)).mp h
    simp only [gamma_frame,row_matrix] at H
    exact orientation_unique v.property.2.2 w.property.2.2 H
  · intro Q;refine Quotient.inductionOn Q ?_;intro a
    let M := (a:SL(2,ℤ))*g
    let v := bottomRow M
    have hco : IsCoprime (v 0) (v 1) := bottomRow_bezout M
    have hlevel : (N:ℤ)∣v 0*g 1 1-v 1*g 1 0 := (integral_cusp_gate N M g).mp
      (by simpa [M,mul_assoc] using a.property)
    rcases oriented hco with hp | hp
    · let w : Row N g := ⟨v,hco,hlevel,hp⟩
      refine ⟨w,(covariant_relation g (gamma w) a).mpr (Or.inl ?_)⟩
      rw [gamma_frame,row_matrix];rfl
    · have hco' : IsCoprime ((-v) 0) ((-v) 1) := by simpa using hco
      have hl : (N:ℤ)∣(-v) 0*g 1 1-(-v) 1*g 1 0 := by
        simpa only [Pi.neg_apply,neg_mul,neg_sub_neg,neg_sub] using dvd_neg.mpr hlevel
      let w : Row N g := ⟨-v,hco',hl,hp⟩
      refine ⟨w,(covariant_relation g (gamma w) a).mpr (Or.inr ?_)⟩
      rw [gamma_frame,row_matrix];rfl

/-- Actual parabolic positions at any integral cusp, including the diagonal. -/
def rowEquiv (N : ℕ) (g : SL(2,ℤ)) : Row N g ≃ GammaInfinityCosets N :=
  Equiv.ofBijective coset (coset_bijective N g)

theorem zero_row {N : ℕ} {g : SL(2,ℤ)} (v : Row N g) (h : v.val 0=0) :
    v.val 1=1 ∧ (N:ℤ)∣g 1 0 := by
  have hp := v.property.2.2
  simp only [positive,h,lt_irrefl,false_or,true_and] at hp
  obtain ⟨u,b,hb⟩ := v.property.1
  simp only [h,mul_zero,zero_add] at hb
  have hd : v.val 1=1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hb with ⟨_,v'⟩|⟨_,v'⟩ <;>omega
  exact ⟨hd,by simpa only [h,hd,zero_mul,one_mul,zero_sub,dvd_neg] using v.property.2.1⟩

theorem exists_zero_iff {N : ℕ} (g : SL(2,ℤ)) :
    (∃ v : Row N g, v.val 0=0) ↔ (N:ℤ)∣g 1 0 := by
  constructor
  · rintro ⟨v,h⟩;exact (zero_row v h).2
  · intro h
    let v : Row N g := ⟨![0,1],by simp,by simpa using h,by simp [positive]⟩
    exact ⟨v,rfl⟩

theorem zero_row_unique {N : ℕ} {g : SL(2,ℤ)} (a b : Row N g)
    (ha : a.val 0=0) (hb : b.val 0=0) : a=b := by
  apply Subtype.ext;funext j;fin_cases j
  · exact ha.trans hb.symm
  · exact (zero_row a ha).1.trans (zero_row b hb).1.symm

/-- Unique full integer lift of the two residues in the actual denominator sum. -/
def liftedD {C N : ℕ} [NeZero C] [NeZero N] (t : ZMod C × ZMod N × ℤ) : ℤ :=
  Dval C t.1 t.2.1+(C:ℤ)*N*t.2.2

theorem residues {C N : ℕ} [NeZero C] [NeZero N] (t : ZMod C × ZMod N × ℤ) :
    (liftedD t : ZMod C)=t.1 ∧ liftedD t/(C:ℤ)=(t.2.1.val:ℤ)+(N:ℤ)*t.2.2 := by
  have hC : (0:ℤ)<C := by exact_mod_cast NeZero.pos C
  have hlt : (t.1.val:ℤ)<C := by exact_mod_cast t.1.val_lt
  have H : liftedD t=(t.1.val:ℤ)+(C:ℤ)*((t.2.1.val:ℤ)+(N:ℤ)*t.2.2) := by
    dsimp [liftedD,Dval];ring
  rw [H]
  constructor
  · simp
  · rw [Int.add_mul_ediv_left _ _ hC.ne',Int.ediv_eq_zero_of_lt (by positivity) hlt,zero_add]

def liftEquiv (C N : ℕ) [NeZero C] [NeZero N] : ZMod C × ZMod N × ℤ ≃ ℤ where
  toFun := liftedD
  invFun D := ((D : ZMod C),((D/(C:ℤ):ℤ):ZMod N),D/(C:ℤ)/(N:ℤ))
  left_inv t := by
    rcases t with ⟨u,j,l⟩
    obtain ⟨hu,hj⟩ := residues (u,j,l)
    have hN : (0:ℤ)<N := by exact_mod_cast NeZero.pos N
    have hlt : (j.val:ℤ)<N := by exact_mod_cast j.val_lt
    simp only [hu,hj,Prod.mk.injEq,true_and]
    constructor
    · simp
    · rw [Int.add_mul_ediv_left _ _ hN.ne',Int.ediv_eq_zero_of_lt (by positivity) hlt,zero_add]
  right_inv D := by
    simp only [liftedD,Dval,ZMod.val_intCast]
    have hC := Int.emod_add_mul_ediv D (C:ℤ)
    have hN := Int.emod_add_mul_ediv (D/(C:ℤ)) (N:ℤ)
    linear_combination hC+(C:ℤ)*hN

theorem lift_gate (C N : ℕ) [NeZero C] [NeZero N] (g : SL(2,ℤ))
    (u : ZMod C) (j : ZMod N) (l : ℤ) :
    ((N:ℤ)∣(C:ℤ)*g 1 1-liftedD (u,j,l)*g 1 0) ↔
      (N:ℤ)∣(C:ℤ)*g 1 1-Dval C u j*g 1 0 := by
  have H : (C:ℤ)*g 1 1-liftedD (u,j,l)*g 1 0=
      ((C:ℤ)*g 1 1-Dval C u j*g 1 0)+(N:ℤ)*(-C*l*g 1 0) := by dsimp [liftedD];push_cast;ring
  rw [H,dvd_add_right (dvd_mul_right _ _)]

end
end ImbalancedChen.Part3.OriginalHeckeCosetRows20261112
