import ImbalancedChen.Part3OriginalHeckeRowSlash
import ImbalancedChen.Part3OriginalHeckePoisson
import Mathlib.Data.ZMod.Units

namespace ImbalancedChen.Part3.OriginalHeckePhysicalRow20261112

noncomputable section
open Set Complex UpperHalfPlane Matrix
open scoped MatrixGroups UpperHalfPlane ModularForm
open OriginalHeckeCosetRows20261112 OriginalHeckeRowSlash20261112
open OriginalHeckeStripPairing20261112 OriginalHolomorphicPoincare20261112
open OriginalHolomorphicCuspFilter20261112 OriginalHeckeFourierKernel20261112
open OriginalHeckeCuspSeries20261112 OriginalHeckePoisson20261112
open P3Period64NativeReconstructionSourceOnly (e)

def uval (C : ℕ+) (D : ℤ) (w : ℍ) : ℝ := (w.re+(D:ℝ)/(C:ℝ))/w.im

def factor (k : ℕ) (C : ℕ+) (p : Params) : ℂ :=
  ((1/(C:ℝ)^k*(C:ℝ)^(-2*p.1.val)*p.2.im^(-(k:ℝ)-p.1.val):ℝ):ℂ)

def term (k m : ℕ) (C : ℕ+) (D : ℤ) (p : Params) : ℂ :=
  factor k C p * chi C ((m:ℤ)*((D:ZMod (C:ℕ))⁻¹).val) *
    kernel k p.1.val (Mval m C p.2) (uval C D p.2)

private theorem top_inverse {C : ℕ+} (M : SL(2,ℤ)) (hc : M 1 0=(C:ℤ)) :
    (M 0 0:ZMod (C:ℕ))=(M 1 1:ZMod (C:ℕ))⁻¹ := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by simpa only [Matrix.det_fin_two] using M.det_coe
  rw [hc] at hd
  have H := congrArg (fun v : ℤ => (v : ZMod (C:ℕ))) hd
  push_cast at H
  simp only [ZMod.natCast_self,mul_zero,sub_zero] at H
  have hcop := Gamma0ParabolicBottomRow20261025a.bottomRow_bezout M
  change IsCoprime (M 1 0) (M 1 1) at hcop
  rw [hc] at hcop
  have hu := (ZMod.coe_int_isUnit_iff_isCoprime (M 1 1) C).mpr hcop
  calc
    _ = (M 0 0:ZMod (C:ℕ))*((M 1 1:ZMod (C:ℕ))*(M 1 1:ZMod (C:ℕ))⁻¹) := by
      rw [ZMod.mul_inv_of_unit _ hu,mul_one]
    _ = _ := by rw [← mul_assoc,H,one_mul]

private theorem scale_real (k : ℕ) {c y t s : ℝ} (hc : 0<c) (hy : 0<y) (ht : 0<t) :
    (y/((c*y)^2*t))^s * ((c*y)^k)⁻¹ =
      (1/c^k*c^(-2*s)*y^(-(k:ℝ)-s))*t^(-s) := by
  have E : y/((c*y)^2*t)=c^(-2:ℝ)*y^(-1:ℝ)*t^(-1:ℝ) := by
    rw [Real.rpow_neg hc.le,Real.rpow_two,Real.rpow_neg_one,Real.rpow_neg_one]
    field_simp [hc.ne',hy.ne',ht.ne'] <;>ring
  rw [E,Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
  simp only [← Real.rpow_mul hc.le,← Real.rpow_mul hy.le,← Real.rpow_mul ht.le,neg_one_mul,
    mul_pow,mul_inv,one_div]
  rw [show -(k:ℝ)-s= -(k:ℝ)+(-s) by ring,Real.rpow_add hy,Real.rpow_neg hy.le,Real.rpow_natCast]
  ring

/-- Exact raw coefficient of the physical matrix at every regularization parameter, including zero. -/
theorem physical_row (r m : ℕ) (M : SL(2,ℤ)) (C : ℕ+) (hC : M 1 0=(C:ℤ)) (p : Params) :
    (heckeSeed m p.1.val ∣[2*(r:ℤ)] M) p.2 = term (2*r) m C (M 1 1) p := by
  let w := p.2
  let y := w.im
  let u := uval C (M 1 1) w
  let v : ℂ := (u:ℂ)+I
  have cy : (0:ℝ)<C := by exact_mod_cast C.property
  have hy : 0<y := w.im_pos
  have H : denom M w = ((C:ℝ)*y:ℝ)*v := by
    rw [ModularGroup.denom_apply,hC]
    apply Complex.ext <;> dsimp [v,u,uval,y] <;> push_cast <;>
      simp [Complex.mul_re,Complex.mul_im] <;> field_simp [cy.ne',hy.ne'] <;>ring
  have hn : Complex.normSq v=1+u^2 := by simp [v,Complex.normSq_apply];ring
  have hzero : v≠0 := by intro h;have h' := congrArg Complex.im h;simp [v] at h'
  have normH : Complex.normSq (denom M w)=((C:ℝ)*y)^2*(1+u^2) := by
    rw [H,Complex.normSq_mul,Complex.normSq_ofReal,hn]
    ring
  have height : (M • w).im=y/(((C:ℝ)*y)^2*(1+u^2)) := by
    rw [ModularGroup.im_smul_eq_div_normSq,normH]
  have detZ : M 0 0*M 1 1-M 0 1*M 1 0=1 := by simpa only [Matrix.det_fin_two] using M.det_coe
  have detC : (M 0 0:ℂ)*(M 1 1:ℂ)-(M 0 1:ℂ)*(C:ℂ)=1 := by rw [hC] at detZ;exact_mod_cast detZ
  have mob : (↑(M • w) : ℂ)=(M 0 0:ℂ)/(C:ℂ)-1/((C:ℂ)*denom M w) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    change ((M 0 0:ℂ)*w+(M 0 1:ℂ))/denom M w=_
    field_simp [denom_ne_zero M w,show (C:ℂ)≠0 by exact_mod_cast cy.ne']
    rw [ModularGroup.denom_apply,hC];push_cast
    linear_combination -detC
  have phase : q (M • w)^m=chi C ((m:ℤ)*((M 1 1:ZMod (C:ℕ))⁻¹).val) *
      Complex.exp (-I*(Mval m C w:ℂ)*v⁻¹) := by
    have hz : chi C ((m:ℤ)*(M 0 0))=chi C ((m:ℤ)*((M 1 1:ZMod (C:ℕ))⁻¹).val) := by
      simp only [chi_eq,Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val,top_inverse M hC]
    rw [← hz,q,Function.Periodic.qParam,div_one,← Complex.exp_nat_mul,mob,H,chi,e,← Complex.exp_add]
    congr 1;dsimp [Mval,y];push_cast
    field_simp [cy.ne',hy.ne',hzero] <;>ring
  have scal := congrArg Complex.ofReal
    (scale_real (2*r) (s:=p.1.val) cy hy (by positivity : 0<1+u^2))
  have k : 2*(r:ℤ)=((2*r:ℕ):ℤ) := by push_cast;rfl
  change (heckeSeed m p.1.val ∣[2*(r:ℤ)] M) w=_
  rw [ModularForm.SL_slash_apply,heckeSeed,height,phase,H,k,zpow_neg,zpow_natCast,mul_pow,mul_inv]
  unfold term factor kernel realPower resolvent
  change _=(_ * chi _ _) * ((v⁻¹)^(2*r)*_*_)
  simp only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow] at scal
  rw [inv_pow]
  linear_combination (chi C ((m:ℤ)*((M 1 1:ZMod (C:ℕ))⁻¹).val) *
    Complex.exp (-I*(Mval m C w:ℂ)*v⁻¹) * (v^(2*r))⁻¹)*scal

theorem term_lift (k m : ℕ) (C : ℕ+) (N : ℕ) [NeZero N] (t : ZMod (C:ℕ)×ZMod N×ℤ)
    (p : Params) : term k m C (liftedD t) p=
      factor k C p*chi C ((m:ℤ)*(t.1⁻¹).val) *
        kernel k p.1.val (Mval m C p.2)
          ((p.2.re+(Dval C t.1 t.2.1:ℝ)/C+(t.2.2:ℝ)*N)/p.2.im) := by
  rw [term,(residues t).1]
  congr 2
  dsimp [uval,liftedD]
  push_cast;field_simp [show (C:ℝ)≠0 by positivity] <;>ring

end
end ImbalancedChen.Part3.OriginalHeckePhysicalRow20261112
