import ImbalancedChen.Part3OriginalPeterssonHorizontalMode
import ImbalancedChen.Part3OriginalPeterssonCuspLimit
import ImbalancedChen.Part3OriginalPeterssonCuspOneArithmetic

namespace ImbalancedChen.Part3.OriginalPeterssonNormalizedOrbits20261112

noncomputable section
open Set Complex UpperHalfPlane Matrix Matrix.SpecialLinearGroup Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane ModularForm
open OriginalPeterssonHorizontalMode20261112 OriginalPeterssonLipschitz20261112
open OriginalHeckeFourierKernel20261112 OriginalHeckeCuspSeries20261112 OriginalHeckePoisson20261112
open OriginalHeckeLimitFamily20261112 OriginalHeckeCuspExpansion20261112
open OriginalHolomorphicCuspFilter20261112 OriginalHolomorphicCuspFrames20261110
open OriginalHolomorphicPeterssonSpace20261112 Gamma0ActualCuspsSourceOnly
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open ActualGeneralJBesselSourceOnly P3Period64NativeReconstructionSourceOnly (e)

def scaledPoint (N : ℕ) [NeZero N] (w : ℍ) : ℍ := ⟨(N:ℂ)*w,by simp [Complex.mul_im];positivity⟩
def modulus (N : ℕ) (C : ℕ+) : ℝ := Real.sqrt N*(C:ℝ)

theorem modulus_pos (N : ℕ) [NeZero N] (C : ℕ+) : 0<modulus N C := by
  dsimp [modulus];exact mul_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))) (by positivity)

theorem frame_one (N r : ℕ) [NeZero N] (f : Forms N r) (w : ℍ) :
    frameForm N (NeZero.pos N) r f cuspOneMatrix w =
      (N:ℂ)^r*((⇑f ∣[2*(r:ℤ)] cuspOneMatrix) (scaledPoint N w)) := by
  let H := widthDiagonal N (NeZero.pos N)
  have hN : 0<(N:ℝ) := by exact_mod_cast NeZero.pos N
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr hN).ne'
  have sq : ((Real.sqrt (N:ℝ):ℝ):ℂ)^2=(N:ℂ) := by exact_mod_cast Real.sq_sqrt hN.le
  have hI : mapGL ℝ (integralReal cuspOneMatrix)=mapGL ℝ cuspOneMatrix := by
    apply Units.ext;ext i j;simp [integralReal,mapGL_coe_matrix,SpecialLinearGroup.map_apply_coe]
  have hf : frameGL N (NeZero.pos N) cuspOneMatrix=mapGL ℝ cuspOneMatrix*mapGL ℝ H := by
    unfold frameGL normalizedScaling
    simp only [cuspWidth_cuspOne,map_mul,hI];rfl
  have act : (mapGL ℝ H) • w=scaledPoint N w := by
    change H • w=_
    apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply]
    simp [H,widthDiagonal,scaledPoint,div_eq_mul_inv,mul_assoc]
    <;> push_cast <;> field_simp [Complex.ofReal_ne_zero.mpr hs]
    <;> linear_combination (w:ℂ)*sq
  have d : denom (mapGL ℝ H) w = ((Real.sqrt (N:ℝ):ℝ):ℂ)⁻¹ := by
    simp [H,widthDiagonal,denom,mapGL_coe_matrix,one_div]
  change (⇑f ∣[2*(r:ℤ)] frameGL N _ cuspOneMatrix) w=_
  rw [hf,SlashAction.slash_mul,ModularForm.slash_apply]
  simp only [UpperHalfPlane.σ,SpecialLinearGroup.det_mapGL,one_pos,if_true,act,d,
    show 2*(r:ℤ)=((2*r:ℕ):ℤ) by push_cast;rfl,zpow_neg,zpow_natCast,inv_pow,inv_inv,pow_mul,sq]
  simp [mul_comm]

def offset {N : ℕ} [NeZero N] (C : ℕ+) (u : ZMod (C:ℕ)) (j : ZMod N) : ℝ :=
  (Dval C u j:ℝ)/((C:ℝ)*N)

def slot {N : ℕ} [NeZero N] (r m : ℕ) (C : ℕ+) (u : ZMod (C:ℕ)) (j : ZMod N) (x : ℝ) : ℂ :=
  if IsUnit u ∧ (N:ℤ)∣(C:ℤ)-Dval C u j then
    chi C ((m:ℤ)*(u⁻¹).val) *
      ((1/(modulus N C:ℂ)^(2*r))*translated (2*r-1) (B*m/(modulus N C:ℂ)^2)
        (point (x+offset C u j))) else 0

theorem scaled_den (N r m : ℕ) [NeZero N] (hr : 0<r) (C : ℕ+) (x : ℝ) :
    (N:ℂ)^r*denominator N (2*r) m cuspOneMatrix C (zeroS,scaledPoint N (point x)) =
      ∑ u : ZMod (C:ℕ),∑ j : ZMod N,slot r m C u j x := by
  classical
  have hN : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  have hc : 0<(C:ℝ) := by exact_mod_cast C.property
  have hs : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt hN.le
  have H : (modulus N C)^2=(C:ℝ)^2*N := by rw [modulus,mul_pow,hs];ring
  have Y : (scaledPoint N (point x)).im=(N:ℝ) := by simp [scaledPoint,point,Complex.mul_im]
  have X : (scaledPoint N (point x)).re=(N:ℝ)*x := by simp [scaledPoint,point,Complex.mul_re]
  have f : (N:ℂ)^r*((1/(C:ℝ)^(2*r)*(C:ℝ)^(-2*(zeroS:ℝ))*
      (N:ℝ)^(-((2*r:ℕ):ℝ)-(zeroS:ℝ)):ℝ):ℂ)=1/(modulus N C:ℂ)^(2*r) := by
    simp only [zeroS,Subtype.coe_mk,mul_zero,Real.rpow_zero,mul_one,sub_zero,
      Real.rpow_neg hN.le,Real.rpow_natCast,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_div,
      Complex.ofReal_one,Complex.ofReal_pow,Complex.ofReal_natCast]
    have HH := congrArg Complex.ofReal H
    push_cast at HH
    rw [pow_mul (modulus N C:ℂ) 2 r,HH,mul_pow,← pow_mul,two_mul r,pow_add]
    field_simp [show (N:ℂ)≠0 by exact_mod_cast hN.ne',show (C:ℂ)≠0 by exact_mod_cast hc.ne']
    <;>ring
  have T (u : ZMod (C:ℕ)) (j : ZMod N) (l : ℤ) :
      ((N:ℝ)*x+(Dval C u j:ℝ)/C+(l:ℝ)*N)/(N:ℝ)=x+offset C u j+l := by
    dsimp [offset];field_simp [hN.ne',hc.ne'];ring
  rw [denominator]
  simp only [Y,X,← mul_assoc,f,Finset.mul_sum]
  apply Finset.sum_congr rfl;intro u _
  by_cases hu : IsUnit u
  · simp only [hu,if_true,Finset.mul_sum]
    apply Finset.sum_congr rfl;intro j _
    by_cases hj : (N:ℤ)∣(C:ℤ)-Dval C u j
    · simp only [slot,hu,hj,and_self,if_true,cuspOneMatrix,Matrix.of_apply,Matrix.cons_val_one,
        Matrix.cons_val_zero,mul_one,translated,show 2*r-1+1=2*r by omega]
      rw [show (1/(modulus N C:ℂ)^(2*r))*(chi C ((m:ℤ)*(u⁻¹).val)*_) =
        chi C ((m:ℤ)*(u⁻¹).val)*((1/(modulus N C:ℂ)^(2*r))*_) by ring]
      congr 2;apply tsum_congr;intro l
      simp only [kernel,realPower,resolvent,T,Mval,Y,zeroS,Subtype.coe_mk,neg_zero,Real.rpow_zero,
        Complex.ofReal_one,mul_one,point,Complex.ofReal_add,Complex.ofReal_intCast,inv_pow,B,one_div]
      have H' := congrArg Complex.ofReal H
      push_cast at H'
      rw [H'];push_cast
      ring_nf
    · simp [slot,hu,hj,cuspOneMatrix]
  · simp [slot,hu]

def orbital (r m h : ℕ) (C : ℝ) : ℂ :=
  ((2*Real.pi/C:ℝ):ℂ)*(-I)^(2*r)*((Real.sqrt h/Real.sqrt m:ℝ):ℂ)^(2*r-1)*
    generalJ ((2*r-1:ℕ):ℂ) (argument (Real.sqrt m) (Real.sqrt h) C)

theorem den_mode (N r m h : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (hh : 0<h) (C : ℕ+) :
    horizontal h (fun x => (N:ℂ)^r*denominator N (2*r) m cuspOneMatrix C (zeroS,scaledPoint N (point x))) =
      cuspSum N C cuspOneMatrix m h*orbital r m h (modulus N C) := by
  classical
  have ha : 1≤2*r-1 := by omega
  have cc (u : ZMod (C:ℕ)) (j : ZMod N) : Continuous (slot r m C u j) := by
    unfold slot;split_ifs
    · exact continuous_const.mul (continuous_const.mul (translated_continuous ha _ _))
    · exact continuous_const
  simp_rw [scaled_den N r m hr C]
  rw [horizontal_finite _ _ (fun u => continuous_finsetSum _ (fun j _ => cc u j))]
  simp_rw [horizontal_finite _ _ (cc _)]
  rw [cuspSum,Finset.sum_mul]
  apply Finset.sum_congr rfl;intro u _
  by_cases hu : IsUnit u
  · simp only [hu,if_true,Finset.sum_mul]
    apply Finset.sum_congr rfl;intro j _
    by_cases hj : (N:ℤ)∣(C:ℤ)-Dval C u j
    · simp only [slot,hu,hj,and_self,if_true,cuspOneMatrix,Matrix.of_apply,Matrix.cons_val_one,
        Matrix.cons_val_zero,mul_one,horizontal_const_mul]
      have hb := translated_bessel ha hm hh (modulus_pos N C) (offset C u j)
      rw [show 2*r-1+1=2*r by omega] at hb
      rw [hb];unfold residuePhase orbital offset
      have he : (h:ℝ)*((Dval C u j:ℝ)/((C:ℝ)*N))=(h:ℝ)*(Dval C u j:ℝ)/((C:ℝ)*N) := by ring
      rw [he];ring
    · simp [slot,hu,hj,cuspOneMatrix,horizontal]
  · simp [slot,hu,horizontal]

end
end ImbalancedChen.Part3.OriginalPeterssonNormalizedOrbits20261112
