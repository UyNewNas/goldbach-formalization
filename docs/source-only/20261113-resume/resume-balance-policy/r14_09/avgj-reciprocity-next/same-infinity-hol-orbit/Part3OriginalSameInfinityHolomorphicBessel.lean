import ImbalancedChen.Part3OriginalSameInfinityHolomorphicOrbit
import Batteries.Tactic.OpenPrivate

/-! Evaluate the surviving same-frame Fourier slot using the published
translated Bessel formula at period one. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityHolomorphicBessel20261113
noncomputable section
open Set Finset Complex MeasureTheory AddCircle UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane FourierTransform
open OriginalSameInfinityHolomorphicOrbit20261113 OriginalHeckeCuspSeries20261112
open OriginalHeckePoisson20261112 OriginalHeckeFourierKernel20261112 OriginalHeckeLimitFamily20261112
open OriginalSmoothPoissonTail OriginalPeterssonHorizontalMode20261112 OriginalPeterssonLipschitz20261112
open OriginalPeterssonNormalizedOrbits20261112 (orbital) P3Period64NativeReconstructionSourceOnly (e norm_e)
open private char_eq from ImbalancedChen.Part3OriginalPeterssonHorizontalMode

private def coefficient (k m : ℕ) (C : ℕ+) (n : ℤ) : ℂ :=
  transformed 1 k m C n (zeroS,point 0)

private theorem coeff_at (k m : ℕ) (C : ℕ+) (n : ℤ) (x : ℝ) :
    transformed 1 k m C n (zeroS,point x)=coefficient k m C n := by
  simp [coefficient,transformed,Mval,sample,point]

private theorem character (h : ℕ) (n : ℤ) (z : ℂ) :
    horizontal h (fun x => z*e ((n:ℝ)*x))=if n=(h:ℤ) then (amplitude h)⁻¹*z else 0 := by
  have H := congrFun (fourierCoeff_fourier (T:=1) n) (h:ℤ)
  rw [fourierCoeff_eq_intervalIntegral _ _ (0:ℝ)] at H
  simp only [zero_add,div_one,one_smul,smul_eq_mul,Pi.single_apply] at H
  have I : (∫ x in (0:ℝ)..1,e (-((h:ℝ)*x))*e ((n:ℝ)*x))=if n=(h:ℤ) then 1 else 0 := by
    simpa only [←char_eq,Int.cast_neg,Int.cast_natCast,neg_mul,eq_comm (a := (h:ℤ))] using H
  rw [horizontal,show (fun x : ℝ => e (-((h:ℝ)*x))*(z*e ((n:ℝ)*x)))=
    fun x => z*(e (-((h:ℝ)*x))*e ((n:ℝ)*x)) from funext fun _ => by ring,
    intervalIntegral.integral_const_mul,I]
  split_ifs <;> simp

private theorem extract (h : ℕ) (f : ℝ→ℂ) (v : ℤ→ℂ) (hv : Summable (fun n => ‖v n‖))
    (hf : ∀ x,HasSum (fun n : ℤ => v n*e ((n:ℝ)*x)) (f x)) :
    horizontal h f=(amplitude h)⁻¹*v (h:ℤ) := by
  have T := horizontal_hasSum h _ f (fun n => by unfold e; fun_prop) hv
    (fun n x => by simp [norm_e]) hf
  simp_rw [character] at T
  simpa using T.tsum_eq.symm

private theorem coeff_summable (k m : ℕ) (hk : 2≤k) (C : ℕ+) :
    Summable (fun n : ℤ => ‖coefficient k m C n‖) := by
  obtain ⟨A,_,bound⟩ := transformed_price 1 k m hk (by norm_num : (0:ℝ)<1)
  exact (freqPrice_summable.mul_left A).of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => bound C n (zeroS,point 0) (by simp [point]))

private theorem unshifted_mode (r m h : ℕ) (hr : 0<r) (hm : 0<m) (hh : 0<h) (C : ℕ+) :
    (amplitude h)⁻¹*((1/(C:ℂ)^(2*r))*coefficient (2*r) m C (h:ℤ))=orbital r m h (C:ℝ) := by
  have hk : 2≤2*r := by omega
  have a : 1≤2*r-1 := by omega
  have s : 2*r-1+1=2*r := by omega
  let f (x : ℝ) := translated (2*r-1) (B*m/(C:ℂ)^2) (point x)
  have P (x : ℝ) : HasSum (fun n : ℤ => coefficient (2*r) m C n*e ((n:ℝ)*x)) (f x) := by
    have H := periodization 1 (2*r) m hk C (zeroS,point x) x
    have Y : (point x).im=1 := by simp [point]
    have h (l : ℤ) : kernel (2*r) zeroS.val (Mval m C (point x)) (x+(l:ℝ)) =
        (1/((point x:ℂ)+l)^(2*r))*exp ((B*m/(C:ℂ)^2)/((point x:ℂ)+l)) := by
      have den : ((x+(l:ℝ):ℝ):ℂ)+I=(point x:ℂ)+l := by
        simp only [point,Complex.ofReal_add,Complex.ofReal_intCast]
        ring
      simp only [kernel,realPower,resolvent,Mval,Y,zeroS,Subtype.coe_mk,neg_zero,Real.rpow_zero,
        Complex.ofReal_one,mul_one,den,B,one_div,inv_pow,div_eq_mul_inv]
      push_cast
      ring_nf
    simp only [Y,Nat.cast_one,div_one,Complex.ofReal_one,one_mul,mul_one,coeff_at,h] at H
    simpa only [f,translated,s] using H
  have E := extract h f (coefficient (2*r) m C) (coeff_summable _ _ hk _) P
  have M := translated_bessel a hm hh (show 0<(C:ℝ) by exact_mod_cast C.property) 0
  rw [s] at M
  simp only [add_zero,mul_zero,show e 0=1 by simp [e],one_mul,horizontal_const_mul] at M
  change (1/(C:ℂ)^(2*r))*horizontal h f=orbital r m h (C:ℝ) at M
  rw [E] at M
  linear_combination M

/-- Exact same-infinity positive Bessel orbit at every modulus, including
all exceptional level divisors and weight two. -/
theorem same_infinity_den_mode (N r m h : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (hh : 0<h) (C : ℕ+) :
    horizontal h (fun x => denominator N (2*r) m 1 C (zeroS,point x)) =
      if N∣C.val then kloosterman C.val (h:ℤ) (m:ℤ)*orbital r m h (C:ℝ) else 0 := by
  have hk : 2≤2*r := by omega
  by_cases good : N∣C.val
  · rw [if_pos good]
    let V (n : ℤ) := kloosterman C.val n (m:ℤ)*((1/(C:ℂ)^(2*r))*coefficient (2*r) m C n)
    have sum : Summable (fun n => ‖V n‖) := by
      apply ((coeff_summable _ _ hk C).mul_left ((C:ℝ)*‖1/(C:ℂ)^(2*r)‖)).of_nonneg_of_le
        (fun _ => norm_nonneg _)
      intro n
      dsimp only [V]
      rw [norm_mul,norm_mul,←mul_assoc]
      gcongr
      exact kloosterman_norm_le _ _ _
    have P (x : ℝ) : HasSum (fun n : ℤ => V n*e ((n:ℝ)*x)) (denominator N (2*r) m 1 C (zeroS,point x)) := by
      have abs := sum.of_nonneg_of_le (fun n => norm_nonneg (V n*e ((n:ℝ)*x)))
        (fun n => by simp [norm_e])
      have eq : (∑' n : ℤ, V n*e ((n:ℝ)*x))=denominator N (2*r) m 1 C (zeroS,point x) := by
        rw [identity_denominator _ _ _ hk,if_pos good]
        apply tsum_congr
        intro n
        have imx : (point x).im=1 := by simp [point]
        have rex : (point x).re=x := by simp [point]
        simp [V,coeff_at,imx,rex,zeroS] <;> ring
      exact eq ▸ abs.of_norm.hasSum
    rw [extract h _ V sum P,←unshifted_mode r m h hr hm hh C]
    dsimp [V]
    ring
  · simp [identity_denominator N (2*r) m hk C,good,horizontal]

end
end ImbalancedChen.Part3.OriginalSameInfinityHolomorphicBessel20261113
