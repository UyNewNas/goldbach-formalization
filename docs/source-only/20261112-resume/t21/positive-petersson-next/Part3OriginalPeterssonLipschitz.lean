import ImbalancedChen.Part3ActualGeneralJBessel
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace ImbalancedChen.Part3.OriginalPeterssonLipschitz20261112

noncomputable section
open Complex UpperHalfPlane
open scoped UpperHalfPlane BigOperators
open ActualGeneralJBesselSourceOnly GeneralComplexISeriesSourceOnly

def B : ℂ := -2*Real.pi*I
def Q (w : ℍ) : ℂ := Complex.exp (2*Real.pi*I*(w:ℂ))

def translated (a : ℕ) (v : ℂ) (w : ℍ) : ℂ :=
  ∑' l : ℤ, (1/((w:ℂ)+l)^(a+1)) * exp (v/((w:ℂ)+l))

def modeTerm (a : ℕ) (v : ℂ) (n t : ℕ) : ℂ :=
  (v^t/t.factorial) * (B^(a+t+1)/(a+t).factorial) * (n:ℂ)^(a+t)

private def spatial (a : ℕ) (v : ℂ) (w : ℍ) (l : ℤ) (t : ℕ) : ℂ :=
  (1/((w:ℂ)+l)^(a+1))*((v/((w:ℂ)+l))^t/t.factorial)

private theorem spatial_abs {a : ℕ} (ha : 1≤a) (v : ℂ) (w : ℍ) :
    Summable fun p : ℤ×ℕ => ‖spatial a v w p.1 p.2‖ := by
  let L := fun l : ℤ => ‖1/((w:ℂ)+l)^(a+1)‖
  have hL : Summable L := by
    apply summable_norm_iff.mpr
    simpa [one_div] using EisensteinSeries.linear_right_summable (w:ℂ) 1
      (by omega : (2:ℤ)≤((a+1:ℕ):ℤ))
  have h := hL.mul_of_nonneg (Real.summable_pow_div_factorial (‖v‖/w.im))
    (fun _ => norm_nonneg _) (fun _ => by positivity)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) ?_ h
  intro ⟨l,t⟩
  change ‖spatial a v w l t‖ ≤ L l * _
  rw [spatial,norm_mul,norm_div,norm_pow,norm_div,Complex.norm_natCast]
  have hlow : w.im ≤ ‖(w:ℂ)+l‖ := by
    simpa using Complex.im_le_norm ((w:ℂ)+l)
  gcongr

private theorem translated_taylor {a : ℕ} (ha : 1≤a) (v : ℂ) (w : ℍ) :
    translated a v w =
      ∑' t : ℕ, ∑' n : ℕ, modeTerm a v n t * (Q w)^n := by
  calc
    _ = ∑' l : ℤ, ∑' t : ℕ, spatial a v w l t := by
      apply tsum_congr; intro l
      rw [Complex.exp_eq_exp_ℂ,NormedSpace.exp_eq_tsum_div,← tsum_mul_left]
    _ = ∑' t : ℕ, ∑' l : ℤ, spatial a v w l t := (spatial_abs ha v w).of_norm.tsum_comm
    _ = _ := by
      apply tsum_congr; intro t
      have he (l : ℤ) : spatial a v w l t =
          (v^t/t.factorial)*(1/((w:ℂ)+l)^(a+t+1)) := by
        rw [spatial,show a+t+1=(a+1)+t by omega,pow_add,div_pow]
        simp only [div_eq_mul_inv,mul_inv_rev];ring
      simp_rw [he]
      rw [tsum_mul_left,EisensteinSeries.qExpansion_identity (by omega : 1≤a+t),
        ← mul_assoc,← tsum_mul_left]
      apply tsum_congr; intro n
      dsimp only [modeTerm,B,Q]; ring

theorem freq_abs {a : ℕ} (v : ℂ) (w : ℍ) :
    Summable fun p : ℕ×ℕ => ‖modeTerm a v p.2 p.1 * (Q w)^p.2‖ := by
  let b : ℝ := Real.pi*w.im
  have hb : 0<b := mul_pos Real.pi_pos w.im_pos
  let U := fun t : ℕ => (‖v‖*‖B‖/b)^t/(t.factorial:ℝ)
  let V := fun n : ℕ => ‖B‖^(a+1)*((n:ℝ)^a*Real.exp (-b*n))
  have hU : Summable U := Real.summable_pow_div_factorial _
  have hV : Summable V := (Real.summable_pow_mul_exp_neg_nat_mul a hb).mul_left _
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (hU.mul_of_nonneg hV (fun _ => by dsimp [U]; positivity) (fun _ => by dsimp [V]; positivity))
  intro ⟨t,n⟩
  have hq : ‖(Q w)^n‖=Real.exp (-b*n)*Real.exp (-b*n) := by
    rw [norm_pow,Q,norm_exp,← Real.exp_nat_mul,← Real.exp_add]
    congr 1; simp [b,Complex.mul_re,Complex.mul_im]; ring
  have hfac : (t.factorial:ℝ)≤(a+t).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : t≤a+t)
  have hp : (b*(n:ℝ))^t/(↑((a+t).factorial):ℝ) ≤ Real.exp (b*n) :=
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hfac).trans
      (Real.pow_div_factorial_le_exp (by positivity) t)
  have hpt : ((n:ℝ)^t/(↑((a+t).factorial):ℝ))*Real.exp (-b*n) ≤ (b^t)⁻¹ := by
    rw [show -b*(n:ℝ)=-(b*n) by ring,Real.exp_neg]
    field_simp [hb.ne',(Real.exp_pos _).ne'] at hp ⊢
    simpa [mul_pow,mul_comm,mul_assoc,mul_left_comm] using hp
  change ‖modeTerm a v n t * (Q w)^n‖ ≤ U t*V n
  rw [norm_mul,hq,modeTerm]
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_natCast]
  rw [show a+t+1=(a+1)+t by omega,pow_add ‖B‖ (a+1) t,pow_add (n:ℝ) a t]
  dsimp only [U,V]
  rw [div_pow,mul_pow]
  calc
    _ = (‖v‖^t/t.factorial * ‖B‖^(a+1)*‖B‖^t*(n:ℝ)^a*Real.exp (-b*n)) *
          (((n:ℝ)^t/(↑((a+t).factorial):ℝ))*Real.exp (-b*n)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hpt (by positivity)).trans_eq (by ring)

/-- Full ordinary q-series of the orbit kernel at a fixed positive denominator. -/
theorem translated_modes {a : ℕ} (ha : 1≤a) (v : ℂ) (w : ℍ) :
    translated a v w = ∑' n : ℕ, (∑' t : ℕ, modeTerm a v n t) * (Q w)^n := by
  rw [translated_taylor ha]
  convert (freq_abs (a:=a) v w).of_norm.tsum_comm using 1
  simp_rw [tsum_mul_right]

theorem mode_zero {a : ℕ} (ha : 1≤a) (v : ℂ) (t : ℕ) : modeTerm a v 0 t=0 := by
  simp [modeTerm,show a+t≠0 by omega]

def argument (u v C : ℝ) : ℝ := 4*Real.pi*u*v/C

/-- Here u and v are the square roots of the two *positive* frequency marks. -/
theorem mode_bessel (a m n : ℕ) {C : ℝ} (hC : 0<C) (hm : 0<m) (hn : 0<n) :
    let u := Real.sqrt m
    let v := Real.sqrt n
    let V := B*m/(C:ℂ)^2
    HasSum (fun t => (1/(C:ℂ)^(a+1))*modeTerm a V n t)
      ((2*Real.pi/C:ℝ)*(-I)^(a+1)*((v/u:ℝ):ℂ)^a*
        generalJ (a:ℂ) (argument u v C)) := by
  dsimp only
  let u := Real.sqrt (m:ℝ)
  let v := Real.sqrt (n:ℝ)
  let q := argument u v C
  let x := ((q/2:ℝ):ℂ)
  have hu : (u:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  have hc : (C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hC.ne'
  have hu2 : (u:ℂ)^2 = (m:ℂ) := by exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg m)
  have hv2 : (v:ℂ)^2 = (n:ℂ) := by exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n)
  let scale : ℂ := ((2*Real.pi/C:ℝ):ℂ)*(-I)^(a+1)*((v/u:ℝ):ℂ)^a
  have harg : x=(2*Real.pi*(u:ℂ)*(v:ℂ))/(C:ℂ) := by dsimp [x,q,argument];push_cast;ring
  have hl : B*m/(C:ℂ)^2*B*n = (-1:ℂ)*x^2 := by
    rw [harg,← hu2,← hv2]
    dsimp [B]
    field_simp [hc]
    linear_combination (4*(Real.pi:ℂ)^2*(u:ℂ)^2*(v:ℂ)^2)*Complex.I_sq
  have hbase : (1/(C:ℂ)^(a+1))*B^(a+1)*(n:ℂ)^a = scale*x^a := by
    rw [harg,← hv2]
    dsimp [scale,B]
    push_cast
    rw [show -2*(Real.pi:ℂ)*I=(2*Real.pi)*(-I) by ring,mul_pow]
    simp only [pow_succ,div_pow,mul_pow]
    field_simp [hc,hu]
    <;> ring
  apply ((generalJ_hasSum (by simp : -1<(a:ℂ).re) q).mul_left scale).congr_fun
  intro t
  symm
  have hΓ : Complex.Gamma ((t:ℂ)+(a:ℂ)+1) = ((a+t).factorial:ℂ) := by
    simpa only [Nat.cast_add,add_comm (a:ℂ) t] using Complex.Gamma_nat_eq_factorial (a+t)
  rw [generalJTerm,Complex.cpow_natCast,generalICoeff,hΓ,modeTerm]
  change scale*(x^a*((-1:ℂ)^t*_*x^(2*t))) = _
  rw [show a+t+1=(a+1)+t by omega,pow_add B (a+1) t,pow_add (n:ℂ) a t,pow_mul x 2 t]
  calc
    _ = (scale*x^a)*((-1:ℂ)*x^2)^t / ((t.factorial:ℂ)*(a+t).factorial) := by
      rw [mul_pow];ring
    _ = _ := by rw [← hl,← hbase];simp only [mul_pow];ring

end
end ImbalancedChen.Part3.OriginalPeterssonLipschitz20261112
