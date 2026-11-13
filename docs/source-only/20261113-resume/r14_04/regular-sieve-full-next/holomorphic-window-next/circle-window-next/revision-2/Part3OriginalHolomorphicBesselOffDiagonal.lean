import ImbalancedChen.Part3OriginalHolomorphicQuarterProjection
import ImbalancedChen.Part3OriginalHolomorphicAngularOffDiagonal
import ImbalancedChen.Part3ActualGeneralJWronskian

/-! The exact odd-order Bessel weights of Petersson, on all original
positive level multiples and arbitrary complex coefficient rows. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicBesselOffDiagonal20261113
open Finset Real
open ActualGeneralJBesselSourceOnly (generalJ)
open ActualGeneralJWronskian20261025a (conj_generalJ)
open OriginalHolomorphicPoissonHeight20261113 (orderTerm poisson_height_sum)
open OriginalHolomorphicCircleProjection20261113 (imaginaryHeight)
open OriginalHolomorphicQuarterProjection20261113 (corrected_native_window)
open OriginalHolomorphicOddWindow20261113 (weight)
open OriginalHolomorphicLongModulus20261113 (rawWindow)
open OriginalHolomorphicPhysicalCosine20261113 (form argument scale)
open OriginalHolomorphicShortOscillation20261113 (rowProduct)
open OriginalHolomorphicAngularOffDiagonal20261113 (angularTerm cost angular_off_diagonal)

def nativeTerm (t x : ℝ) (h : ℕ) : ℂ :=
  if Odd h then (((h:ℝ)*weight t h:ℝ):ℂ)*(Complex.I^(h+1)*generalJ (h:ℂ) x) else 0

def nativeWindow (t x : ℝ) : ℂ := 2*∑' h, nativeTerm t x h

private theorem imag_term (t : ℝ) {x : ℝ} (hx : 0<x) (h : ℕ) :
    ((-((orderTerm t x h).im-exp (2-t)*(orderTerm 2 x h).im):ℝ):ℂ)=nativeTerm t x h := by
  let g := (generalJ (h:ℂ) x).re
  have realJ : (g:ℂ)=generalJ (h:ℂ) x := by
    apply Complex.conj_eq_iff_re.mp
    simpa only [map_natCast] using conj_generalJ (h:ℂ) hx
  have rt : (Real.exp (-t))^h=Real.exp (-(h:ℝ)*t) := by rw [←Real.exp_nat_mul]; congr 1 <;> ring
  have r2 : (Real.exp (-(2:ℝ)))^h=Real.exp (-2*(h:ℝ)) := by rw [←Real.exp_nat_mul]; congr 1 <;> ring
  let k := h/2
  have parity : h=2*k ∨ h=2*k+1 := by dsimp only [k]; omega
  have i2 : Complex.I^(2*k)=(((-1:ℝ)^k:ℝ):ℂ) := by
    rw [pow_mul,Complex.I_sq,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  rcases parity with even|odd
  · have e : ¬Odd h := by
      rintro ⟨d,hd⟩
      omega
    have ph : Complex.I^h=(((-1:ℝ)^k:ℝ):ℂ) := (congrArg (fun n : ℕ => Complex.I^n) even).trans i2
    rw [nativeTerm,if_neg e]
    simp only [orderTerm,ph,←realJ,←Complex.ofReal_mul,Complex.ofReal_im,mul_zero,sub_zero,
      neg_zero,Complex.ofReal_zero]
  · have e : Odd h := ⟨k,by omega⟩
    have ph : Complex.I^h=(((-1:ℝ)^k:ℝ):ℂ)*Complex.I := by
      calc
        _ = Complex.I^(2*k+1) := congrArg (fun n : ℕ => Complex.I^n) odd
        _ = _ := by rw [pow_succ,i2]
    have pk : Complex.I^(h+1)= -(((-1:ℝ)^k:ℝ):ℂ) := by
      rw [pow_succ,ph,mul_assoc,←sq,Complex.I_sq]; ring
    rw [nativeTerm,if_pos e]
    simp only [orderTerm,ph,pk,←realJ,rt,r2,weight,Complex.mul_im,Complex.mul_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
    push_cast <;> ring

/-- Actual corrected sum of odd natural h, including the h=1 cancellation,
equals the physical quarter-circle window with its full -2/π multiplier. -/
theorem native_window_eq {t x : ℝ} (ht : 0<t) (hx : 0<x) :
    Summable (nativeTerm t x) ∧ nativeWindow t x=(-(2/π)*rawWindow t x:ℝ) := by
  have imag (u : ℝ) (hu : 0<u) :
      HasSum (fun h => (orderTerm u x h).im) (imaginaryHeight u x) := by
    exact Complex.imCLM.hasSum (poisson_height_sum hu x).summable.hasSum
  have R := ((imag t ht).sub ((imag 2 (by norm_num)).mul_left (exp (2-t)))).neg
  have J : HasSum (nativeTerm t x) ((-(imaginaryHeight t x-exp (2-t)*imaginaryHeight 2 x):ℝ):ℂ) := by
    apply (Complex.ofRealCLM.hasSum R).congr_fun
    intro h
    exact (imag_term t hx h).symm
  refine ⟨J.summable,?_⟩
  rw [nativeWindow,J.tsum_eq,←corrected_native_window ht x]
  push_cast <;> ring

def geometricTerm (M z : ℕ) (t : ℝ) (a b : ℕ → ℂ) (j : ℕ) : ℂ :=
  let c := z*(j+1)
  form M c a b (fun m n => nativeWindow t (argument c m n))/(c:ℂ)

private theorem term_identity {M z : ℕ} (hM : 0<M) (hz : 0<z) {t : ℝ} (ht : 0<t)
    (a b : ℕ → ℂ) (j : ℕ) :
    geometricTerm M z t a b j = ((-(2/π):ℝ):ℂ)*angularTerm M z t a b j := by
  let c := z*(j+1)
  have cp : 0<c := Nat.mul_pos hz (by omega)
  have sc : 0<scale c := div_pos (mul_pos (by norm_num) pi_pos) (by exact_mod_cast cp)
  have pos (i k : ℕ) : 0<argument c (M+i) (M+k) := mul_pos
    (mul_pos sc (sqrt_pos.mpr (by exact_mod_cast (show 0<M+i by omega))))
    (sqrt_pos.mpr (by exact_mod_cast (show 0<M+k by omega)))
  dsimp only [geometricTerm,angularTerm,form]
  rw [←mul_div_assoc]
  apply congrArg (fun w : ℂ => w/(c:ℂ))
  simp only [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  rw [(native_window_eq ht (pos i k)).2,Complex.ofReal_mul]
  ring

theorem native_bessel_off_diagonal {e : ℝ} (he : 0<e) (M z : ℕ) (hM : 0<M) (hz : 0<z)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    Summable (fun j => ‖geometricTerm M z t a b j‖) ∧
    (∑' j, ‖geometricTerm M z t a b j‖) ≤
      ((2/π)*cost e)*((M:ℝ)^(1+e)/z)*rowProduct M a b := by
  obtain ⟨S,B⟩ := angular_off_diagonal he M z hM hz ht ht1 a b
  have k : 0≤2/π := by positivity
  have T (j : ℕ) : ‖geometricTerm M z t a b j‖=(2/π)*‖angularTerm M z t a b j‖ := by
    rw [term_identity hM hz ht,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_nonneg k]
  simp only [T]
  refine ⟨S.const_mul _,?_⟩
  rw [tsum_mul_left]
  convert mul_le_mul_of_nonneg_left B k using 1 <;> ring

end ImbalancedChen.Part3.OriginalHolomorphicBesselOffDiagonal20261113
end
