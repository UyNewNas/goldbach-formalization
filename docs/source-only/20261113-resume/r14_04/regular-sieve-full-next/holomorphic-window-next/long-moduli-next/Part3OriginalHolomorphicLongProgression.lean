import ImbalancedChen.Part3OriginalHolomorphicLongModulus
import ImbalancedChen.Part3SmoothProgressionError

/-! Absolute convergence of the full long-modulus progression of the
corrected angular window, including the geometric trace factor 1/c. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicLongProgression20261113

open Real
open OriginalHolomorphicOddWindow20261113 (amplitudeConstant)
open OriginalHolomorphicPhysicalCosine20261113 (form argument)
open OriginalHolomorphicLongModulus20261113 (rawWindow longConstant long_modulus_bound)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)
open CommonSmoothCutoff (poisson_decay_summable_nat poisson_decay_tsum_nat_le)

def longTerm (M z : ℕ) (t : ℝ) (a b : ℕ → ℂ) (j : ℕ) : ℂ :=
  let c := z*(j+1)
  if M≤c then form M c a b (fun m n => (rawWindow t (argument c m n):ℂ))/(c:ℂ) else 0

private theorem scalar_comparison {r d : ℝ} (hr : 0<r) (hd : 0<d) (h : r≤d) :
    (r/d)^3 ≤ 4*r*((1/r)/(1+(1/r)*d)^2) := by
  have step : 1+(1/r)*d=(r+d)/r := by field_simp [hr.ne'] <;> ring
  have e : r*(r+d)^2≤4*d^3 := by
    have u := mul_le_mul_of_nonneg_right h (sq_nonneg (r+d))
    have v := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg hr.le hd.le)
        (show r+d≤2*d by linarith only [h]) 2) hd.le
    nlinarith only [u,v]
  calc
    (r/d)^3 ≤ 4*r^2/(r+d)^2 := by
      rw [div_pow]
      apply (div_le_div_iff₀ (pow_pos hd 3) (sq_pos_of_pos (add_pos hr hd))).mpr
      have w := mul_le_mul_of_nonneg_left e (sq_nonneg r)
      nlinarith only [w]
    _ = _ := by rw [step]; field_simp [hr.ne',(add_pos hr hd).ne'] <;> ring

/-- Every multiple of the original positive level z is present once.
The sum of absolute values pays one factor M/z at every original dyadic
length and for all 0<t≤1. -/
theorem long_progression_bound {M z : ℕ} (hM : 0<M) (hz : 0<z)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    Summable (fun j => ‖longTerm M z t a b j‖) ∧
    (∑' j, ‖longTerm M z t a b j‖) ≤
      4*longConstant*((M:ℝ)/z)*sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b) := by
  let r : ℝ := M/(z:ℝ)
  let K := longConstant*sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b)
  let decay : ℕ → ℝ := fun j => (1/r)/(1+(1/r)*((j:ℝ)+1))^2
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have zp : 0<(z:ℝ) := by exact_mod_cast hz
  have rp : 0<r := div_pos mp zp
  have kp : 0≤K := by dsimp only [K,longConstant,amplitudeConstant]; positivity
  have b0 : 0≤4*K*r := by positivity
  have hi : Summable decay := poisson_decay_summable_nat (one_div_pos.mpr rp)
  have total : (∑' j,decay j)≤1 := poisson_decay_tsum_nat_le (one_div_pos.mpr rp)
  have per (j : ℕ) : ‖longTerm M z t a b j‖ ≤ (4*K*r)*decay j := by
    let c := z*(j+1)
    let d := (j:ℝ)+1
    have d0 : 0<d := by dsimp [d]; positivity
    have c0 : 0<c := Nat.mul_pos hz (by omega)
    have cd : (c:ℝ)=(z:ℝ)*d := by simp [c,d]
    have cr : 0<(c:ℝ) := by exact_mod_cast c0
    letI : NeZero c := ⟨c0.ne'⟩
    by_cases hm : M≤c
    · have rd : r≤d := (div_le_iff₀ zp).mpr (by
        have mc : (M:ℝ)≤c := by exact_mod_cast hm
        rw [cd] at mc
        linarith only [mc])
      have h := div_le_div_of_nonneg_right (long_modulus_bound hM hm ht ht1 a b) cr.le
      have e : longConstant*((M:ℝ)^3/(c:ℝ)^2)*sqrt (dyadEnergy M a)*
          sqrt (dyadEnergy M b)/c = K*(r/d)^3 := by
        rw [cd]
        dsimp only [r,K]
        field_simp [zp.ne',d0.ne'] <;> ring
      rw [e] at h
      have W := mul_le_mul_of_nonneg_left (scalar_comparison rp d0 rd) kp
      change ‖if M≤c then _ else _‖ ≤ _
      rw [if_pos hm,norm_div,Complex.norm_natCast]
      apply h.trans
      apply W.trans_eq
      dsimp only [decay,d]
      ring
    · change ‖if M≤c then _ else _‖ ≤ _
      rw [if_neg hm,norm_zero]
      exact mul_nonneg b0 (div_nonneg (one_div_pos.mpr rp).le (sq_nonneg _))
  have major : Summable (fun j => (4*K*r)*decay j) := hi.const_mul _
  have actual := major.of_nonneg_of_le (fun j => norm_nonneg (longTerm M z t a b j)) per
  refine ⟨actual,?_⟩
  apply (actual.tsum_le_tsum per major).trans
  rw [tsum_mul_left]
  have cost := mul_le_mul_of_nonneg_left total b0
  dsimp only [K,r] at cost
  convert cost using 1 <;> ring

end ImbalancedChen.Part3.OriginalHolomorphicLongProgression20261113
end
