import ImbalancedChen.Part3OriginalRegularGaussianLongModulus
import ImbalancedChen.Part3OriginalHolomorphicAngularOffDiagonal

/-! Sum of the actual two-row Gaussian orbital coefficients over every
positive multiple of the given level. The cost has one power of K. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularGaussianOffDiagonal20261113
open Real Finset
open OriginalRegularGaussianSingleModulus20261113
open OriginalRegularGaussianLongModulus20261113
open OriginalRegularGaussianForms20261113 (numerator normalization normalization_pos)
open OriginalRegularGaussianMoment20261113 (bill bill_nonnegative)
open OriginalHolomorphicShortOscillation20261113 (rowProduct row_product_nonnegative)
open CommonSmoothCutoff (poisson_decay_summable_nat poisson_decay_tsum_nat_le)
open private positive_shift log_cost from ImbalancedChen.Part3OriginalHolomorphicAngularOffDiagonal

def entry (M z : ℕ) (K : ℝ) (a b : ℕ→ℂ) (j : ℕ) : ℂ :=
  let c := z*(j+1)
  numerator M c K a b/(c:ℂ)

def cost (e : ℝ) := shortConstant*exp (4*π)*(16*(1+2/e)^2)+4*longConstant

theorem short_nonnegative : 0≤shortConstant := by
  dsimp only [shortConstant];have b := bill_nonnegative;have n := normalization_pos;positivity

theorem long_nonnegative : 0≤longConstant := by
  dsimp only [longConstant];have b := bill_nonnegative;have n := normalization_pos;positivity

private theorem squared_tail {r d : ℝ} (hr : 0<r) (hd : 0<d) (h : r≤d) :
    (r/d)^2≤4*r*((1/r)/(1+(1/r)*d)^2) := by
  have step : 1+(1/r)*d=(r+d)/r := by field_simp [hr.ne'] <;> ring
  have e := pow_le_pow_left₀ (add_nonneg hr.le hd.le) (show r+d≤2*d by linarith only [h]) 2
  calc
    _ ≤ 4*r^2/(r+d)^2 := by
      rw [div_pow]
      apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos (add_pos hr hd))).mpr
      have w := mul_le_mul_of_nonneg_left e (sq_nonneg r)
      nlinarith only [w]
    _ = _ := by rw [step];field_simp [hr.ne',(add_pos hr hd).ne'] <;> ring

theorem full_progression {M z : ℕ} (hM : 0<M) (hz : 0<z) {K : ℝ} (hK : 2≤K)
    (a b : ℕ→ℂ) :
    Summable (fun j => ‖entry M z K a b j‖) ∧
      (∑' j,‖entry M z K a b j‖)≤
        shortConstant*K*M*price M*rowProduct M a b/z*(1+log M)+
        4*longConstant*((M:ℝ)/z)*rowProduct M a b := by
  let E := rowProduct M a b
  let r : ℝ := M/(z:ℝ)
  let S := shortConstant*K*M*price M*E/z
  let V := (4*longConstant*r*E)
  let U := fun j : ℕ => if j<M then S/((j:ℝ)+1) else 0
  let D := fun j : ℕ => (1/r)/(1+(1/r)*((j:ℝ)+1))^2
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have zp : 0<(z:ℝ) := by exact_mod_cast hz
  have kp : 0<K := by linarith only [hK]
  have p0 := (exp_pos _).le.trans (price_exp hM)
  have rp : 0<r := div_pos mp zp
  have e0 : 0≤E := row_product_nonnegative M a b
  have s0 : 0≤S := by dsimp only [S];have h := short_nonnegative;positivity
  have v0 : 0≤V := by dsimp only [V];have h := long_nonnegative;positivity
  have tail (j : ℕ) (h : j∉range M) : U j=0 := by simp only [U,if_neg (fun h' => h (mem_range.mpr h'))]
  have su : Summable U := summable_of_ne_finset_zero tail
  have sd : Summable D := poisson_decay_summable_nat (one_div_pos.mpr rp)
  have sm : (∑' j,U j)≤S*(1+log M) := by
    rw [tsum_eq_sum tail]
    calc
      _ = ∑ j∈range M,S*(1/((j+1:ℕ):ℝ)) := by
        apply sum_congr rfl
        intro j hj
        simp only [U,if_pos (mem_range.mp hj),Nat.cast_add,Nat.cast_one]
        ring
      _ = S*∑ d∈Icc 1 M,1/(d:ℝ) := by
        rw [Finset.mul_sum]
        exact positive_shift M (fun d => S*(1/(d:ℝ)))
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ s0
        calc
          _=(harmonic M:ℝ) := by
            simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
          _≤_ := harmonic_le_one_add_log M
  have total : (∑' j,D j)≤1 := poisson_decay_tsum_nat_le (one_div_pos.mpr rp)
  have per (j : ℕ) : ‖entry M z K a b j‖≤U j+V*D j := by
    let c := z*(j+1)
    let d : ℝ := (j:ℝ)+1
    have d0 : 0<d := by dsimp only [d];positivity
    have c0 : 0<c := Nat.mul_pos hz (by omega)
    letI : NeZero c := ⟨c0.ne'⟩
    have cr : 0<(c:ℝ) := by exact_mod_cast c0
    have cd : (c:ℝ)=(z:ℝ)*d := by simp [c,d]
    have vD : 0≤V*D j := mul_nonneg v0 (div_nonneg (one_div_pos.mpr rp).le (sq_nonneg _))
    have U0 : 0≤U j := by dsimp only [U];split <;> positivity
    change ‖numerator M c K a b/(c:ℂ)‖≤_
    rw [norm_div,Complex.norm_natCast]
    by_cases low : c<M
    · have le : j+1≤c := by simpa only [c,one_mul] using Nat.mul_le_mul_right (j+1) (show 1≤z from hz)
      have jj : j<M := by omega
      have bound := div_le_div_of_nonneg_right (short_modulus hM low.le hK a b) cr.le
      calc
        _ ≤ _ := bound
        _ = U j := by rw [cd];dsimp only [U,S,E,d];rw [if_pos jj];ring
        _ ≤ _ := le_add_of_nonneg_right vD
    · have high := le_of_not_gt low
      have rd : r≤d := (div_le_iff₀ zp).mpr (by
        have mc : (M:ℝ)≤c := by exact_mod_cast high
        rw [cd] at mc
        linarith only [mc])
      have bound := div_le_div_of_nonneg_right (long_modulus hM high hK a b) cr.le
      have scalar : longConstant*((M:ℝ)^2/c)*rowProduct M a b/c=longConstant*E*(r/d)^2 := by
        rw [cd];dsimp only [r,E];field_simp [zp.ne',d0.ne'] <;> ring
      rw [scalar] at bound
      have w := mul_le_mul_of_nonneg_left (squared_tail rp d0 rd) (mul_nonneg long_nonnegative e0)
      have cap : longConstant*E*(r/d)^2≤V*D j := by
        apply w.trans_eq;dsimp only [V,D,d];ring
      exact (bound.trans cap).trans (le_add_of_nonneg_left U0)
  have sh := su.add (sd.const_mul V)
  have act := sh.of_nonneg_of_le (fun j => norm_nonneg (entry M z K a b j)) per
  refine ⟨act,(act.tsum_le_tsum per sh).trans ?_⟩
  rw [su.tsum_add (sd.const_mul V),tsum_mul_left]
  have t := mul_le_mul_of_nonneg_left total v0
  dsimp only [S,V,r,E] at *
  nlinarith only [sm,t]

/-- Uniform K M^(1+e)/z bound for the *entire* native geometric
off-diagonal. The factor K cancels against the actual dyadic probe floor. -/
theorem gaussian_off_diagonal {e : ℝ} (he : 0<e) (M z : ℕ) (hM : 0<M) (hz : 0<z)
    {K : ℝ} (hK : 2≤K) (a b : ℕ→ℂ) :
    Summable (fun j => ‖entry M z K a b j‖) ∧
      (∑' j,‖entry M z K a b j‖)≤cost e*K*((M:ℝ)^(1+e)/z)*rowProduct M a b := by
  obtain ⟨summ,old⟩ := full_progression hM hz hK a b
  refine ⟨summ,old.trans ?_⟩
  have m1 : 1≤(M:ℝ) := by exact_mod_cast hM
  have mp := zero_lt_one.trans_le m1
  have zp : 0<(z:ℝ) := by exact_mod_cast hz
  have kp : 0<K := by linarith only [hK]
  have base0 := mul_nonneg (div_nonneg mp.le zp.le) (row_product_nonnegative M a b)
  have w := mul_le_mul_of_nonneg_right (log_cost m1 he)
    (mul_nonneg (mul_nonneg (mul_nonneg short_nonnegative kp.le) (exp_pos (4*π)).le) base0)
  have l := mul_le_mul (show (1:ℝ)≤K by linarith only [hK]) (one_le_rpow m1 he.le)
    zero_le_one kp.le
  have v := mul_le_mul_of_nonneg_right l
    (mul_nonneg (mul_nonneg (show (0:ℝ)≤4 by norm_num) long_nonnegative) base0)
  dsimp only [cost,price]
  rw [rpow_add mp,rpow_one]
  simp only [div_eq_mul_inv] at w v ⊢
  nlinarith only [w,v]

end ImbalancedChen.Part3.OriginalRegularGaussianOffDiagonal20261113
end

