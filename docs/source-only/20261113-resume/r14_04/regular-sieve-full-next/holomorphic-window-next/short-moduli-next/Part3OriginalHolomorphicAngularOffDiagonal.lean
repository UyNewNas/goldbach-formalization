import ImbalancedChen.Part3OriginalHolomorphicShortProgression
import ImbalancedChen.Part3OriginalHolomorphicLongProgression

/-! The complete geometric progression of the corrected angular window,
with an epsilon-dependent constant preceding the level, indices and rows. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicAngularOffDiagonal20261113
open Real Finset
open OriginalHolomorphicOddWindow20261113 (amplitudeConstant)
open OriginalHolomorphicPhysicalCosine20261113 (form argument)
open OriginalHolomorphicLongModulus20261113 (rawWindow longConstant)
open OriginalHolomorphicLongProgression20261113 (longTerm long_progression_bound)
open OriginalHolomorphicShortOscillation20261113 (rowProduct row_product_nonnegative)
open OriginalHolomorphicShortProgression20261113 (shortTerm shortBill balancedConstant short_progression_bound)

def angularTerm (M z : ℕ) (t : ℝ) (a b : ℕ → ℂ) (j : ℕ) : ℂ :=
  let c := z*(j+1)
  form M c a b (fun m n => (rawWindow t (argument c m n):ℂ))/(c:ℂ)

private theorem log_cost {m e : ℝ} (hm : 1≤m) (he : 0<e) :
    sqrt (244*(1+log m))*(1+log m) ≤ 16*(1+2/e)^2*m^e := by
  have mp := zero_lt_one.trans_le hm
  have l0 := log_nonneg hm
  have t1 := one_le_rpow hm (show 0≤e/2 by positivity)
  have tp := rpow_pos_of_pos mp (e/2)
  have g := log_le_sub_one_of_pos tp
  rw [log_rpow mp] at g
  have ell : log m≤(2/e)*m^(e/2) := by
    have h : log m≤(2*m^(e/2))/e := (le_div_iff₀ he).mpr (by nlinarith only [g])
    convert h using 1 <;> ring
  have l1 : 1+log m≤(1+2/e)*m^(e/2) := by nlinarith only [ell,t1]
  have sq := pow_le_pow_left₀ (by linarith only [l0] : 0≤1+log m) l1 2
  have re : (m^(e/2))^2 = m^e := by
    calc
      _ = (m^(e/2))^((2:ℕ):ℝ) := (rpow_natCast _ 2).symm
      _ = m^((e/2)*2) := (rpow_mul mp.le (e/2) 2).symm
      _ = _ := by rw [show e/2*2=e by ring]
  rw [mul_pow,re] at sq
  have r : sqrt (244*(1+log m))≤16*(1+log m) := sqrt_le_iff.mpr
    ⟨by linarith only [l0],by nlinarith only [l0,sq_nonneg (log m)]⟩
  have u := mul_le_mul_of_nonneg_right r (by linarith only [l0] : 0≤1+log m)
  have v := mul_le_mul_of_nonneg_left sq (by norm_num : (0:ℝ)≤16)
  nlinarith only [u,v]

private theorem positive_shift (M : ℕ) (f : ℕ → ℝ) :
    (∑ j∈range M, f (j+1)) = ∑ d∈Icc 1 M, f d := by
  have eq : Icc 1 M=Ico 1 (M+1) := by ext k; simp only [mem_Icc,mem_Ico]; omega
  rw [eq,sum_Ico_eq_sum_range,show M+1-1=M by omega]
  exact sum_congr rfl (fun j _ => congrArg f (by omega))

private theorem full_log_bound {M z : ℕ} (hM : 0<M) (hz : 0<z)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    Summable (fun j => ‖angularTerm M z t a b j‖) ∧
    (∑' j, ‖angularTerm M z t a b j‖) ≤
      shortBill M a b/z*(1+log M)+4*longConstant*((M:ℝ)/z)*rowProduct M a b := by
  let U := fun j => ‖shortTerm M z t a b (j+1)‖
  let V := fun j => ‖longTerm M z t a b j‖
  have split (j : ℕ) : ‖angularTerm M z t a b j‖=U j+V j := by
    by_cases h : z*(j+1)<M
    · simp only [angularTerm,U,V,shortTerm,longTerm,if_pos h,if_neg (not_le.mpr h),norm_zero,add_zero]
    · simp only [angularTerm,U,V,shortTerm,longTerm,if_neg h,if_pos (le_of_not_gt h),norm_zero,zero_add]
  have tail (j : ℕ) (hj : j∉range M) : U j=0 := by
    have jM : M≤j := by simpa only [mem_range,not_lt] using hj
    have z1 : 1≤z := hz
    have low : j+1≤z*(j+1) := by simpa only [one_mul] using Nat.mul_le_mul_right (j+1) z1
    dsimp only [U,shortTerm]
    rw [if_neg (by omega),norm_zero]
  have hu : Summable U := summable_of_ne_finset_zero tail
  have s := short_progression_bound hM hz ht ht1 a b
  have sh : (∑' j,U j)≤shortBill M a b/z*(1+log M) := by
    rw [tsum_eq_sum tail]
    exact (positive_shift M (fun d => ‖shortTerm M z t a b d‖)).le.trans s
  obtain ⟨hv,lv⟩ := long_progression_bound hM hz ht ht1 a b
  have hV : Summable V := hv
  have sv : (∑' j,V j)≤4*longConstant*((M:ℝ)/z)*rowProduct M a b := by
    convert lv using 1 <;> dsimp only [V,rowProduct] <;> ring
  simp only [split]
  exact ⟨hu.add hV,(hu.tsum_add hV).le.trans (add_le_add sh sv)⟩

def cost (e : ℝ) : ℝ :=
  balancedConstant*amplitudeConstant*exp (4*π)*(16*(1+2/e)^2)+4*longConstant

/-- Arbitrary independent complex rows and every original level and length.
The raw angular test has absolute multiplier 2/π in the Petersson trace. -/
theorem angular_off_diagonal {e : ℝ} (he : 0<e) (M z : ℕ) (hM : 0<M) (hz : 0<z)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    Summable (fun j => ‖angularTerm M z t a b j‖) ∧
    (∑' j, ‖angularTerm M z t a b j‖) ≤
      cost e*((M:ℝ)^(1+e)/z)*rowProduct M a b := by
  obtain ⟨summ,old⟩ := full_log_bound hM hz ht ht1 a b
  refine ⟨summ,old.trans ?_⟩
  have m1 : 1≤(M:ℝ) := by exact_mod_cast hM
  have mp := zero_lt_one.trans_le m1
  have zp : 0<(z:ℝ) := by exact_mod_cast hz
  have p0 := row_product_nonnegative M a b
  have C0 : 0≤balancedConstant*amplitudeConstant*exp (4*π) := by
    dsimp only [balancedConstant,amplitudeConstant]; positivity
  have L0 : 0≤4*longConstant := by dsimp only [longConstant,amplitudeConstant]; positivity
  let base := (M:ℝ)/z*rowProduct M a b
  have B0 : 0≤base := mul_nonneg (div_nonneg mp.le zp.le) p0
  have X := mul_le_mul_of_nonneg_right (log_cost m1 he) (mul_nonneg C0 B0)
  have Y := mul_le_mul_of_nonneg_right (one_le_rpow m1 he.le) (mul_nonneg L0 B0)
  dsimp only [base] at X Y
  dsimp only [shortBill,cost]
  rw [rpow_add mp,rpow_one]
  nlinarith only [X,Y]

end ImbalancedChen.Part3.OriginalHolomorphicAngularOffDiagonal20261113
end
