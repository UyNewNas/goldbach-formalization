import ImbalancedChen.Part3OriginalPositiveStripMoments
import ImbalancedChen.Part3OriginalPositiveStripContour

/-! The two entire expressions for B have the same complex test on both sides. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveStripBoundary20261112

open Complex MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualPositiveCosineProfile20261112 (profile profile_apply cosineTest_apply testDiv)
open OriginalPositiveJacobiAnger20261112 (oddOrder sin_cosh)
open ActualPositiveHolomorphicWeights20261112 (intJ)
open OriginalPositiveStripData20261112
open OriginalPositiveStripMoments20261112

def B (ell : D4→ℤ) (Y : ℝ) (z : ℂ) := laplace (testDiv ell Y) (Complex.cosh z)-2*I*series ell Y z
def Q (ell : D4→ℤ) (Y w : ℝ) := (B ell Y w-B ell Y (-(w:ℂ)))/(2*I)
def h (ell : D4→ℤ) (Y w : ℝ) := deriv (Q ell Y) w/(Real.pi:ℂ)

theorem B_entire (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) : Differentiable ℂ (B ell Y) :=
  ((div_laplace_diff ell hY).comp Complex.differentiable_cosh).sub
    ((fun z => (series_deriv ell hY z).differentiableAt).const_mul (2*I))

private theorem norm_cosh_bound (z : ℂ) : ‖Complex.cosh z‖≤Real.exp ‖z‖ := by
  rw [Complex.cosh,norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  have p := Complex.norm_exp_le_exp_norm z
  have n := Complex.norm_exp_le_exp_norm (-z)
  rw [norm_neg] at n
  linarith only [norm_add_le (Complex.exp z) (Complex.exp (-z)),p,n]

theorem B_alternate (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (z : ℂ) :
    B ell Y z=laplace (testDiv ell Y) (-Complex.cosh z)+2*I*series ell Y (-z) := by
  let b := fun j : ℕ => 2*sign j*Complex.cosh ((oddOrder j:ℂ)*z)
  have hb (j : ℕ) : ‖b j‖≤2*(Real.exp ‖z‖)^(oddOrder j) := by
    simp only [b,sign,norm_mul,norm_pow,norm_neg,norm_one,one_pow,Complex.norm_ofNat,mul_one]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hz := norm_cosh_bound ((oddOrder j:ℂ)*z)
    simpa [norm_mul,Real.exp_nat_mul] using hz
  have S := integrate_odd ell hY b (fun q => Complex.sin ((q:ℂ)*Complex.cosh z))
    (by norm_num : (0:ℝ)≤2) (Real.exp_pos _).le hb (fun q _ =>
      (sin_cosh q z).congr_fun (fun j => by dsimp [b,sign]; ring))
  have sums : (∫ q in Ioi (0:ℝ),Complex.sin ((q:ℂ)*Complex.cosh z)*testDiv ell Y q)=
      series ell Y z+series ell Y (-z) := by
    apply S.unique
    apply ((series_sum ell hY z).hasSum.add (series_sum ell hY (-z)).hasSum).congr_fun
    intro j
    dsimp [b,coeff,Complex.cosh]
    rw [neg_mul,neg_mul_neg]
    ring
  have D : laplace (testDiv ell Y) (Complex.cosh z)-laplace (testDiv ell Y) (-Complex.cosh z)=
      2*I*(∫ q in Ioi (0:ℝ),Complex.sin ((q:ℂ)*Complex.cosh z)*testDiv ell Y q) := by
    rw [div_wave_Ioi ell hY,div_wave_Ioi ell hY,←integral_sub (div_wave_integrable ell hY _)
      (div_wave_integrable ell hY _),←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun q => by
      rw [Complex.sin]
      have a : I*(q:ℂ)*Complex.cosh z=((q:ℂ)*Complex.cosh z)*I := by ring
      have b : I*(q:ℂ)*(-Complex.cosh z)=(-((q:ℂ)*Complex.cosh z))*I := by ring
      rw [a,b]
      ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [sums] at D
  unfold B
  linear_combination D

private theorem odd_phase (j : ℕ) : Complex.exp (-(oddOrder j:ℂ)*((Real.pi:ℂ)*I)) = -1 := by
  rw [neg_mul,←mul_neg,Complex.exp_nat_mul,Complex.exp_neg,Complex.exp_pi_mul_I]
  simp [oddOrder,pow_succ,pow_mul]

theorem series_add_pi (ell : D4→ℤ) (Y : ℝ) (z : ℂ) :
    series ell Y (z+Real.pi*I)= -series ell Y z := by
  unfold series
  rw [←tsum_neg]
  apply tsum_congr
  intro j
  rw [mul_add,Complex.exp_add,odd_phase]
  ring

theorem B_reflect (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (z : ℂ) :
    B ell Y (z+Real.pi*I)=B ell Y (-z) := by
  rw [B_alternate ell hY (-z),neg_neg]
  unfold B
  rw [series_add_pi,Complex.cosh_add,Complex.cosh_mul_I,Complex.sinh_mul_I,← Complex.ofReal_cos,
    ← Complex.ofReal_sin,Real.cos_pi,Real.sin_pi,Complex.cosh_neg]
  simp

theorem boundary_sum (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) :
    B ell Y w+B ell Y (-(w:ℂ))=2*profile ell hY w := by
  rw [B_alternate ell hY (-(w:ℂ)),neg_neg,Complex.cosh_neg]
  unfold B
  rw [show ∀ a b c : ℂ,a-b+(c+b)=a+c from fun _ _ _ => by ring,div_wave_Ioi ell hY,div_wave_Ioi ell hY,
    ←integral_add (div_wave_integrable ell hY _) (div_wave_integrable ell hY _),
    profile_apply,cosineTest_apply,←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun q => by
    rw [Complex.ofReal_cos,Complex.ofReal_mul,←Complex.ofReal_cosh,Complex.cos]
    have e : I*(q:ℂ)*(Real.cosh w:ℂ)=((q:ℂ)*(Real.cosh w:ℂ))*I := by ring
    have n : I*(q:ℂ)*(-((Real.cosh w:ℂ)))=(-((q:ℂ)*(Real.cosh w:ℂ)))*I := by ring
    rw [e,n]
    ring

theorem bottom (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) :
    B ell Y w=profile ell hY w+I*Q ell Y w := by
  have S := boundary_sum ell hY w
  unfold Q
  field_simp [I_ne_zero]
  linear_combination I*S

theorem top (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (w : ℝ) :
    B ell Y ((w:ℂ)+Real.pi*I)=profile ell hY w-I*Q ell Y w := by
  rw [B_reflect ell hY]
  linear_combination boundary_sum ell hY w-(bottom ell hY w)

theorem Q_odd (ell : D4→ℤ) (Y w : ℝ) : Q ell Y (-w)= -Q ell Y w := by
  unfold Q; rw [Complex.ofReal_neg,neg_neg]; ring

private theorem exp_le_cosh (z : ℂ) (hr : 0≤z.re) : Real.exp z.re ≤ 2*‖Complex.cosh z‖+1 := by
  have a := norm_sub_le (2*Complex.cosh z) (Complex.exp (-z))
  have e : 2*Complex.cosh z-Complex.exp (-z)=Complex.exp z := by rw [Complex.cosh]; ring
  rw [e,norm_mul,Complex.norm_ofNat,Complex.norm_exp,Complex.norm_exp,Complex.neg_re] at a
  linarith only [a,Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)]

theorem strip_bound (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ C : ℝ,0≤C ∧ ∀ x y : ℝ,0≤y → y≤Real.pi →
      ‖B ell Y ((x:ℂ)+y*I)‖ ≤ C*Real.exp (-|x|) := by
  obtain ⟨L,hL,HL⟩ := div_laplace_bounds ell hY
  let S := ∑' j,‖coeff ell Y j‖
  have hS : 0≤S := tsum_nonneg fun _ => norm_nonneg _
  let C := 3*L+2*S
  have right (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (hp : y≤Real.pi) :
      ‖B ell Y ((x:ℂ)+y*I)‖≤C*Real.exp (-x) := by
    let z : ℂ := x+y*I
    have zr : z.re=x := by simp [z]
    have hr : 0≤z.re := by simpa only [zr] using hx
    have zi : 0≤(Complex.cosh z).im := by
      simpa [z,Complex.cosh_add,Complex.cosh_mul_I,Complex.sinh_mul_I,←Complex.ofReal_sinh,
        ←Complex.ofReal_cosh,←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.mul_im,Complex.mul_re] using
        mul_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.sin_nonneg_of_nonneg_of_le_pi hy hp)
    obtain ⟨hu,hv⟩ := HL _ zi
    have c := exp_le_cosh z hr
    rw [zr] at c
    let A := laplace (testDiv ell Y) (Complex.cosh z)
    have b : ‖A‖≤(3*L)*Real.exp (-x) := by
      rw [Real.exp_neg,←div_eq_mul_inv,le_div_iff₀ (Real.exp_pos _)]
      nlinarith only [mul_le_mul_of_nonneg_right c (norm_nonneg A),hu,hv]
    have s := series_norm ell hY z hr
    rw [zr] at s
    have bound := norm_sub_le A (2*I*series ell Y z)
    rw [norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one] at bound
    change ‖A-2*I*series ell Y z‖≤_
    dsimp only [C,S] at *
    linarith only [bound,b,s]
  refine ⟨C,by dsimp [C]; positivity,fun x y hy hp => ?_⟩
  by_cases hx : 0≤x
  · simpa [abs_of_nonneg hx] using right x y hx hy hp
  · have he := B_reflect ell hY (-((x:ℂ)+y*I))
    rw [neg_neg,show -((x:ℂ)+(y:ℂ)*I)+Real.pi*I=((-x:ℝ):ℂ)+((Real.pi-y:ℝ):ℂ)*I by push_cast; ring] at he
    rw [←he,abs_of_neg (lt_of_not_ge hx)]
    exact right (-x) (Real.pi-y) (by linarith) (by linarith) (by linarith)

end ImbalancedChen.Part3.OriginalPositiveStripBoundary20261112
end
