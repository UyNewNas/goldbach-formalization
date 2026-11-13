import ImbalancedChen.Part3OriginalHolomorphicPhysicalCosine
import ImbalancedChen.Part3OriginalHolomorphicWindowMoment

/-! The cubic remainder of the corrected odd window, applied to both
arbitrary coefficient vectors and the complete Kloosterman operator. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicLongModulus20261113

open Finset Real Set MeasureTheory
open OriginalSmoothPoissonTail (kloosterman)
open OriginalAllParameterKloosterman20261113 (dyadEnergy)
open OriginalHolomorphicOddWindow20261113
open OriginalHolomorphicPhysicalCosine20261113
open OriginalHolomorphicWindowMoment20261113

private theorem cosine_second_remainder (u : ℝ) :
    cos u-1 = -(u^2)*(∫ s in (0:ℝ)..1, (1-s)*cos (s*u)) := by
  let F : ℝ → ℝ := fun s => cos (s*u)-(1-s)*u*sin (s*u)
  have deriv (s : ℝ) : HasDerivAt F (-(u^2)*((1-s)*cos (s*u))) s := by
    have p := (hasDerivAt_id s).mul_const u
    have k := ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).mul_const u
    apply (p.cos.sub (k.mul p.sin)).congr_deriv
    dsimp <;> ring
  have cont : Continuous (fun s : ℝ => -(u^2)*((1-s)*cos (s*u))) :=
    continuous_const.mul ((continuous_const.sub continuous_id).mul
      (continuous_cos.comp (continuous_id.mul continuous_const)))
  rw [←intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => deriv s) (cont.intervalIntegrable 0 1)]
  simp [F]

private theorem form_integral (M c : ℕ) (a b : ℕ → ℂ) {l r : ℝ}
    (f : ℕ → ℕ → ℝ → ℂ) (hf : ∀ m n, Continuous (f m n)) :
    form M c a b (fun m n => ∫ t in l..r, f m n t) =
      ∫ t in l..r, form M c a b (fun m n => f m n t) := by
  dsimp only [form]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · exact sum_congr rfl (fun j _ => (intervalIntegral.integral_const_mul _ _).symm)
    · exact fun j _ => (continuous_const.mul (hf (M+i) (M+j))).intervalIntegrable l r
  · intro i _
    exact (continuous_finsetSum _ fun j _ => continuous_const.mul
      (hf (M+i) (M+j))).intervalIntegrable l r

def angularIntegrand (t x y : ℝ) : ℝ :=
  x*(correctedAmplitude t y*(cos (x*cos y)-1))

def rawWindow (t x : ℝ) : ℝ := x*(∫ y in (0:ℝ)..π/2, correctedAmplitude t y*cos (x*cos y))

theorem raw_window_integral {t : ℝ} (ht : 0<t) (x : ℝ) :
    rawWindow t x=∫ y in (0:ℝ)..π/2, angularIntegrand t x y := by
  rw [rawWindow,corrected_window_remove_constant ht,angularIntegrand,intervalIntegral.integral_const_mul]

private def angularScalar (t y : ℝ) : ℝ := -(correctedAmplitude t y)*(cos y)^2

private theorem row_integral_coefficient (t y : ℝ) (c m n : ℕ) :
    (angularIntegrand t (argument c m n) y:ℂ) =
      ∫ s in (0:ℝ)..1, (((scale c)^3*angularScalar t y*(1-s):ℝ):ℂ) *
        (((sqrt m)^3:ℝ):ℂ) * (((sqrt n)^3:ℝ):ℂ) *
        (cos ((s*cos y)*argument c m n):ℂ) := by
  let x := argument c m n
  have h := cosine_second_remainder (x*cos y)
  have realId : angularIntegrand t x y =
      ∫ s in (0:ℝ)..1,
        (scale c)^3*angularScalar t y*(1-s)*(sqrt m)^3*(sqrt n)^3*
          cos ((s*cos y)*x) := by
    calc
      _ = (x*correctedAmplitude t y*(-((x*cos y)^2)))*
          (∫ s in (0:ℝ)..1,(1-s)*cos (s*(x*cos y))) := by rw [angularIntegrand,h]; ring
      _ = _ := by
        rw [←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro s hs
        rw [show s*(x*cos y)=(s*cos y)*x by ring]
        dsimp only [angularScalar,x,argument]
        ring
  rw [show angularIntegrand t (argument c m n) y=angularIntegrand t x y by rfl,realId,
    ←intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [Complex.ofReal_mul,x]

private theorem fixed_angle_identity (M c : ℕ) (t y : ℝ) (a b : ℕ → ℂ) :
    form M c a b (fun m n => (angularIntegrand t (argument c m n) y:ℂ)) =
      ∫ s in (0:ℝ)..1, (((scale c)^3*angularScalar t y*(1-s):ℝ):ℂ)*
        cosineForm M c (s*cos y) (cubicRow a) (cubicRow b) := by
  simp_rw [row_integral_coefficient]
  rw [form_integral]
  · apply intervalIntegral.integral_congr
    intro s hs
    dsimp only [cosineForm,form,cubicRow]
    simp only [mul_sum]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))
  · intro m n
    fun_prop

private theorem angle_scalar_bound {t : ℝ} (ht : t∈Icc 0 1) (y : ℝ) :
    |angularScalar t y| ≤ amplitudeConstant := by
  rw [angularScalar,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg _)]
  have p : (cos y)^2≤1 := by
    simpa only [sq_abs,one_pow] using
      pow_le_pow_left₀ (abs_nonneg (cos y)) (abs_cos_le_one y) 2
  exact (mul_le_of_le_one_right (abs_nonneg _) p).trans (corrected_amplitude_bound ht y)

def longConstant : ℝ := π/2*(4*π)^3*amplitudeConstant*(12*exp (4*π))*8

private def integrandBill (M c : ℕ) (a b : ℕ → ℂ) : ℝ :=
  ((scale c)^3*amplitudeConstant)*(12*exp (4*π)*c)*
    (rowCost M*sqrt (dyadEnergy M a))*(rowCost M*sqrt (dyadEnergy M b))

private theorem fixed_angle_bound {M c : ℕ} [NeZero c] (hM : 0<M) (hc : M≤c)
    {t y : ℝ} (ht : t∈Icc 0 1) (hy : y∈Icc 0 (π/2)) (a b : ℕ → ℂ) :
    ‖form M c a b (fun m n => (angularIntegrand t (argument c m n) y:ℂ))‖ ≤
      integrandBill M c a b := by
  have scale0 : 0≤scale c := by dsimp [scale]; positivity
  have c0 : 0≤cos y := cos_nonneg_of_mem_Icc ⟨by linarith only [pi_pos,hy.1],hy.2⟩
  have hA : 0≤amplitudeConstant := by unfold amplitudeConstant; positivity
  have hRow : 0≤rowCost M := pow_nonneg (sqrt_nonneg _) _
  rw [fixed_angle_identity]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=integrandBill M c a b)
    (f:=fun s : ℝ => (((scale c)^3*angularScalar t y*(1-s):ℝ):ℂ)*
      cosineForm M c (s*cos y) (cubicRow a) (cubicRow b)) (fun s hs => by
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hs
      have hq := mul_nonneg hs.1.le c0
      have q1 := mul_le_one₀ hs.2 c0 (cos_le_one y)
      have sr := sub_nonneg.mpr hs.2
      have budget : |(scale c)^3*angularScalar t y*(1-s)|≤(scale c)^3*amplitudeConstant := by
        rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg scale0 _),abs_of_nonneg sr]
        apply (mul_le_of_le_one_right (mul_nonneg (pow_nonneg scale0 _) (abs_nonneg _))
          (by linarith only [hs.1])).trans
        exact mul_le_mul_of_nonneg_left (angle_scalar_bound ht y) (pow_nonneg scale0 _)
      have w := cosine_long_bound hM hc hq q1 (cubicRow a) (cubicRow b)
      have U := mul_le_mul_of_nonneg_left (cubic_row_energy M a)
        (show 0≤12*exp (4*π)*c by positivity)
      have V := mul_le_mul U (cubic_row_energy M b) (sqrt_nonneg _) (by positivity)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      have z := mul_le_mul budget (w.trans V) (norm_nonneg _) (mul_nonneg (pow_nonneg scale0 _) hA)
      convert z using 1 <;> dsimp only [integrandBill] <;> ring)
  simpa only [sub_zero,abs_one,mul_one] using h

/-- Unscaled same-cusp geometric numerator. Multiplying rawWindow by
−2/π gives the odd Laplace window in the Petersson formula. -/
theorem long_modulus_bound {M c : ℕ} [NeZero c] (hM : 0<M) (hc : M≤c)
    {t : ℝ} (ht : 0<t) (ht1 : t≤1) (a b : ℕ → ℂ) :
    ‖form M c a b (fun m n => (rawWindow t (argument c m n):ℂ))‖ ≤
      longConstant*((M:ℝ)^3/(c:ℝ)^2)*sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b) := by
  have cv : Continuous (correctedAmplitude t) := (amplitude_continuous ht).sub
    (continuous_const.mul (amplitude_continuous (by norm_num : (0:ℝ)<2)))
  have reg (x : ℝ) : Continuous (angularIntegrand t x) :=
    continuous_const.mul (cv.mul ((continuous_cos.comp
      (continuous_const.mul continuous_cos)).sub continuous_const))
  simp_rw [raw_window_integral ht,←intervalIntegral.integral_ofReal]
  rw [form_integral M c a b _ (fun m n => Complex.continuous_ofReal.comp (reg _))]
  have p0 : 0≤π/2 := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=π/2) (C:=integrandBill M c a b)
    (f:=fun y => form M c a b (fun m n => (angularIntegrand t (argument c m n) y:ℂ)))
    (fun y hy => by
      rw [uIoc_of_le p0] at hy
      exact fixed_angle_bound hM hc ⟨ht.le,ht1⟩ ⟨hy.1.le,hy.2⟩ a b)
  rw [sub_zero,abs_of_nonneg p0] at h
  apply h.trans_eq
  have cp : (c:ℝ)≠0 := by exact_mod_cast (NeZero.ne c)
  calc
    integrandBill M c a b*(π/2) =
      π/2*(scale c)^3*amplitudeConstant*(12*exp (4*π))*c*(rowCost M)^2*
        sqrt (dyadEnergy M a)*sqrt (dyadEnergy M b) := by dsimp only [integrandBill]; ring
    _ = _ := by rw [row_cost_square]; dsimp only [longConstant,scale]; field_simp [cp] <;> ring

end ImbalancedChen.Part3.OriginalHolomorphicLongModulus20261113
end
