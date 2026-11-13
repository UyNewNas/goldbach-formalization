import ImbalancedChen.Part3OriginalHolomorphicShortOscillation
import ImbalancedChen.Part3OriginalHolomorphicLongModulus

/-! An exact physical angular split. The scalar integration by parts is
performed before applying the finite complex Kloosterman form. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicAngularSplit20261113

open Real Finset Set MeasureTheory
open OriginalHolomorphicOddWindow20261113
open OriginalHolomorphicWindowMoment20261113 (amplitude_continuous)
open OriginalHolomorphicPhysicalCosine20261113 (argument scale form cosineForm)
open OriginalHolomorphicLongModulus20261113 (rawWindow)
open OriginalHolomorphicShortOscillation20261113 (rootRow sineForm)

def quotient (t y : ℝ) : ℝ := angleQuotient t y-exp (2-t)*angleQuotient 2 y

theorem quotient_eq_div {t y : ℝ} (hy : sin y≠0) :
    quotient t y=correctedAmplitude t y/sin y := by
  simp only [quotient,←quotient_eq hy,correctedAmplitude]
  ring

theorem derivative_continuous {t : ℝ} (ht : 0<t) : Continuous (correctedDerivative t) := by
  have h {u : ℝ} (hu : 0<u) : Continuous (derivativeValue u) := by
    have b : 0<sinh u := sinh_pos_iff.mpr hu
    apply Continuous.div _ _ (fun y => (sq_pos_of_pos
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos b) (sq_nonneg (sin y)))).ne')
    · exact (continuous_const.mul continuous_cos).mul (continuous_const.sub (continuous_sin.pow 2))
    · exact (continuous_const.add (continuous_sin.pow 2)).pow 2
  exact (h ht).sub (continuous_const.mul (h (by norm_num : (0:ℝ)<2)))

private theorem quotient_deriv {t y : ℝ} (hy : sin y≠0) :
    HasDerivAt (quotient t) (correctedDerivative t y) y :=
  (quotient_derivative t y hy).sub ((quotient_derivative 2 y hy).const_mul (exp (2-t)))

def nearPart (t x Δ : ℝ) := ∫ y in (0:ℝ)..Δ, x*correctedAmplitude t y*cos (x*cos y)
def remainderPart (t x Δ : ℝ) :=
  ∫ y in Δ..π/2, correctedDerivative t y*sin (x*cos y)

private theorem scalar_split {t Δ : ℝ} (ht : 0<t) (hd : 0<Δ) (hd' : Δ≤π/2) (x : ℝ) :
    rawWindow t x = nearPart t x Δ+
      quotient t Δ*sin (x*cos Δ)+remainderPart t x Δ := by
  let G := fun y : ℝ => sin (x*cos y)
  let G' := fun y : ℝ => -(x*sin y)*cos (x*cos y)
  have dG (y : ℝ) : HasDerivAt G (G' y) y := by
    apply (((hasDerivAt_cos y).const_mul x).sin).congr_deriv
    dsimp only [G']
    ring
  have s0 (y : ℝ) (hy : y∈uIcc Δ (π/2)) : 0<sin y := by
    rw [uIcc_of_le hd'] at hy
    exact sin_pos_of_pos_of_lt_pi (hd.trans_le hy.1) (by linarith only [hy.2,pi_pos])
  have vp : Continuous (correctedAmplitude t) := (amplitude_continuous ht).sub
    (continuous_const.mul (amplitude_continuous (by norm_num : (0:ℝ)<2)))
  have fc : Continuous (fun y => x*correctedAmplitude t y*cos (x*cos y)) :=
    (continuous_const.mul vp).mul (continuous_cos.comp (continuous_const.mul continuous_cos))
  have gc : Continuous G' := (continuous_const.mul continuous_sin).neg.mul
    (continuous_cos.comp (continuous_const.mul continuous_cos))
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u:=quotient t) (u':=correctedDerivative t) (v:=G) (v':=G')
    (fun y hy => quotient_deriv (s0 y hy).ne') (fun y _ => dG y)
    ((derivative_continuous ht).intervalIntegrable Δ (π/2)) (gc.intervalIntegrable Δ (π/2))
  have H : (∫ y in Δ..π/2, quotient t y*G' y) =
      -(∫ y in Δ..π/2, x*correctedAmplitude t y*cos (x*cos y)) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [quotient_eq_div (s0 y hy).ne']
    dsimp only [G']
    field_simp [(s0 y hy).ne'] <;> ring
  rw [H] at ibp
  have e : G (π/2)=0 := by simp [G]
  rw [e,mul_zero,zero_sub] at ibp
  have old := intervalIntegral.integral_add_adjacent_intervals
    (fc.intervalIntegrable 0 Δ) (fc.intervalIntegrable Δ (π/2))
  have em : rawWindow t x=∫ y in (0:ℝ)..π/2,x*correctedAmplitude t y*cos (x*cos y) := by
    rw [rawWindow,←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun _ _ => by ring)
  dsimp only [G] at ibp
  unfold nearPart remainderPart
  rw [em]
  linarith only [old,ibp]

private theorem angular_sum_integral (M c : ℕ) (a b : ℕ → ℂ) {l r : ℝ}
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

def nearPhysical (M c : ℕ) (t Δ : ℝ) (a b : ℕ → ℂ) :=
  ∫ y in (0:ℝ)..Δ, ((scale c*correctedAmplitude t y:ℝ):ℂ)*
    cosineForm M c (cos y) (rootRow a) (rootRow b)

def remainderPhysical (M c : ℕ) (t Δ : ℝ) (a b : ℕ → ℂ) :=
  ∫ y in Δ..π/2, (correctedDerivative t y:ℂ)*sineForm M c (cos y) a b

private theorem near_physical {t : ℝ} (ht : 0<t) (M c : ℕ) (Δ : ℝ) (a b : ℕ → ℂ) :
    form M c a b (fun m n => (nearPart t (argument c m n) Δ:ℂ))=nearPhysical M c t Δ a b := by
  have cv : Continuous (correctedAmplitude t) := (amplitude_continuous ht).sub
    (continuous_const.mul (amplitude_continuous (by norm_num : (0:ℝ)<2)))
  simp only [nearPart,←intervalIntegral.integral_ofReal]
  rw [angular_sum_integral]
  · apply intervalIntegral.integral_congr
    intro y hy
    dsimp only [form,cosineForm,rootRow]
    simp only [mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
      rw [mul_comm (argument c (M+i) (M+j)) (cos y)]
      simp only [argument,Complex.ofReal_mul]
      ring
  · intro m n
    exact Complex.continuous_ofReal.comp ((continuous_const.mul cv).mul
      (continuous_cos.comp (continuous_const.mul continuous_cos)))

private theorem remainder_physical {t : ℝ} (ht : 0<t) (M c : ℕ) (Δ : ℝ) (a b : ℕ → ℂ) :
    form M c a b (fun m n => (remainderPart t (argument c m n) Δ:ℂ)) =
      remainderPhysical M c t Δ a b := by
  simp only [remainderPart,←intervalIntegral.integral_ofReal]
  rw [angular_sum_integral]
  · apply intervalIntegral.integral_congr
    intro y _
    dsimp only [form,sineForm]
    simp only [mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
      rw [mul_comm (argument c (M+i) (M+j)) (cos y)]
      push_cast <;> ring
  · intro m n
    exact Complex.continuous_ofReal.comp ((derivative_continuous ht).mul
      (continuous_sin.comp (continuous_const.mul continuous_cos)))

theorem physical_angular_split {t Δ : ℝ} (ht : 0<t) (hd : 0<Δ) (hd' : Δ≤π/2)
    (M c : ℕ) (a b : ℕ → ℂ) :
    form M c a b (fun m n => (rawWindow t (argument c m n):ℂ)) =
      nearPhysical M c t Δ a b+(quotient t Δ:ℂ)*sineForm M c (cos Δ) a b+
        remainderPhysical M c t Δ a b := by
  rw [←near_physical ht,←remainder_physical ht]
  simp only [sineForm,form,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [scalar_split ht hd hd',mul_comm (argument c (M+i) (M+j)) (cos Δ)]
  push_cast <;> ring

end ImbalancedChen.Part3.OriginalHolomorphicAngularSplit20261113
end
