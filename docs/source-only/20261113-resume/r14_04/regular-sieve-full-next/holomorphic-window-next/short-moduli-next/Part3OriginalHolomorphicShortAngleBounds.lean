import ImbalancedChen.Part3OriginalHolomorphicAngularSplit

/-! Cost of the two true angular integrals and their boundary, with the
cut left free for the original square-root choice. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicShortAngleBounds20261113
open Real Set MeasureTheory
open OriginalHolomorphicOddWindow20261113
open OriginalHolomorphicPhysicalCosine20261113 (form argument scale cosineForm)
open OriginalHolomorphicLongModulus20261113 (rawWindow)
open OriginalHolomorphicShortOscillation20261113
open OriginalHolomorphicAngularSplit20261113

private theorem amplitude_nonneg : 0≤amplitudeConstant := by dsimp [amplitudeConstant]; positivity

private theorem cos_one_positive : 0<cos (1:ℝ) :=
  cos_pos_of_mem_Ioo ⟨by linarith only [pi_pos],by linarith only [pi_gt_three]⟩

private theorem local_cos {y : ℝ} (h0 : 0≤y) (h1 : y≤1) : cos 1≤cos y :=
  cos_le_cos_of_nonneg_of_le_pi h0 (by linarith only [pi_gt_three]) h1

private theorem local_sin {y : ℝ} (hy : 0<y) (h1 : y≤π/2) : 0<sin y :=
  sin_pos_of_pos_of_lt_pi hy (by linarith only [h1,pi_pos])

def ampCost (M c : ℕ) (a b : ℕ → ℂ) : ℝ :=
  amplitudeConstant*(oscillationCost M c*rowProduct M a b)

private theorem near_bound {M c : ℕ} [NeZero c] (hc : c≤M) {t Δ : ℝ} (ht : t∈Icc 0 1)
    (hd : 0<Δ) (h1 : Δ≤1) (a b : ℕ → ℂ) :
    ‖nearPhysical M c t Δ a b‖ ≤
      (scale c*(2*(M:ℝ))*ampCost M c a b/sqrt (cos 1))*Δ := by
  have sc : 0≤scale c := by dsimp only [scale]; positivity
  have scos := sqrt_pos.mpr cos_one_positive
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=Δ) (C:=scale c*(2*(M:ℝ))*ampCost M c a b/sqrt (cos 1))
    (f:=fun y => ((scale c*correctedAmplitude t y:ℝ):ℂ)*
      cosineForm M c (cos y) (rootRow a) (rootRow b)) (fun y hy => by
      rw [uIoc_of_le hd.le] at hy
      have co := local_cos hy.1.le (hy.2.trans h1)
      have hq := cos_one_positive.trans_le co
      have bound := (short_oscillation hc hq (by linarith only [cos_le_one y])
        (rootRow a) (rootRow b)).1
      have rc := mul_le_mul_of_nonneg_left (root_row_product M a b) (oscillation_cost_nonnegative _ _)
      have den := div_le_div_of_nonneg_left
        (mul_nonneg (oscillation_cost_nonnegative _ _) (row_product_nonnegative _ _ _))
        scos (sqrt_le_sqrt co)
      have w := div_le_div_of_nonneg_right rc scos.le
      have V := mul_le_mul (mul_le_mul_of_nonneg_left (corrected_amplitude_bound ht y) sc)
        (bound.trans (den.trans w)) (norm_nonneg _) (mul_nonneg sc amplitude_nonneg)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg sc]
      convert V using 1 <;> dsimp only [ampCost] <;> ring)
  simpa only [nearPhysical,sub_zero,abs_of_pos hd] using h

private theorem boundary_bound {M c : ℕ} [NeZero c] (hc : c≤M) {t Δ : ℝ}
    (ht : t∈Icc 0 1) (hd : 0<Δ) (h1 : Δ≤1) (a b : ℕ → ℂ) :
    ‖(quotient t Δ:ℂ)*sineForm M c (cos Δ) a b‖ ≤
      ampCost M c a b/(sin Δ*sqrt (cos 1)) := by
  have sp := local_sin hd (by linarith only [h1,pi_gt_three])
  have q1 := local_cos hd.le h1
  have b := (short_oscillation hc (cos_one_positive.trans_le q1)
    (by linarith only [cos_le_one Δ]) a b).2
  have d := div_le_div_of_nonneg_left
    (mul_nonneg (oscillation_cost_nonnegative _ _) (row_product_nonnegative _ _ _))
    (sqrt_pos.mpr cos_one_positive) (sqrt_le_sqrt q1)
  have e := mul_le_mul (div_le_div_of_nonneg_right (corrected_amplitude_bound ht Δ) sp.le)
    (b.trans d) (norm_nonneg _) (div_nonneg amplitude_nonneg sp.le)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,quotient_eq_div sp.ne',abs_div,abs_of_pos sp]
  convert e using 1 <;> dsimp only [ampCost] <;> ring

private theorem csc_integral {Δ : ℝ} (hd : 0<Δ) (hp : Δ≤π/2) :
    (∫ y in Δ..π/2, 1/(sin y)^2) = cos Δ/sin Δ := by
  have sn (y : ℝ) (hy : y∈uIcc Δ (π/2)) : 0<sin y := by
    rw [uIcc_of_le hp] at hy
    exact local_sin (hd.trans_le hy.1) hy.2
  have D (y : ℝ) (hy : y∈uIcc Δ (π/2)) :
      HasDerivAt (fun v => -(cos v/sin v)) (1/(sin y)^2) y := by
    apply ((hasDerivAt_cos y).div (hasDerivAt_sin y) (sn y hy).ne').neg.congr_deriv
    field_simp [(sn y hy).ne'] <;> nlinarith only [sin_sq_add_cos_sq y]
  have cont : ContinuousOn (fun y : ℝ => 1/(sin y)^2) (uIcc Δ (π/2)) :=
    continuousOn_const.div (continuous_sin.pow 2).continuousOn (fun y hy => (sq_pos_of_pos (sn y hy)).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt D cont.intervalIntegrable]
  simp

private theorem remainder_bound {M c : ℕ} [NeZero c] (hc : c≤M) {t Δ : ℝ}
    (ht : t∈Icc 0 1) (hd : 0<Δ) (hp : Δ≤π/2) (a b : ℕ → ℂ) :
    ‖remainderPhysical M c t Δ a b‖≤ampCost M c a b/sin Δ := by
  have sn (y : ℝ) (hy : y∈uIcc Δ (π/2)) : 0<sin y := by
    rw [uIcc_of_le hp] at hy
    exact local_sin (hd.trans_le hy.1) hy.2
  have c0 : 0≤ampCost M c a b := mul_nonneg amplitude_nonneg
    (mul_nonneg (oscillation_cost_nonnegative _ _) (row_product_nonnegative _ _ _))
  have cont : ContinuousOn (fun y : ℝ => ampCost M c a b*(1/(sin y)^2)) (uIcc Δ (π/2)) :=
    continuousOn_const.mul (continuousOn_const.div (continuous_sin.pow 2).continuousOn
      (fun y hy => (sq_pos_of_pos (sn y hy)).ne'))
  have v := intervalIntegral.norm_integral_le_of_norm_le
    (a:=Δ) (b:=π/2) (f:=fun y => (correctedDerivative t y:ℂ)*sineForm M c (cos y) a b)
    (g:=fun y => ampCost M c a b*(1/(sin y)^2)) hp
    (ae_of_all _ fun y hy => by
      have sy := local_sin (hd.trans hy.1) hy.2
      have co := cos_nonneg_of_mem_Icc ⟨by linarith only [pi_pos,hd,hy.1],hy.2⟩
      have e := corrected_derivative_bound ht sy co
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      by_cases q : cos y=0
      · rw [q,zero_div,mul_zero] at e
        have h0 := le_antisymm e (abs_nonneg _)
        rw [h0,zero_mul]
        exact mul_nonneg c0 (div_nonneg zero_le_one (sq_nonneg _))
      · have cp := lt_of_le_of_ne co (Ne.symm q)
        have jp := sqrt_pos.mpr cp
        have bnd := (short_oscillation hc cp (by linarith only [cos_le_one y]) a b).2
        have z := mul_le_mul e bnd (norm_nonneg _)
          (mul_nonneg amplitude_nonneg (div_nonneg co (sq_nonneg _)))
        apply z.trans
        have cancel : cos y / sqrt (cos y)=sqrt (cos y) :=
          (div_eq_iff jp.ne').mpr (by nlinarith only [sq_sqrt co])
        have sq1 : sqrt (cos y)≤1 := by simpa only [sqrt_one] using sqrt_le_sqrt (cos_le_one y)
        calc
          _ = (ampCost M c a b*(1/(sin y)^2))*(cos y/sqrt (cos y)) := by
            dsimp only [ampCost]
            ring
          _ = (ampCost M c a b*(1/(sin y)^2))*sqrt (cos y) := by rw [cancel]
          _ ≤ _ := mul_le_of_le_one_right (mul_nonneg c0 (div_nonneg zero_le_one (sq_nonneg _))) sq1)
    cont.intervalIntegrable
  apply v.trans
  rw [intervalIntegral.integral_const_mul,csc_integral hd hp]
  have d := div_le_div_of_nonneg_right (cos_le_one Δ) (local_sin hd hp).le
  convert mul_le_mul_of_nonneg_left d c0 using 1 <;> ring

theorem short_angle_bound {M c : ℕ} [NeZero c] (hc : c≤M) {t Δ : ℝ} (ht : 0<t)
    (ht1 : t≤1) (hd : 0<Δ) (h1 : Δ≤1) (a b : ℕ → ℂ) :
    ‖form M c a b (fun m n => (rawWindow t (argument c m n):ℂ))‖ ≤
      (scale c*(2*(M:ℝ))*ampCost M c a b/sqrt (cos 1))*Δ+
        ampCost M c a b/(sin Δ*sqrt (cos 1))+ampCost M c a b/sin Δ := by
  have hπ : Δ≤π/2 := by linarith only [h1,pi_gt_three]
  rw [physical_angular_split ht hd hπ]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (near_bound hc ⟨ht.le,ht1⟩ hd h1 a b)
      (boundary_bound hc ⟨ht.le,ht1⟩ hd h1 a b))) (remainder_bound hc ⟨ht.le,ht1⟩ hd hπ a b))

end ImbalancedChen.Part3.OriginalHolomorphicShortAngleBounds20261113
end
