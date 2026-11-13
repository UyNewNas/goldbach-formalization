import ImbalancedChen.Part3OriginalSwitchedOrderAwayZero

/-! The additive exceptional weight in the level recurrence:
the logarithmic small-order loss is charged to the Y^ε term alone. -/
namespace ImbalancedChen.Part3.OriginalSwitchedAdditiveWeight20261113
noncomputable section
open Set MeasureTheory Complex
open CommonSmoothCutoff (dyadicCutoff)
open OriginalSwitchedMellinRows20261113 (wave)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)
open OriginalExceptionalMellinCeiling20261113 (tested_ceiling)
open OriginalSwitchedOrderAwayZero20261113 (away_ceiling)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau mem_exceptional)
open ActualPositiveNativeDiagonal20261112 (nativeWeight complementaryHeight complementary_range)

theorem additive_ceiling {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ C Y₀ : ℝ,0<C ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ s : ℝ,0<s → s≤T → ∀ t : ℝ,
      ‖exceptionalWeight (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) (s/2)‖≤
        C*(Y^s+Y^ε) := by
  let η := ε/2
  have ηp : 0<η := by dsimp [η];positivity
  obtain ⟨B,Z,bp,z1,f⟩ := tested_ceiling tp t1
  obtain ⟨K,X,kp,x1,g⟩ := away_ceiling tp t1 ηp
  let A := 1+Real.log 4+1/η
  have lp : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have ap : 0<A := by dsimp only [A];positivity
  refine ⟨K+B*A,max X Z,add_pos kp (mul_pos bp ap),x1.trans (le_max_left _ _),fun Y hy s sp st t => ?_⟩
  have y1 := x1.trans ((le_max_left _ _).trans hy)
  have yp := zero_lt_one.trans_le y1
  have ye := Real.rpow_nonneg yp.le ε
  have ys := Real.rpow_nonneg yp.le s
  by_cases he : η≤s
  · apply (g Y ((le_max_left _ _).trans hy) s he st t).trans
    exact mul_le_mul (le_add_of_nonneg_right (mul_nonneg bp.le ap.le)) (le_add_of_nonneg_right ye) ys (by positivity)
  · have one : 1≤Y^η := Real.one_le_rpow y1 ηp.le
    have log : 1+Real.log (4*Y)≤A*Y^η := by
      rw [Real.log_mul (by norm_num) yp.ne']
      dsimp only [A]
      have l := Real.log_le_rpow_div yp.le ηp
      rw [div_eq_mul_inv] at l
      have h := mul_le_mul_of_nonneg_left one (add_nonneg zero_le_one lp)
      nlinarith only [h,l]
    have small := Real.rpow_le_rpow_of_exponent_le y1 (le_of_not_ge he)
    have prod := mul_le_mul log small ys (mul_nonneg ap.le (Real.rpow_nonneg yp.le _))
    have p : Y^η*Y^η=Y^ε := by rw [←Real.rpow_add yp,show η+η=ε by dsimp [η];ring]
    have h : (1+Real.log (4*Y))*Y^s≤A*Y^ε := by
      simpa only [mul_assoc,p] using prod
    apply (f Y ((le_max_right _ _).trans hy) s sp st t).trans
    calc
      _ ≤ (B*A)*Y^ε := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h bp.le
      _ ≤ _ := mul_le_mul (le_add_of_nonneg_left kp.le) (le_add_of_nonneg_left ys) ye (by positivity)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

theorem native_additive {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ C Y₀ : ℝ,0<C ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ (z : ℕ+) (i : ↥(exceptional z)),tau z i.val≤T → ∀ t : ℝ,
      ‖nativeWeight z.val (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) i.val‖≤
        C*(Y^(tau z i.val)+Y^ε) := by
  obtain ⟨K,X,kp,x1,h⟩ := additive_ceiling tp t1 ep
  let D := Real.cos (Real.pi*(T/2))
  have dp : 0<D := Real.cos_pos_of_mem_Ioo ⟨by nlinarith only [Real.pi_pos,mul_nonneg Real.pi_pos.le tp],
    by nlinarith only [mul_lt_mul_of_pos_left t1 Real.pi_pos]⟩
  refine ⟨K/D,X,div_pos kp dp,x1,fun Y yx z i st t => ?_⟩
  have ex := ((mem_exceptional z i.val).mp i.property).2
  let a := complementaryHeight z.val i.val
  have R := complementary_range z.val ex
  have a0 : 0<a := R.1
  have cp : 0<Real.cos (Real.pi*a) := R.2.2
  have s2 : tau z i.val/2=a := by unfold tau a complementaryHeight; ring
  have sp : 0<tau z i.val := by linarith only [s2,a0]
  have co : D≤Real.cos (Real.pi*a) := Real.cos_le_cos_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le a0.le) (by nlinarith only [Real.pi_pos,mul_lt_mul_of_pos_left t1 Real.pi_pos])
    (mul_le_mul_of_nonneg_left (by linarith only [s2,st]) Real.pi_pos.le)
  have q := h Y yx _ sp st t
  rw [s2] at q
  have yp : 0<Y := zero_lt_one.trans_le (x1.trans yx)
  simp only [nativeWeight,if_pos ex,norm_div,Complex.norm_real,Real.norm_of_nonneg cp.le]
  calc
    _ ≤ (K*(Y^(tau z i.val)+Y^ε))/D := div_le_div₀ (by positivity) q dp co
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalSwitchedAdditiveWeight20261113
