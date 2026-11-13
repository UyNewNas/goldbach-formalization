import Mathlib

/-! Positive cumulative weight on the original odd Petersson order k-1
and the bounded angular amplitude in its summed geometric window. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicOddWindow20261113
open Real Set

def weight (t : ℝ) (h : ℕ) : ℝ := exp (-(h:ℝ)*t)-exp (2-t)*exp (-2*(h:ℝ))

theorem weight_one (t : ℝ) : weight t 1=0 := by
  unfold weight
  rw [←exp_add,sub_eq_zero]
  congr 1 <;> push_cast <;> ring

private theorem weight_factor (t : ℝ) (h : ℕ) :
    weight t h=exp (-(h:ℝ)*t)*(1-exp (-((h:ℝ)-1)*(2-t))) := by
  rw [weight,mul_sub,mul_one,←exp_add,←exp_add]
  congr 2 <;>ring

theorem weight_nonnegative {t : ℝ} (ht : t≤1) {h : ℕ} (hh : 1≤h) : 0≤weight t h := by
  rw [weight_factor]
  apply mul_nonneg (exp_pos _).le (sub_nonneg.mpr _)
  apply exp_le_one_iff.mpr
  have h1 : 1≤(h:ℝ) := by exact_mod_cast hh
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr h1))
    (by linarith only [ht])

def floorConstant : ℝ := exp (-1)*(1-exp (-2))

theorem floorConstant_pos : 0<floorConstant := by
  apply mul_pos (exp_pos _) (sub_pos.mpr _)
  exact exp_lt_one_iff.mpr (by norm_num)

theorem original_odd_order_floor {K : ℝ} (hK : 1≤K) {h : ℕ} (hh : 3≤h) (hcut : (h:ℝ)≤K) :
    floorConstant≤weight (1/K) h := by
  have kp := zero_lt_one.trans_le hK
  have t1 : 1/K≤1 := (div_le_one kp).mpr hK
  have h3 : 3≤(h:ℝ) := by exact_mod_cast hh
  have U : 1≤2-1/K := by linarith only [t1]
  have D : 2≤(h:ℝ)-1 := by linarith only [h3]
  have z := mul_le_mul D U (by norm_num : (0:ℝ)≤1) (by linarith only [h3])
  have ratio : exp (-((h:ℝ)-1)*(2-1/K))≤exp (-2) := exp_le_exp.mpr (by linarith only [z])
  have H : exp (-1)≤exp (-(h:ℝ)*(1/K)) := by
    apply exp_le_exp.mpr
    have T := (div_le_one kp).mpr hcut
    simpa only [one_div,div_eq_mul_inv,neg_mul] using neg_le_neg T
  rw [weight_factor]
  exact mul_le_mul H (by linarith only [ratio]) (sub_nonneg.mpr (exp_le_one_iff.mpr (by norm_num)))
    (exp_pos _).le

def amplitude (u y : ℝ) : ℝ := cosh u*(sin y)^2/((sinh u)^2+(sin y)^2)
def angleQuotient (u y : ℝ) : ℝ := cosh u*sin y/((sinh u)^2+(sin y)^2)
def derivativeValue (u y : ℝ) : ℝ :=
  cosh u*cos y*((sinh u)^2-(sin y)^2)/((sinh u)^2+(sin y)^2)^2

theorem amplitude_bound (u y : ℝ) : 0≤amplitude u y ∧ amplitude u y≤cosh u := by
  have C := (cosh_pos u).le
  have h0 : 0≤(sinh u)^2+(sin y)^2 := by positivity
  refine ⟨div_nonneg (mul_nonneg C (sq_nonneg _)) h0,?_⟩
  by_cases z : (sinh u)^2+(sin y)^2=0
  · simp only [amplitude,z,div_zero];exact C
  · apply (div_le_iff₀ (lt_of_le_of_ne h0 (Ne.symm z))).mpr
    have h := mul_nonneg C (sq_nonneg (sinh u))
    linarith only [h]

theorem quotient_eq {u y : ℝ} (hy : sin y≠0) : amplitude u y/sin y=angleQuotient u y := by
  unfold amplitude angleQuotient
  have d := add_pos_of_nonneg_of_pos (sq_nonneg (sinh u)) (sq_pos_of_ne_zero hy)
  field_simp [hy,d.ne'] <;>ring

theorem quotient_derivative (u y : ℝ) (hy : sin y≠0) :
    HasDerivAt (angleQuotient u) (derivativeValue u y) y := by
  have d : (sinh u)^2+(sin y)^2≠0 :=
    (add_pos_of_nonneg_of_pos (sq_nonneg (sinh u)) (sq_pos_of_ne_zero hy)).ne'
  have p := ((hasDerivAt_sin y).const_mul (cosh u)).div
    (((hasDerivAt_sin y).pow 2).const_add ((sinh u)^2)) d
  convert p using 1 <;> dsimp [angleQuotient,derivativeValue] <;>ring

theorem derivative_bound (u y : ℝ) (hy : 0<sin y) (hc : 0≤cos y) :
    |derivativeValue u y|≤cosh u*cos y/(sin y)^2 := by
  let B := (sinh u)^2
  let S := (sin y)^2
  have b0 : 0≤B := sq_nonneg _
  have s0 : 0<S := sq_pos_of_pos hy
  have d0 := add_pos_of_nonneg_of_pos b0 s0
  have c0 := mul_nonneg (cosh_pos u).le hc
  have V : |B-S|≤B+S := abs_le.mpr ⟨by linarith only [b0],by linarith only [s0]⟩
  change |cosh u*cos y*(B-S)/(B+S)^2|≤cosh u*cos y/S
  rw [abs_div,abs_mul,abs_of_nonneg c0,abs_of_nonneg (sq_nonneg _)]
  have U := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left V c0) (sq_nonneg (B+S))
  apply U.trans
  have E : cosh u*cos y*(B+S)/(B+S)^2=cosh u*cos y/(B+S) := by field_simp [d0.ne'] <;>ring
  rw [E]
  exact div_le_div_of_nonneg_left c0 s0 (le_add_of_nonneg_left b0)

def correctedAmplitude (t y : ℝ) := amplitude t y-exp (2-t)*amplitude 2 y
def correctedDerivative (t y : ℝ) := derivativeValue t y-exp (2-t)*derivativeValue 2 y
def amplitudeConstant := cosh 2*(1+exp 2)

private theorem two_bounds {t : ℝ} (ht : t∈Icc 0 1) :
    cosh t≤cosh 2 ∧ exp (2-t)≤exp 2 := by
  constructor
  · apply cosh_le_cosh.mpr
    rw [abs_of_nonneg ht.1,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [ht.2]
  · exact exp_le_exp.mpr (by linarith only [ht.1])

theorem corrected_amplitude_bound {t : ℝ} (ht : t∈Icc 0 1) (y : ℝ) :
    |correctedAmplitude t y|≤amplitudeConstant := by
  obtain ⟨A,B⟩ := two_bounds ht
  have u := amplitude_bound t y
  have v := amplitude_bound 2 y
  have C := mul_le_mul B v.2 v.1 (exp_pos _).le
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg u.1,abs_of_nonneg (mul_nonneg (exp_pos _).le v.1)]
  dsimp only [amplitudeConstant]
  nlinarith only [C,u.2,A]

theorem corrected_derivative_bound {t y : ℝ} (ht : t∈Icc 0 1) (hy : 0<sin y) (hc : 0≤cos y) :
    |correctedDerivative t y|≤amplitudeConstant*(cos y/(sin y)^2) := by
  obtain ⟨A,B⟩ := two_bounds ht
  have D : 0≤cos y/(sin y)^2 := div_nonneg hc (sq_nonneg _)
  have T : ∀ u : ℝ, |derivativeValue u y|≤cosh u*(cos y/(sin y)^2) := by
    intro u
    simpa only [mul_div_assoc] using derivative_bound u y hy hc
  have V := mul_le_mul B (T 2) (abs_nonneg _) (exp_pos _).le
  have U := (T t).trans (mul_le_mul_of_nonneg_right A D)
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_pos (exp_pos _)]
  dsimp only [amplitudeConstant]
  nlinarith only [U,V]

end ImbalancedChen.Part3.OriginalHolomorphicOddWindow20261113
end
