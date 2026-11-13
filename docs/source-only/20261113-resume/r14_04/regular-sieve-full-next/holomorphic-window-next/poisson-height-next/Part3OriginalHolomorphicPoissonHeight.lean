import ImbalancedChen.Part3OriginalHolomorphicBesselCoefficient
import ImbalancedChen.Part3OriginalHolomorphicOddWindow

/-! Sum over the exact integral Petersson orders with their Poisson
weight, and pay the diagonal of the corrected positive window. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicPoissonHeight20261113
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly (generalJ)
open OriginalHolomorphicBesselCoefficient20261113 (wave integer_bessel_coefficient)
open OriginalHolomorphicOddWindow20261113 (weight weight_nonnegative)
open CompletedKWeightedIntegral20261026b
  (integerPhase integerPhase_norm integerPhase_continuous)

def heightKernel (u y : ℝ) : ℂ :=
  let Z := (Real.exp (-u):ℂ)*integerPhase (-1) y
  Z/(1-Z)^2

private theorem phase_power (h : ℕ) (y : ℝ) :
    integerPhase (-(h:ℤ)) y=integerPhase (-1) y^h := by
  unfold integerPhase
  rw [←exp_nat_mul]
  congr 1
  push_cast <;> ring

private theorem wave_norm (x y : ℝ) : ‖wave x y‖=1 := by
  simp [wave,norm_exp,mul_re]

private theorem wave_cont (x : ℝ) : Continuous (wave x) := by unfold wave; fun_prop

theorem native_order_norm (h : ℕ) (x : ℝ) : ‖generalJ (h:ℂ) x‖≤1 := by
  have T := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=1) (f:=fun y => wave x y*integerPhase (-(h:ℤ)) y)
    (fun y _ => by simp [norm_mul,wave_norm,integerPhase_norm])
  simpa only [integer_bessel_coefficient,norm_mul,norm_pow,norm_I,one_pow,one_mul,
    sub_zero,abs_one,mul_one] using T

private def heightTerm (u x : ℝ) (h : ℕ) (y : ℝ) : ℂ :=
  (((h:ℝ)*Real.exp (-u)^h:ℝ):ℂ)*(wave x y*integerPhase (-(h:ℤ)) y)

private theorem height_sum {u : ℝ} (hu : 0<u) (x y : ℝ) :
    HasSum (fun h => heightTerm u x h y) (wave x y*heightKernel u y) := by
  let r := Real.exp (-u)
  let Z : ℂ := (r:ℂ)*integerPhase (-1) y
  have r0 : 0<r := Real.exp_pos _
  have r1 : r<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have HZ : ‖Z‖<1 := by
    simpa only [Z,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos r0,integerPhase_norm,mul_one] using r1
  apply ((hasSum_coe_mul_geometric_of_norm_lt_one HZ).mul_left (wave x y)).congr_fun
  intro h
  dsimp only [Z,r,heightTerm]
  rw [phase_power]
  simp only [mul_pow,ofReal_mul,ofReal_pow,ofReal_natCast]
  ring

def orderTerm (u x : ℝ) (h : ℕ) : ℂ :=
  (((h:ℝ)*Real.exp (-u)^h:ℝ):ℂ)*(I^h*generalJ (h:ℂ) x)

/-- Analytic height sum of the native generalJ coefficients on the unit
circle, with the exact first Poisson derivative Z/(1−Z)². -/
theorem poisson_height_sum {u : ℝ} (hu : 0<u) (x : ℝ) :
    HasSum (orderTerm u x) (∫ y in (0:ℝ)..1, wave x y*heightKernel u y) := by
  let r := Real.exp (-u)
  have r0 : 0<r := Real.exp_pos _
  have r1 : r<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have H : Summable (fun h : ℕ => (h:ℝ)*r^h) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs,abs_of_pos r0] using r1)).summable
  have integ (h : ℕ) : Integrable (heightTerm u x h) (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((continuous_const.mul ((wave_cont x).mul (integerPhase_continuous _))).intervalIntegrable (0:ℝ) 1).1
  have nrm (h : ℕ) (y : ℝ) : ‖heightTerm u x h y‖=(h:ℝ)*r^h := by
    have p := mul_nonneg (Nat.cast_nonneg h : (0:ℝ)≤h) (pow_nonneg r0.le h)
    simp only [heightTerm,norm_mul,Complex.norm_real,Real.norm_eq_abs,wave_norm,integerPhase_norm,
      mul_one,abs_of_nonneg p,r]
  have masses (h : ℕ) : (∫ y in Ioc (0:ℝ) 1, ‖heightTerm u x h y‖)=(h:ℝ)*r^h := by
    rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    simp only [nrm]
    simp
  have mass : Summable (fun h : ℕ => ∫ y in Ioc (0:ℝ) 1, ‖heightTerm u x h y‖) := by
    simpa only [masses] using H
  have order (h : ℕ) : (∫ y in Ioc (0:ℝ) 1, heightTerm u x h y)=orderTerm u x h := by
    rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),heightTerm,
      intervalIntegral.integral_const_mul,integer_bessel_coefficient,orderTerm]
  have sn : Summable (fun h => ‖orderTerm u x h‖) := by
    apply H.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro h
    have p := mul_nonneg (Nat.cast_nonneg h : (0:ℝ)≤h) (pow_nonneg r0.le h)
    dsimp only [orderTerm]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg p,norm_mul,norm_pow,norm_I,one_pow,one_mul]
    exact mul_le_of_le_one_right p (native_order_norm h x)
  have E : (∑' h,orderTerm u x h)=(∫ y in (0:ℝ)..1,wave x y*heightKernel u y) := by
    simp_rw [←order]
    rw [integral_tsum_of_summable_integral_norm integ mass,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    exact setIntegral_congr_fun measurableSet_Ioc
      (fun y _ => (height_sum hu x y).tsum_eq)
  rw [←E]
  exact sn.of_norm.hasSum

private theorem diagonal_envelope {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    Real.exp (-t)/(1-Real.exp (-t))^2 ≤ 4/t^2 := by
  let r := Real.exp (-t)
  have rp : 0<r := Real.exp_pos _
  have r1 : r<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have e : 1+t≤Real.exp t := by simpa only [add_comm] using Real.add_one_le_exp t
  have er : Real.exp t*r=1 := by dsimp only [r]; rw [←Real.exp_add]; simp
  have low : t/2≤1-r := by
    have P := mul_le_mul_of_nonneg_right e rp.le
    rw [er] at P
    have z : t≤(1-r)*(1+t) := by nlinarith only [P]
    have u := mul_le_mul_of_nonneg_left (show 1+t≤2 by linarith only [ht1]) (sub_nonneg.mpr r1.le)
    linarith only [z,u]
  have ds := pow_le_pow_left₀ (by linarith only [ht] : 0≤t/2) low 2
  change r/(1-r)^2≤4/t^2
  apply (div_le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr r1)) (sq_pos_of_pos ht)).mpr
  have h := mul_le_mul_of_nonneg_right r1.le (sq_nonneg t)
  nlinarith only [h,ds]

def oddDiagonal (t : ℝ) (h : ℕ) : ℝ :=
  if Odd h then (h:ℝ)*weight t h else 0

/-- The complete corrected positive-order diagonal for every cumulative
height K≥1 has cost 4K², including the removed order 1. -/
theorem corrected_diagonal_bound {K : ℝ} (hK : 1≤K) :
    Summable (oddDiagonal (1/K)) ∧ (∑' h,oddDiagonal (1/K) h)≤4*K^2 := by
  have kp := zero_lt_one.trans_le hK
  let t := 1/K
  have tp : 0<t := one_div_pos.mpr kp
  have t1 : t≤1 := (div_le_one kp).mpr hK
  let r := Real.exp (-t)
  have rp : 0<r := Real.exp_pos _
  have r1 : r<1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr tp)
  have H : HasSum (fun h : ℕ => (h:ℝ)*r^h) (r/(1-r)^2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs,abs_of_pos rp] using r1)
  have positive (h : ℕ) : 0≤oddDiagonal t h := by
    unfold oddDiagonal
    by_cases p : Odd h
    · rw [if_pos p]
      have h0 : 1≤h := by obtain ⟨k,hk⟩ := p; omega
      exact mul_nonneg (Nat.cast_nonneg _) (weight_nonnegative t1 h0)
    · rw [if_neg p]
  have per (h : ℕ) : oddDiagonal t h≤(h:ℝ)*r^h := by
    unfold oddDiagonal
    split
    · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      dsimp only [r,weight]
      rw [←Real.exp_nat_mul,show (h:ℝ)*(-t)=-(h:ℝ)*t by ring]
      exact sub_le_self _ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg rp.le _)
  have S := H.summable.of_nonneg_of_le positive per
  refine ⟨S,((S.tsum_le_tsum per H.summable).trans_eq H.tsum_eq).trans ?_⟩
  convert diagonal_envelope tp t1 using 1 <;> dsimp only [t,r] <;> field_simp [kp.ne'] <;> ring

end ImbalancedChen.Part3.OriginalHolomorphicPoissonHeight20261113
end
