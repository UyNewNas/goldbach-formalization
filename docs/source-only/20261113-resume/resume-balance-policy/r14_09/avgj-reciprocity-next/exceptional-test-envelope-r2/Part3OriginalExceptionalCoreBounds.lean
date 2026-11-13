import ImbalancedChen.Part3GeneralIOrderHolomorphy
import ImbalancedChen.Part3ActualGeneralJBessel
import Mathlib.Analysis.Complex.Liouville

/-! Uniform lower, upper and order-derivative bounds on the actual
alternating J core near zero, on any compact real order band below one. -/
namespace ImbalancedChen.Part3.OriginalExceptionalCoreBounds20261113
noncomputable section
open Set Filter Complex Metric
open scoped Topology BigOperators
open GeneralComplexISeriesSourceOnly GeneralIOrderHolomorphySourceOnly

private theorem ball_price {B : ℝ} (bp : 0<B) (lt : B<1) :
    ∃ K : ℝ,0<K ∧ ∀ ν z : ℂ,‖ν‖≤B → ‖z‖≤1 →
      ‖generalICore ν z‖≤K ∧ ‖generalICore ν z-generalICore ν 0‖≤K*‖z‖ := by
  let r := 1-B
  have rp : 0<r := sub_pos.mpr lt
  obtain ⟨C,c⟩ := (isCompact_closedBall (0:ℂ) B).exists_bound_of_continuousOn
    ((differentiable_generalICoeff_order 0).continuous.continuousOn)
  let A := max C 1
  have ap : 0<A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let g := fun n : ℕ => A*((r⁻¹)^n/(n.factorial:ℝ))
  have sg : Summable g := (Real.summable_pow_div_factorial _).mul_left _
  have nn (n : ℕ) : 0≤g n := mul_nonneg ap.le (div_nonneg (pow_nonneg (inv_nonneg.mpr rp.le) _) (Nat.cast_nonneg _))
  let K := 1+∑' n,g n
  have kp : 0<K := add_pos_of_pos_of_nonneg zero_lt_one (tsum_nonneg nn)
  refine ⟨K,kp,fun ν z hv hz => ?_⟩
  have re : r≤ν.re+1 := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm ν).trans hv)).1
    dsimp only [r];linarith
  have ord : -1<ν.re := by linarith only [rp,re]
  have base : ‖(Complex.Gamma (ν+1))⁻¹‖≤A := by
    have opt := c ν (show ν∈closedBall 0 B by simpa only [mem_closedBall,dist_zero_right] using hv)
    simpa only [generalICoeff,Nat.factorial_zero,Nat.cast_one,Nat.cast_zero,zero_add,one_mul] using
      opt.trans (le_max_left C 1)
  have cb (n : ℕ) : ‖generalICoeff ν n‖≤g n := by
    apply (generalICoeff_norm_le ord n).trans
    calc
      _ ≤ A/(r^n*(n.factorial:ℝ)) := by
        apply div_le_div₀ ap.le base
          (mul_pos (pow_pos rp _) (by exact_mod_cast Nat.factorial_pos n))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ rp.le re n) (Nat.cast_nonneg _)
      _ = _ := by simp only [g,inv_pow,div_eq_mul_inv,mul_inv_rev];ring
  have S := summable_norm_generalICore ord z
  have ub (n : ℕ) : ‖generalICoeff ν n*z^n‖≤g n := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ ‖generalICoeff ν n‖*1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hz) (norm_nonneg _)
      _ ≤ g n := by rw [mul_one]; exact cb n
  have get := (norm_tsum_le_tsum_norm S).trans (S.tsum_le_tsum ub sg)
  have sk : (∑' n,g n)≤K := le_add_of_nonneg_left zero_le_one
  refine ⟨get.trans sk,?_⟩
  let F := fun n : ℕ => generalICoeff ν n*z^n
  have tail : generalICore ν z-generalICore ν 0=∑' n,F (n+1) := by
    have E := S.of_norm.tsum_eq_zero_add
    rw [generalICore_zero]
    change (∑' n,F n)-_=_
    change (∑' n,F n)=F 0+∑' n,F (n+1) at E
    rw [E]
    simp only [F,generalICoeff,Nat.factorial_zero,Nat.cast_one,Nat.cast_zero,zero_add,one_mul,pow_zero,mul_one]
    ring
  rw [tail]
  have st : Summable (fun n => ‖F (n+1)‖) := (summable_nat_add_iff 1).mpr S
  have gt : Summable (fun n => g (n+1)) := (summable_nat_add_iff 1).mpr sg
  apply (norm_tsum_le_tsum_norm st).trans
  have bound (n : ℕ) : ‖F (n+1)‖≤g (n+1)*‖z‖ := by
    simp only [F,norm_mul,norm_pow,pow_succ]
    apply mul_le_mul (cb _) _ (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) (nn _)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hz (n:=n)) (norm_nonneg z)
  have D := st.tsum_le_tsum bound (gt.mul_right ‖z‖)
  rw [tsum_mul_right] at D
  exact D.trans (mul_le_mul_of_nonneg_right (by have eq := sg.tsum_eq_zero_add;linarith only [eq,nn 0,sk]) (norm_nonneg _))

/-- The three constants and the admissible argument radius precede the
real order and test argument. The final inequality is for the complex
order derivative, so also gives a Lipschitz estimate along real segments. -/
theorem core_band {T : ℝ} (t0 : 0≤T) (t1 : T<1) :
    ∃ c K d : ℝ,0<c ∧ 0<K ∧ 0<d ∧ d≤1 ∧ ∀ ν : ℝ,|ν|≤T → ∀ z : ℂ,‖z‖≤d →
      c≤(generalICore (ν:ℂ) z).re ∧ ‖generalICore (ν:ℂ) z‖≤K ∧
        ‖deriv (fun μ => generalICore μ z) (ν:ℂ)‖≤K := by
  let B := (1+T)/2
  let R := B-T
  have b0 : 0<B := by dsimp [B];linarith
  have b1 : B<1 := by dsimp [B];linarith
  have rp : 0<R := by dsimp [R,B];linarith
  obtain ⟨U,up,h⟩ := ball_price b0 b1
  let g := fun x : ℝ => (generalICoeff (x:ℂ) 0).re
  have cg : Continuous g := Complex.continuous_re.comp
    ((differentiable_generalICoeff_order 0).continuous.comp Complex.continuous_ofReal)
  obtain ⟨v,hv,low⟩ := (isCompact_Icc : IsCompact (Icc (-T) T)).exists_isMinOn
    ⟨0,neg_nonpos.mpr t0,t0⟩ cg.continuousOn
  have eqg (x : ℝ) : g x=(Real.Gamma (x+1))⁻¹ := by
    change ((↑(Nat.factorial 0) * Complex.Gamma (↑(0:ℕ)+(x:ℂ)+1))⁻¹).re = _
    simp only [Nat.factorial_zero,Nat.cast_one,Nat.cast_zero,zero_add,one_mul]
    rw [show (x:ℂ)+1=((x+1:ℝ):ℂ) by push_cast <;> rfl,Complex.Gamma_ofReal,←Complex.ofReal_inv,Complex.ofReal_re]
  have gp : 0<g v := by rw [eqg];exact inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith [hv.1]))
  let d := min 1 (g v/(2*U))
  have dp : 0<d := lt_min zero_lt_one (div_pos gp (by positivity))
  let K := U+U/R
  refine ⟨g v/2,K,d,by positivity,add_pos up (div_pos up rp),dp,min_le_left _ _,fun ν hn z hz => ?_⟩
  have nv : ‖(ν:ℂ)‖≤B := by rw [Complex.norm_real,Real.norm_eq_abs];dsimp [B];linarith
  have hZ := h (ν:ℂ) z nv (hz.trans (min_le_left _ _))
  have zero : (generalICore (ν:ℂ) 0).re=g ν := by simp only [g,generalICore_zero,generalICoeff,Nat.factorial_zero,
    Nat.cast_one,Nat.cast_zero,zero_add,one_mul]
  have sc : U*‖z‖≤g v/2 := by
    have e := (le_div_iff₀ (show 0<2*U by positivity)).mp (hz.trans (min_le_right _ _))
    linarith only [e]
  have diff := Complex.re_le_norm (generalICore (ν:ℂ) 0-generalICore (ν:ℂ) z)
  rw [Complex.sub_re,zero,norm_sub_rev] at diff
  have L : g v≤g ν := low (abs_le.mp hn)
  have W (u : ℂ) (hu : u∈closedBall (ν:ℂ) R) : ‖u‖≤B := by
    have dx : ‖u-(ν:ℂ)‖≤R := by simpa only [mem_closedBall,dist_eq_norm] using hu
    calc
      _ ≤ ‖u-(ν:ℂ)‖+‖(ν:ℂ)‖ := by simpa only [sub_add_cancel] using norm_add_le (u-(ν:ℂ)) (ν:ℂ)
      _ ≤ R+T := add_le_add dx (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hn)
      _ = B := sub_add_cancel B T
  have der : ‖deriv (fun μ => generalICore μ z) (ν:ℂ)‖≤U/R := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le rp
    · apply (analyticOnNhd_generalICore_order z).differentiableOn.diffContOnCl_ball
      intro u hu
      have re := (abs_le.mp ((Complex.abs_re_le_norm u).trans (W u hu))).1
      change -1<u.re
      linarith
    · exact fun u hu => (h u z (W u (sphere_subset_closedBall hu)) (hz.trans (min_le_left _ _))).1
  exact ⟨by linarith only [diff,hZ.2,sc,L],hZ.1.trans (le_add_of_nonneg_right (div_nonneg up.le rp.le)),
    der.trans (le_add_of_nonneg_left up.le)⟩

end
end ImbalancedChen.Part3.OriginalExceptionalCoreBounds20261113
