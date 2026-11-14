import ImbalancedChen.Part3OriginalRegularMarkedDyadic
import ImbalancedChen.Part3OriginalRegularBaseCumulative

/-! Add the geometric height shells. The length charge is repeated
only up to the last shell below the given height. Its multiplicity is
paid by length slack or by the diagonal square, uniformly in the level. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularCumulativePrice20261113
open Real Set Finset
open OriginalHolomorphicInfinityPacket20261113 (start start_rpow)
open OriginalRegularGaussianOffDiagonal20261113 (cost)
open OriginalRegularBaseCumulative20261113 (baseConstant baseConstant_pos)

def cut (n : ℕ) := 2*(2:ℝ)^n
theorem first : cut 0=2 := by norm_num [cut]
theorem twice (n : ℕ) : cut (n+1)=2*cut n := by simp only [cut,pow_succ];ring
theorem two_le (n : ℕ) : 2≤cut n := by
  have h : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
  dsimp only [cut]
  linarith only [h]

private theorem count (n : ℕ) : (n:ℝ)+1≤(2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have one : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_succ,pow_succ]
    linarith only [one,ih]

theorem locate {K : ℝ} (k1 : 1≤K) : ∃ n : ℕ,K≤cut n ∧ (2:ℝ)^n≤K := by
  obtain ⟨j,hj⟩ := exists_nat_ge K
  have big : K≤cut j := by
    have a := count j
    dsimp only [cut]
    linarith only [hj,a,Nat.cast_nonneg (α:=ℝ) j]
  have chooseCut (l : ℕ) : K≤cut l → ∃ n : ℕ,K≤cut n ∧ (2:ℝ)^n≤K := by
    induction l with
    | zero => exact fun z => ⟨0,z,by simpa only [pow_zero] using k1⟩
    | succ l J =>
      intro z
      by_cases low : K≤cut l
      · exact J low
      · refine ⟨l+1,z,?_⟩
        simpa only [cut,pow_succ,mul_comm] using (le_of_not_ge low)
  exact chooseCut j big

def repeatCost (d : ℝ) := 1+(1+d)/(d*log 2)
def finalCost (d : ℝ) := 9+repeatCost d*3^(1+2*d)
def common (C d : ℝ) := max (1+baseConstant) (C*(|π*sqrt π/8|+|cost d|+1))

theorem common_positive (C d : ℝ) : 0<common C d :=
  (show 0<1+baseConstant by linarith only [baseConstant_pos]).trans_le (le_max_left _ _)

theorem common_base (C d : ℝ) : baseConstant≤common C d :=
  (by linarith : baseConstant≤1+baseConstant).trans (le_max_left _ _)

theorem common_shell {C d x y : ℝ} (hC : 0≤C) (hx : 0≤x) (hy : 0≤y) :
    C*((π*sqrt π/8)*x+cost d*y)≤common C d*(x+y) := by
  let b := |π*sqrt π/8|+|cost d|+1
  have u : π*sqrt π/8≤b := (le_abs_self _).trans (by dsimp only [b];linarith only [abs_nonneg (cost d)])
  have v : cost d≤b := (le_abs_self _).trans (by dsimp only [b];linarith only [abs_nonneg (π*sqrt π/8)])
  have eq : C*b≤common C d := le_max_right _ _
  calc
    _≤C*(b*x+b*y) := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_right u hx) (mul_le_mul_of_nonneg_right v hy)) hC
    _=(C*b)*(x+y) := by ring
    _≤_ := mul_le_mul_of_nonneg_right eq (add_nonneg hx hy)

theorem initial_length {d L : ℝ} (hd : 0<d) : L≤(start L:ℝ)^(1+d) := by
  have m : L<(start L:ℝ) := by simpa [start] using Nat.lt_floor_add_one L
  have m1 : 1≤(start L:ℝ) := by exact_mod_cast (Nat.succ_pos ⌊L⌋₊)
  exact m.le.trans (Real.self_le_rpow_of_one_le m1 (by linarith only [hd]))

theorem repeat_positive {d : ℝ} (hd : 0<d) : 0<repeatCost d := by
  have l : 0<log 2 := log_pos (by norm_num)
  dsimp only [repeatCost]
  positivity

theorem final_positive {d : ℝ} (hd : 0<d) : 0<finalCost d := by
  have rp := repeat_positive hd
  dsimp only [finalCost]
  positivity

/-- The full shell count charges only the arithmetic term. The cost
uses epsilon = 2d and holds also for one occupied integer. -/
theorem cumulative_price {d K L : ℝ} (hd : 0<d) (hL : 1/2≤L) {q : ℕ+}
    {n : ℕ} (h : (2:ℝ)^n≤K) :
    2*(cut n)^2+((n:ℝ)+1)*((start L:ℝ)^(1+d)/q.val)≤
      finalCost d*(K^2+L^(1+2*d)/q.val) := by
  let M : ℝ := start L
  let X := M^(1+d)
  let Y := M^(1+2*d)
  have m1 : 1≤M := by exact_mod_cast (Nat.succ_pos ⌊L⌋₊)
  have mp := zero_lt_one.trans_le m1
  have lp : 0<L := by linarith only [hL]
  have zp : 0<(q.val:ℝ) := by exact_mod_cast q.property
  have z1 : 1≤(q.val:ℝ) := by exact_mod_cast q.property
  have xp : 0<X := rpow_pos_of_pos mp _
  have yp : 0<Y := rpow_pos_of_pos mp _
  have k1 : 1≤K := (show 1≤(2:ℝ)^n from one_le_pow₀ (by norm_num)).trans h
  have ell : 0<log 2 := log_pos (by norm_num)
  have rp := repeat_positive hd
  have Q : 2*(cut n)^2≤8*K^2 := by
    have sq := pow_le_pow_left₀ (show 0≤(2:ℝ)^n by positivity) h 2
    dsimp only [cut]
    nlinarith only [sq]
  have alg : X*M^d=Y := by
    dsimp only [X,Y]
    rw [←rpow_add mp,show 1+d+d=1+2*d by ring]
  have pre : ((n:ℝ)+1)*(X/q.val)≤K^2+repeatCost d*(Y/q.val) := by
    by_cases low : X/q.val≤K
    · have w := mul_le_mul ((count n).trans h) low (div_nonneg xp.le zp.le) (by linarith only [k1] : 0≤K)
      have p := mul_nonneg rp.le (div_nonneg yp.le zp.le)
      nlinarith only [w,p]
    · have xbound : K≤X := (le_of_not_ge low).trans (div_le_self xp.le z1)
      have A := log_le_log (show 0<(2:ℝ)^n by positivity) (h.trans xbound)
      rw [log_pow,show X=M^(1+d) from rfl,log_rpow mp] at A
      have B := log_le_sub_one_of_pos (rpow_pos_of_pos mp d)
      rw [log_rpow mp] at B
      have scale : (n:ℝ)≤((1+d)*M^d)/(d*log 2) := by
        apply (le_div_iff₀ (mul_pos hd ell)).mpr
        have a1 := mul_le_mul_of_nonneg_right A hd.le
        have b1 := mul_le_mul_of_nonneg_left B (show 0≤1+d by linarith only [hd])
        nlinarith only [a1,b1,hd]
      have N : (n:ℝ)+1≤repeatCost d*M^d := by
        have m := one_le_rpow m1 hd.le
        dsimp only [repeatCost]
        simp only [div_eq_mul_inv] at scale ⊢
        nlinarith only [scale,m]
      have w := mul_le_mul_of_nonneg_right N (div_nonneg xp.le zp.le)
      have E : repeatCost d*M^d*(X/q.val)=repeatCost d*(Y/q.val) := by rw [←alg];ring
      rw [E] at w
      exact w.trans (le_add_of_nonneg_left (sq_nonneg K))
  have T : Y≤3^(1+2*d)*L^(1+2*d) := start_rpow (by linarith only [hd] : 0<2*d) hL
  have V := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right T zp.le) rp.le
  have C0 : 0≤repeatCost d*(3:ℝ)^(1+2*d) := mul_nonneg rp.le (rpow_nonneg (by norm_num) _)
  have P := mul_nonneg C0 (sq_nonneg K)
  have Z := div_nonneg (rpow_nonneg lp.le (1+2*d)) zp.le
  change 2*(cut n)^2+((n:ℝ)+1)*(X/q.val)≤_
  dsimp only [finalCost]
  simp only [div_eq_mul_inv] at pre V Z ⊢
  nlinarith only [Q,pre,V,P,Z]

end ImbalancedChen.Part3.OriginalRegularCumulativePrice20261113
end
