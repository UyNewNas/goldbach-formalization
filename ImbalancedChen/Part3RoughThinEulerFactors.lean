import ImbalancedChen.Part3RoughFiniteEulerLogDerivative

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual finite p<=z Euler factors in a thin LEFT strip. The common radius
rho=2^(-3/4)<1 follows from Re(s)>=1-delta and delta<=1/4, independently
of cutoff or height. The sharper numerator exp(kappa)/p uses the actual
condition delta*log(max 2 z)<=kappa. Principal characters and p|q remain
included. The weighted prime mass stays explicit for its separate primary
supplier; no elementary log-squared replacement or full L bound is used.
-/

namespace ImbalancedChen.Part3.RoughThinEulerFactors20261026b
noncomputable section
open Classical Finset Complex
open scoped BigOperators
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open RoughFiniteEulerLogDerivative20261026b

def primeRadius : ℝ := (2 : ℝ)^(-(3/4 : ℝ))

theorem primeRadius_pos : 0<primeRadius := Real.rpow_pos_of_pos (by norm_num) _

theorem primeRadius_lt_one : primeRadius<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

def logPrimeMass (z : ℝ) : ℝ := ∑ p ∈ smallPrimes z, Real.log (p : ℝ)/(p : ℝ)

theorem logPrimeMass_nonneg (z : ℝ) : 0≤logPrimeMass z := by
  apply Finset.sum_nonneg
  intro p hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (smallPrimes_prime hp).one_lt.le))
    (Nat.cast_nonneg p)

def thinLogCost (κ z : ℝ) : ℝ := Real.exp κ/(1-primeRadius)*logPrimeMass z

theorem thinLogCost_nonneg (κ z : ℝ) : 0≤thinLogCost κ z := by
  exact mul_nonneg (div_nonneg (Real.exp_pos κ).le (by linarith [primeRadius_lt_one]))
    (logPrimeMass_nonneg z)

theorem prime_twist_norm_le_radius {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) {δ : ℝ} (hδ : δ≤1/4) {s : ℂ} (hs : 1-δ≤s.re) :
    ‖χ p*(p : ℂ)^(-s)‖ ≤ primeRadius := by
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast hp.one_lt.le
  calc
    _ ≤ 1*‖(p : ℂ)^(-s)‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (χ.norm_le_one p) (norm_nonneg _)
    _ = (p : ℝ)^(-s.re) := by
      rw [one_mul,Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
    _ ≤ (p : ℝ)^(-(3/4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ ≤ (2 : ℝ)^(-(3/4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)

theorem prime_twist_norm_le_exp_div {q p : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ κ : ℝ} (hz : 0≤z) (hp : p∈smallPrimes z) (hδ : 0≤δ)
    (hκ : δ*Real.log (max 2 z)≤κ) {s : ℂ} (hs : 1-δ≤s.re) :
    ‖χ p*(p : ℂ)^(-s)‖ ≤ Real.exp κ/(p : ℝ) := by
  have hprime := smallPrimes_prime hp
  have hpR : 0<(p : ℝ) := by exact_mod_cast hprime.pos
  have hlog : 0≤Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  have hpz : (p : ℝ)≤max 2 z := ((mem_smallPrimes hz).mp hp).2.trans (le_max_right _ _)
  have hlogz := Real.log_le_log hpR hpz
  have hκp : δ*Real.log (p : ℝ)≤κ :=
    (mul_le_mul_of_nonneg_left hlogz hδ).trans hκ
  calc
    _ ≤ 1*‖(p : ℂ)^(-s)‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (χ.norm_le_one p) (norm_nonneg _)
    _ = Real.exp (Real.log (p : ℝ)*(-s.re)) := by
      rw [one_mul,Complex.norm_natCast_cpow_of_pos hprime.pos,Complex.neg_re,
        Real.rpow_def_of_pos hpR]
    _ ≤ Real.exp (κ-Real.log (p : ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_sub,Real.exp_log hpR]

theorem thin_prime_factor {q p : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : p.Prime) {δ : ℝ} (hδ : δ≤1/4) {s : ℂ} (hs : 1-δ≤s.re) :
    0<(1-χ p*(p : ℂ)^(-s)).re ∧ (1-χ p*(p : ℂ)^(-s))≠0 ∧
      1-primeRadius≤‖1-χ p*(p : ℂ)^(-s)‖ ∧
      ‖(1-χ p*(p : ℂ)^(-s))⁻¹‖≤(1-primeRadius)⁻¹ := by
  have ht := prime_twist_norm_le_radius χ hp hδ hs
  have hre := (abs_le.mp (Complex.abs_re_le_norm (χ p*(p : ℂ)^(-s)))).2
  have hpos : 0<(1-χ p*(p : ℂ)^(-s)).re := by
    simp only [sub_re,one_re]
    linarith [primeRadius_lt_one]
  have hlow : 1-primeRadius≤‖1-χ p*(p : ℂ)^(-s)‖ := by
    have htriangle := norm_add_le (1-χ p*(p : ℂ)^(-s)) (χ p*(p : ℂ)^(-s))
    rw [sub_add_cancel,norm_one] at htriangle
    linarith
  have hmargin : 0<1-primeRadius := by linarith [primeRadius_lt_one]
  refine ⟨hpos,norm_pos_iff.mp (hmargin.trans_le hlow),hlow,?_⟩
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hmargin hlow

theorem finiteCorrection_ne_zero_thin {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {δ : ℝ} (hδ : δ≤1/4) {s : ℂ} (hs : 1-δ≤s.re) :
    finiteCorrection χ z s≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (thin_prime_factor χ (smallPrimes_prime hp) hδ hs).2.1

theorem finiteCorrection_logDeriv_thin {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {δ : ℝ} (hδ : δ≤1/4) {s : ℂ} (hs : 1-δ≤s.re) :
    logDeriv (finiteCorrection χ z) s =
      ∑ p ∈ smallPrimes z,
        (χ p*(p : ℂ)^(-s)*Complex.log (p : ℂ))/(1-χ p*(p : ℂ)^(-s)) := by
  have hfun : finiteCorrection χ z =
      ∏ p ∈ smallPrimes z,(fun w : ℂ => 1-χ p*(p : ℂ)^(-w)) := by
    funext w
    simp only [finiteCorrection,Finset.prod_apply]
  rw [hfun,logDeriv_prod
    (fun p hp => (thin_prime_factor χ (smallPrimes_prime hp) hδ hs).2.1)
    (fun p hp => (factor_hasDerivAt χ (smallPrimes_prime hp) s).differentiableAt)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logDeriv_apply,(factor_hasDerivAt χ (smallPrimes_prime hp) s).deriv]

theorem finiteCorrection_logDeriv_norm_thin {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ κ : ℝ} (hz : 0≤z) (hδ : 0≤δ) (hδ1 : δ≤1/4)
    (hκ : δ*Real.log (max 2 z)≤κ) {s : ℂ} (hs : 1-δ≤s.re) :
    ‖logDeriv (finiteCorrection χ z) s‖ ≤ thinLogCost κ z := by
  rw [finiteCorrection_logDeriv_thin χ z hδ1 hs]
  apply (norm_sum_le _ _).trans
  unfold thinLogCost logPrimeMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := smallPrimes_prime hp
  have hpR : 0<(p : ℝ) := by exact_mod_cast hprime.pos
  have hlog : 0≤Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
  have hnormlog : ‖Complex.log (p : ℂ)‖=Real.log (p : ℝ) := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_log (Nat.cast_nonneg p),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  rw [div_eq_mul_inv,norm_mul,norm_mul,hnormlog]
  calc
    _ ≤ (Real.exp κ/(p : ℝ)*Real.log (p : ℝ))*(1-primeRadius)⁻¹ :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (prime_twist_norm_le_exp_div χ hz hp hδ hκ hs) hlog)
        (thin_prime_factor χ hprime hδ1 hs).2.2.2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end ImbalancedChen.Part3.RoughThinEulerFactors20261026b
