import ImbalancedChen.Part3OriginalFullPositiveLevelSwitch

/-! Simplify the additive error in the complete six-window level recurrence.
The coefficient of each returned prefix energy is independent of all scales. -/
namespace ImbalancedChen.Part3.OriginalNativeSixWindowMean20261113
noncomputable section
open Finset
open scoped Classical BigOperators
open OriginalFullPositiveLevelSwitch20261113 (recurrence)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)
open OriginalSwitchedReturnedWindow20261113 (prefixMax)
open OriginalSwitchedActiveLevels20261113 (inScale outScale)
open OriginalSwitchedPhysicalWindows20261113 (returnScale)
open OriginalSwitchedPaidReturn20261113 (allowance)
open OriginalSwitchedRegularTracePrice20261113 (log_allowance)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)

private def Z : ℝ := 2+16*Real.pi

private theorem scales (j : ℕ) {Q Y : ℝ} (qp : 0<Q) (yp : 0<Y) :
    let M := classicalMScale j
    let P := Q+M+M*Y/Q
    (∀ l∈range 6,outScale j Y Q l≤Z*P) ∧
    (∀ l∈range 4,inScale Q l≤Z*P) := by
  let M := classicalMScale j
  let V := M*Y/Q
  let P := Q+M+V
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have vp : 0<V := div_pos (mul_pos mp yp) qp
  have pv : V≤P := by dsimp only [P];linarith only [qp,mp]
  have pq : Q≤P := by dsimp only [P];linarith only [mp,vp]
  have pp : 0≤P := qp.le.trans pq
  have z₂ : 2≤Z := by dsimp only [Z];linarith only [Real.pi_pos]
  constructor
  · intro l hl
    have n : l≤5 := by have h := mem_range.mp hl;omega
    have pow : (2:ℝ)^l≤32 := (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) n).trans_eq (by norm_num)
    have a : outScale j Y Q l=(2:ℝ)^l*(Real.pi*V)/2 := by dsimp only [outScale,returnScale,V,M];ring
    rw [a]
    calc
      _ ≤ 16*Real.pi*V := by nlinarith only [mul_le_mul_of_nonneg_right pow (mul_nonneg Real.pi_pos.le vp.le)]
      _ ≤ 16*Real.pi*P := mul_le_mul_of_nonneg_left pv (by positivity)
      _ ≤ Z*P := mul_le_mul_of_nonneg_right (by dsimp only [Z];linarith) pp
  · intro l hl
    have n : l≤3 := by have h := mem_range.mp hl;omega
    have pow : (2:ℝ)^l≤8 := (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) n).trans_eq (by norm_num)
    calc
      inScale Q l ≤ 2*Q := by dsimp only [inScale];nlinarith only [mul_le_mul_of_nonneg_right pow qp.le]
      _ ≤ 2*P := mul_le_mul_of_nonneg_left pq (by norm_num)
      _ ≤ Z*P := mul_le_mul_of_nonneg_right z₂ pp

/-- Whole exceptional spectrum on the original row, common additive phase,
six physical output dyads. The logarithmic allowance is fully additive. -/
theorem six_window_mean {ε : ℝ} (ep : 0<ε) :
    ∃ A D Y₀ : ℝ,0<A ∧ 0<D ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ (Q ω : ℝ),0<Q →
    ∀ (j a b : ℕ) (lo : 2^j≤a) (ab : a≤b),b≤2^(j+1) →
    let M := classicalMScale j
    intervalEnergy (classicalLevels Q) Y ω a b 0≤
      A*(∑ l∈range 6,prefixMax (classicalLevels (outScale j Y Q l)) Y ω a b ab)+
      D*((1+M)*(1+Y))^ε*(Q+M+M*Y/Q)*M := by
  let δ := ε/2
  have dp : 0<δ := half_pos ep
  obtain ⟨c,K,D,X,cp,kp,d0,x1,F⟩ := recurrence dp
  obtain ⟨L,lp,ell⟩ := log_allowance dp
  let W := Z+1
  have zp : 0<Z := by dsimp only [Z];positivity
  have wp : 0<W := by dsimp only [W];linarith
  let K₁ := (6*K+40*D*L)*W
  have k₁ : 0<K₁ := mul_pos (add_pos_of_pos_of_nonneg (mul_pos (by norm_num) kp) (by positivity)) wp
  refine ⟨K/c,K₁/c,X,div_pos kp cp,div_pos k₁ cp,x1,fun Y hy Q ω qp j a b lo ab hi => ?_⟩
  let M := classicalMScale j
  let U := (1+M)*(1+Y)
  let P := Q+M+M*Y/Q
  let V := W*P*M
  let I := inScale Q
  let O := outScale j Y Q
  let E (l : ℕ) := prefixMax (classicalLevels (O l)) Y ω a b ab
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have yp := zero_lt_one.trans_le (x1.trans hy)
  have z0 : 0≤M*Y/Q := div_nonneg (mul_nonneg mp.le yp.le) qp.le
  have pp : 0<P := by dsimp only [P];linarith only [qp,mp,z0]
  have pm : M≤P := by dsimp only [P];linarith only [qp,z0]
  have vv : 0≤V := mul_nonneg (mul_nonneg wp.le pp.le) mp.le
  have u1 : 1≤U := by dsimp only [U];nlinarith only [mp.le,yp.le,mul_nonneg mp.le yp.le]
  have uy : Y≤U := by dsimp only [U];nlinarith only [mp.le,mul_nonneg mp.le yp.le]
  have um : M≤U := by dsimp only [U];nlinarith only [yp.le,mul_nonneg mp.le yp.le]
  have s1 := Real.one_le_rpow u1 dp.le
  have sd := Real.rpow_nonneg (zero_le_one.trans u1) δ
  have ye : Y^δ≤U^δ := Real.rpow_le_rpow yp.le uy dp.le
  have se : U^δ≤U^ε := Real.rpow_le_rpow_of_exponent_le u1 (by dsimp only [δ];linarith only [ep])
  have dd : U^δ*U^δ=U^ε := by rw [←Real.rpow_add (zero_lt_one.trans_le u1),show δ+δ=ε by dsimp only [δ];ring]
  have LL : allowance Y≤L*U^δ := (ell Y (x1.trans hy)).trans (mul_le_mul_of_nonneg_left ye lp.le)
  have mm : M^(1+δ)≤P*U^δ := by
    rw [Real.rpow_add mp,Real.rpow_one]
    exact mul_le_mul pm (Real.rpow_le_rpow mp.le um dp.le) (Real.rpow_nonneg mp.le _) pp.le
  have caps := scales j qp yp
  have small (B : ℝ) (h : B≤Z*P) : Y^δ*(B+M)*M≤U^ε*V := by
    have cb : B+M≤W*P := by dsimp only [W];nlinarith only [h,pm]
    have a := mul_le_mul_of_nonneg_left cb (Real.rpow_nonneg yp.le δ)
    have b := mul_le_mul_of_nonneg_right (ye.trans se) (mul_nonneg wp.le pp.le)
    exact (mul_le_mul_of_nonneg_right (a.trans b) mp.le).trans_eq (by dsimp only [V];ring)
  have price (B : ℝ) (h : B≤Z*P) : (B+M^(1+δ))*M≤U^δ*V := by
    have grow := mul_le_mul_of_nonneg_left s1 (mul_nonneg zp.le pp.le)
    have cb : B+M^(1+δ)≤U^δ*(W*P) := by dsimp only [W];nlinarith only [h,grow,mm]
    exact (mul_le_mul_of_nonneg_right cb mp.le).trans_eq (by dsimp only [V];ring)
  have count (n : ℕ) (f : ℕ→ℝ) (p : ℝ) (h : ∀ l∈range n,f l≤p) :
      (∑ l∈range n,f l)≤(n:ℝ)*p := (sum_le_sum h).trans_eq (by simp only [sum_const,card_range,nsmul_eq_mul])
  have A := count 6 (fun l => Y^δ*(O l+M)*M) (U^ε*V) (fun l hl => small (O l) (caps.1 l hl))
  have B := count 6 (fun l => (O l+M^(1+δ))*M) (U^δ*V) (fun l hl => price (O l) (caps.1 l hl))
  have C := count 4 (fun l => (I l+M^(1+δ))*M) (U^δ*V) (fun l hl => price (I l) (caps.2 l hl))
  norm_num only [Nat.cast_ofNat] at A B C
  let T := (∑ l∈range 6,(O l+M^(1+δ))*M)+∑ l∈range 4,(I l+M^(1+δ))*M
  have t0 : 0≤T := by
    have op (l : ℕ) : 0≤O l := by change 0≤(2:ℝ)^l*(Real.pi*M*Y/Q)/2;positivity
    have ip (l : ℕ) : 0≤I l := by dsimp only [I,inScale];positivity
    exact add_nonneg (sum_nonneg fun l _ => mul_nonneg (add_nonneg (op l) (Real.rpow_nonneg mp.le _)) mp.le)
      (sum_nonneg fun l _ => mul_nonneg (add_nonneg (ip l) (Real.rpow_nonneg mp.le _)) mp.le)
  have upper : T≤10*(U^δ*V) := by dsimp only [T];linarith only [B,C]
  have log : allowance Y*T≤10*L*(U^ε*V) :=
    (mul_le_mul LL upper t0 (mul_nonneg lp.le sd)).trans_eq (by rw [←dd];ring)
  have src := F Y hy Q ω qp j a b lo ab hi
  change c*intervalEnergy (classicalLevels Q) Y ω a b 0≤K*(∑ l∈range 6,E l+Y^δ*(O l+M)*M)+4*(D*allowance Y*T) at src
  rw [sum_add_distrib] at src
  have cost := mul_le_mul_of_nonneg_left A kp.le
  have fees := mul_le_mul_of_nonneg_left log d0
  change _≤(K/c)*(∑ l∈range 6,E l)+(K₁/c)*U^ε*P*M
  calc
    _ ≤ (K*(∑ l∈range 6,E l)+K₁*U^ε*P*M)/c := by
      apply (le_div_iff₀ cp).mpr
      dsimp only [K₁,V] at cost fees ⊢
      nlinarith only [src,cost,fees]
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalNativeSixWindowMean20261113

