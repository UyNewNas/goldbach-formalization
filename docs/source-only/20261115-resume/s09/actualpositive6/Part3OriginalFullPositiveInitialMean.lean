import ImbalancedChen.Part3OriginalFullPositiveLevelSwitch
import ImbalancedChen.Part3OriginalSwitchedIntervalUnit

/-! The initial mean for the complete positive native row for all Y>0.
Only the proved 3/4 support of that row enters the bounded-height part. -/
namespace ImbalancedChen.Part3.OriginalFullPositiveInitialMean20261113
noncomputable section
open Finset Complex
open scoped Classical BigOperators
open OriginalFullPositiveLevelSwitch20261113 (rho_zero)
open private row_zero from ImbalancedChen.Part3OriginalFullPositiveLevelSwitch
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)
open OriginalSwitchedIntervalUnit20261113 (short_unit)
open OriginalSwitchedMellinRows20261113 (twistedRow nativeRow)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau classicalLevels mem_exceptional)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ActualPositiveNativeDiagonal20261112 (complementaryHeight complementary_range)
open OriginalSwitchedPaidReturn20261113 (allowance)
open OriginalSwitchedRegularTracePrice20261113 (log_allowance)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

/-- Interpolate only positive native rows, and only to their established
3/4 order. This also holds after the Mellin twist. -/
theorem transport (L : Finset ℕ+) {X Y : ℝ} (xp : 0<X) (yp : 0<Y) (ω : ℝ)
    {a : ℕ} (ap : 0<a) (b : ℕ) (t : ℝ) :
    intervalEnergy L Y ω a b t≤(max 1 (Y/X))^(3/4:ℝ)*intervalEnergy L X ω a b t := by
  simp only [intervalEnergy,Finset.mul_sum]
  apply sum_le_sum
  intro q _
  apply sum_le_sum
  intro i _
  by_cases high : 3/4<tau q i.val
  · simp only [row_zero q i high ap b ω t,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero]
  have pos : 0≤tau q i.val := by
    change 0≤2*complementaryHeight q.val i.val
    exact mul_nonneg (by norm_num) (complementary_range q.val ((mem_exceptional q i.val).mp i.property).2).1.le
  have le := Real.rpow_le_rpow (div_nonneg yp.le xp.le) (le_max_right 1 (Y/X)) pos
  have hi := Real.rpow_le_rpow_of_exponent_le (le_max_left 1 (Y/X)) (le_of_not_gt high)
  have yx := Real.div_rpow yp.le xp.le (tau q i.val)
  have pass := (div_le_iff₀ (Real.rpow_pos_of_pos xp _)).mp (yx.symm.le.trans (le.trans hi))
  exact (mul_le_mul_of_nonneg_right pass (sq_nonneg _)).trans_eq (by ring)

theorem initial_mean {ε : ℝ} (ep : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (j a b : ℕ) (lo : 2^j≤a),a≤b → b≤2^(j+1) →
    ∀ (Q Y ω : ℝ),0<Q → 0<Y →
    let M := classicalMScale j
    intervalEnergy (classicalLevels Q) Y ω a b 0≤C*((1+M)*(1+Y))^ε*(Q+M+Y)*M := by
  let δ := ε/2
  have dep : 0<δ := half_pos ep
  obtain ⟨c,K,Y₀,cp,kp,y1,init⟩ := OriginalFullPositiveLevelSwitch20261113.initial dep
  obtain ⟨P,pp,ell⟩ := log_allowance dep
  let C₀ := (Y₀^(3/4:ℝ))*(32*sieveConstant)
  let C₁ := (K*(1+2*P))/c
  have c0 : 0<C₀ := mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le y1) _)
    (mul_pos (by norm_num) sieveConstant_pos)
  have c1 : 0<C₁ := div_pos (mul_pos kp (by linarith only [pp])) cp
  refine ⟨max C₀ C₁,c0.trans_le (le_max_left _ _),fun j a b lo ab hi Q Y ω qp yp => ?_⟩
  let M := classicalMScale j
  let U := (1+M)*(1+Y)
  let V := (Q+M+Y)*M
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have u1 : 1≤U := by dsimp [U];nlinarith only [mp.le,yp.le,mul_nonneg mp.le yp.le]
  have vp : 0≤V := mul_nonneg (by linarith only [qp,mp,yp]) mp.le
  have one := Real.one_le_rpow u1 ep.le
  have scale {A : ℝ} (h : A≤max C₀ C₁) : A*(U^ε*V)≤(max C₀ C₁)*U^ε*(Q+M+Y)*M :=
    (mul_le_mul_of_nonneg_right h (mul_nonneg (zero_le_one.trans one) vp)).trans_eq (by dsimp only [V];ring)
  by_cases hy : Y₀≤Y
  · let s := (1+M)^δ
    let t := (1+Y)^δ
    have s1 : 1≤s := Real.one_le_rpow (by linarith only [mp]) dep.le
    have t1 : 1≤t := Real.one_le_rpow (by linarith only [yp]) dep.le
    have pow : s*t=U^δ := (Real.mul_rpow (by linarith only [mp] : 0≤1+M) (by linarith only [yp] : 0≤1+Y)).symm
    have small := Real.rpow_le_rpow_of_exponent_le u1 (by dsimp [δ];linarith only [ep] : δ≤ε)
    have mh : M^(1+δ)≤M*s := by
      rw [Real.rpow_add mp,Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow mp.le (by linarith) dep.le) mp.le
    have qh := mul_le_mul_of_nonneg_left s1 qp.le
    have z : (Q+M^(1+δ))*M≤s*V := by
      dsimp only [V]
      nlinarith only [mul_le_mul_of_nonneg_right mh mp.le,mul_le_mul_of_nonneg_right qh mp.le,
        mul_nonneg (mul_nonneg (zero_le_one.trans s1) yp.le) mp.le]
    have log := (ell Y (y1.trans hy)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow yp.le (by linarith : Y≤1+Y) dep.le) pp.le)
    have addCost : allowance Y*(Q+M^(1+δ))*M≤P*U^ε*V := by
      have h := mul_le_mul log z (mul_nonneg (add_nonneg qp.le (Real.rpow_nonneg mp.le _)) mp.le)
        (mul_nonneg pp.le (zero_le_one.trans t1))
      calc
        _ ≤ (P*t)*(s*V) := (by simpa only [allowance,mul_assoc] using h)
        _ = P*(s*t)*V := by ring
        _ ≤ _ := by rw [pow];exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left small pp.le) vp
    have first : U^δ*(M+Y)*M≤U^ε*V := by
      have p := mul_le_mul small (by linarith only [qp] : M+Y≤Q+M+Y)
        (add_nonneg mp.le yp.le) (Real.rpow_nonneg (zero_le_one.trans u1) _)
      exact (mul_le_mul_of_nonneg_right p mp.le).trans_eq (by dsimp only [V];ring)
    have lhs := init j a b lo ab hi Y Q ω hy qp
    apply le_trans _ (scale (le_max_right _ _))
    have core := mul_le_mul_of_nonneg_left (add_le_add first addCost) kp.le
    change c*intervalEnergy (classicalLevels Q) Y ω a b 0≤
      K*(U^δ*(M+Y)*M+allowance Y*(Q+M^(1+δ))*M) at lhs
    have val : intervalEnergy (classicalLevels Q) Y ω a b 0≤(K*(1+2*P)*(U^ε*V))/c := by
      apply (le_div_iff₀ cp).mpr
      nlinarith only [lhs,core,mul_nonneg (mul_nonneg (mul_nonneg kp.le pp.le) (zero_le_one.trans one)) vp]
    exact val.trans_eq (by dsimp only [C₁];ring)
  · have high := transport (classicalLevels Q) zero_lt_one yp ω ap b 0
    rw [div_one] at high
    have move := Real.rpow_le_rpow (zero_le_one.trans (le_max_left 1 Y)) (max_le y1 (le_of_not_ge hy)) (by norm_num : (0:ℝ)≤3/4)
    have uni := short_unit qp j a b lo hi ω 0
    have un : 0≤intervalEnergy (classicalLevels Q) 1 ω a b 0 := by
      unfold intervalEnergy;exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (Real.rpow_nonneg zero_le_one _) (sq_nonneg _)
    have g := mul_le_mul move uni un (Real.rpow_nonneg (zero_le_one.trans y1) _)
    apply high.trans (g.trans ?_)
    apply le_trans _ (scale (le_max_left _ _))
    have mono : V≤U^ε*V := by simpa only [one_mul] using mul_le_mul_of_nonneg_right one vp
    have t : (Q+M)*M≤U^ε*V := (mul_le_mul_of_nonneg_right (by linarith only [yp] : Q+M≤Q+M+Y) mp.le).trans mono
    exact (show Y₀^(3/4:ℝ)*(32*sieveConstant*(Q+M)*M)=C₀*((Q+M)*M) by dsimp only [C₀];ring).le.trans
      (mul_le_mul_of_nonneg_left t c0.le)

end
end ImbalancedChen.Part3.OriginalFullPositiveInitialMean20261113
