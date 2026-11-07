import ImbalancedChen.P5RoughSquareWeightedBudget
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One threshold, before every physical cap and test mass, absorbs the exact
complete-product collision logarithms. The proved primary logarithm/power
limit is reused. A positive-power presieve retains its FULL saving:
the cost is (Q+T)*N^(zeta-omega), for every zeta>0, not a beta l1 bound.
-/
namespace ImbalancedChen.P5Z.RoughSquarePowerPayment
noncomputable section
open Filter Topology
open RoughSquareWeightedBudget

/-- Uniform in ALL smaller physical caps, including Q=0. -/
theorem eventually_logBudget_cap_payment (theta zeta : ℝ)
    (htheta : 0 ≤ theta) (hzeta : 0 < zeta) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ ∀ Q : ℕ, (Q : ℝ) ≤ (N : ℝ)^theta →
      logBudget Q*(1+2*logBudget Q) ≤ (N : ℝ)^zeta := by
  let C : ℝ := 3*(1+theta)^2
  have hdecay : Tendsto (fun N : ℕ => C*((Real.log (N : ℝ))^2/(N : ℝ)^zeta))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_nat_log_pow_div_rpow 2 hzeta).const_mul C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      C*((Real.log (N : ℝ))^2/(N : ℝ)^zeta) < 1 :=
    hdecay.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hloglarge : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hsmall,hloglarge,eventually_ge_atTop (2 : ℕ)] with N hs hlog hN
  refine ⟨hN,?_⟩
  intro Q hQ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hNpow : (0 : ℝ) < (N : ℝ)^zeta := Real.rpow_pos_of_pos hNp _
  have hcap : max 1 (Q : ℝ) ≤ (N : ℝ)^theta :=
    max_le (Real.one_le_rpow hN1 htheta) hQ
  have hlogcap := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Q : ℝ))) hcap
  rw [Real.log_rpow hNp] at hlogcap
  have hH1 : 1 ≤ logBudget Q := by
    dsimp [logBudget]
    linarith [Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))]
  have hH : logBudget Q ≤ (1+theta)*Real.log (N : ℝ) := by
    dsimp [logBudget]
    nlinarith
  have hright : 0 ≤ (1+theta)*Real.log (N : ℝ) := by positivity
  have hsquare : (logBudget Q)^2 ≤ ((1+theta)*Real.log (N : ℝ))^2 := by
    simpa only [pow_two] using mul_le_mul hH hH (by linarith : 0 ≤ logBudget Q) hright
  have hp : C*(Real.log (N : ℝ))^2 ≤ (N : ℝ)^zeta := by
    have hs' : (C*(Real.log (N : ℝ))^2)/(N : ℝ)^zeta < 1 := by
      simpa only [mul_div_assoc] using hs
    exact ((div_lt_iff₀ hNpow).mp hs').le.trans_eq (one_mul _)
  calc
    _ ≤ 3*(logBudget Q)^2 := by nlinarith
    _ ≤ 3*((1+theta)*Real.log (N : ℝ))^2 := mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ = C*(Real.log (N : ℝ))^2 := by dsimp [C]; ring
    _ ≤ _ := hp

/-- Exact fixed-power payment with the actual positive presieve exponent.
No estimate for a prime product, beta cardinality or beta mass is input. -/
theorem eventually_presieve_kernel_power_payment (theta omega zeta : ℝ)
    (htheta : 0 ≤ theta) (homega : 0 < omega) (hzeta : 0 < zeta) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ ∀ (Q : ℕ) (T : ℝ),
      (Q : ℝ) ≤ (N : ℝ)^theta → 0 ≤ T →
      ((Q : ℝ)+T*logBudget Q*(1+2*logBudget Q))/((N : ℝ)^omega-1) ≤
        2*((Q : ℝ)+T)*(N : ℝ)^(zeta-omega) := by
  have hpresieve : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ)^omega :=
    ((tendsto_rpow_atTop homega).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_logBudget_cap_payment theta zeta htheta hzeta,hpresieve] with N hpay hw
  refine ⟨hpay.1,?_⟩
  intro Q T hQ hT
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hpowp : 0 < (N : ℝ)^omega := Real.rpow_pos_of_pos hNp _
  have hz1 : 1 ≤ (N : ℝ)^zeta := Real.one_le_rpow hN1 hzeta.le
  have hnum : 0 ≤ (Q : ℝ)+T*logBudget Q*(1+2*logBudget Q) := by
    have hH := logBudget_nonneg Q
    positivity
  have hn : (Q : ℝ)+T*logBudget Q*(1+2*logBudget Q) ≤
      ((Q : ℝ)+T)*(N : ℝ)^zeta := by
    have hQpow : (Q : ℝ) ≤ (Q : ℝ)*(N : ℝ)^zeta :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hz1
    have hTpay := mul_le_mul_of_nonneg_left (hpay.2 Q hQ) hT
    nlinarith
  calc
    _ ≤ ((Q : ℝ)+T*logBudget Q*(1+2*logBudget Q))/((N : ℝ)^omega/2) :=
      div_le_div_of_nonneg_left hnum (by positivity) (by linarith)
    _ = 2*((Q : ℝ)+T*logBudget Q*(1+2*logBudget Q))/(N : ℝ)^omega := by ring
    _ ≤ 2*(((Q : ℝ)+T)*(N : ℝ)^zeta)/(N : ℝ)^omega :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hpowp.le
    _ = _ := by rw [Real.rpow_sub hNp]; ring

end
end ImbalancedChen.P5Z.RoughSquarePowerPayment
