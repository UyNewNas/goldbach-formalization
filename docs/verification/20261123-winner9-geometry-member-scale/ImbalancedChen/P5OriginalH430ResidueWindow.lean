import ImbalancedChen.P5OriginalH430CompleteScale

/-! The local proposition's complete moving-residue window, without
imposing the narrower sufficient support window of a dyadic producer. -/
namespace ImbalancedChen.P5OriginalH430ResidueWindow
noncomputable section
open Filter
open scoped Topology
open P5OriginalH430CompleteScale (eventually_complete_scale)

/-- The threshold precedes every allowed physical kappa and x. The
fixed 15/16 lower power is only an internal bound holding throughout
c0*x <= N <= x^(1+kappa). The actual upper exponent stays 1+kappa. -/
theorem eventually_residue_window {c0 z : ℝ} (hc : 0<c0) (hz : 0<z) (hz' : z≤1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ k x : ℝ, 0≤k → k≤1/100 → 0<x → c0*x≤(N:ℝ) → (N:ℝ)≤x^(1+k) →
      let y := min x (N:ℝ)
      let q := Real.logb y (N:ℝ)
      1<x ∧ x^(Real.logb x (N:ℝ))=(N:ℝ) ∧ 1<y ∧ y≤x ∧ y^q=(N:ℝ) ∧ 1≤q ∧ q≤1+k ∧
      x^(1/3-z/2)≤y^(1/3-(7*z/8)/2) := by
  filter_upwards [eventually_complete_scale (c:=1) (C:=1/c0) (z:=z) (k:=1) (k0:=1/16)
    zero_lt_one (by positivity) hz hz' zero_lt_one (by norm_num),eventually_ge_atTop (2:ℕ)] with N H hN
  intro k x hk hk' hx hcN hpow
  let y := min x (N:ℝ)
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hk1 : 0<1+k := by linarith
  have hx1 : 1<x := by
    by_contra! hh
    exact (not_lt_of_ge (hpow.trans (Real.rpow_le_one hx.le hh hk1.le))) hn
  have hlo : 1*(N:ℝ)^(1-1/16:ℝ)≤x := by
    rw [one_mul]
    calc
      (N:ℝ)^(1-1/16:ℝ) ≤ (x^(1+k))^(1-1/16:ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg N) hpow (by norm_num)
      _ = x^((1+k)*(1-1/16)) := (Real.rpow_mul hx.le _ _).symm
      _ ≤ x^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith only [hk'])
      _ = x := Real.rpow_one _
  have hhi : x≤(1/c0)*(N:ℝ) := by
    rw [div_mul_eq_mul_div,one_mul]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcN)
  obtain ⟨h1,_,_,hxx,hy,hyx,hyq,hql,_,hA⟩ := H x hlo hhi
  have hyN : (N:ℝ)≤y^(1+k) := by
    rcases le_total x (N:ℝ) with h | h
    · simpa only [y,min_eq_left h] using hpow
    · unfold y; rw [min_eq_right h]
      simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hn.le (show (1:ℝ)≤1+k by linarith))
  exact ⟨h1,hxx,hy,hyx,hyq,hql,(Real.logb_le_iff_le_rpow hy (zero_lt_one.trans hn)).mpr hyN,hA⟩

end
end ImbalancedChen.P5OriginalH430ResidueWindow
