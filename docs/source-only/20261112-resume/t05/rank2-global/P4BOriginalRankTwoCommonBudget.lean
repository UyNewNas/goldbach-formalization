import ImbalancedChen.P4BOriginalRankTwoPhysicalBlocks

/-! Select a single logarithmic grid and a single conductor accuracy.
All thresholds are taken before the physical parameters and both rows. -/
namespace ImbalancedChen.P4BOriginalRankTwoCommonBudget
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open P4BOriginalRankTwoChartScales (eventually_power)

def gridSize (B N : ℕ) := Nat.ceil ((Real.log (N:ℝ))^B)

/-- Two positive powers after all physical support losses. This only
uses product scale x=PV and the nonzero support of the physical source. -/
theorem eventually_geometry (B : ℕ) (x0 : ℝ) :
    ∀ᶠ N : ℕ in atTop,2≤N ∧ 1≤Real.log (N:ℝ) ∧
      4*(N:ℝ)^(9/10:ℝ)<N ∧ 0<gridSize B N ∧
      (Real.log (N:ℝ))^B≤(gridSize B N:ℝ) ∧
      (gridSize B N:ℝ)≤2*(Real.log (N:ℝ))^B ∧
      ∀ P V : ℕ,∀ x : ℝ,(N:ℝ)^(9/10:ℝ)≤x → x≤Real.exp 1*(N:ℝ) →
        (N:ℝ)^(19/96:ℝ)<2*(P:ℝ) → (N:ℝ)^(19/96:ℝ)<2*(V:ℝ) →
        x0≤x ∧ x^(1/10:ℝ)≤P ∧ x^(1/10:ℝ)≤V ∧ gridSize B N≤P ∧
        (N:ℝ)^(2/5:ℝ)≤x^(9/20:ℝ) ∧ Real.log (N:ℝ)/2≤Real.log x := by
  have hm := (tendsto_nat_log_pow_div_rpow B (by norm_num : 0<(1/8:ℝ))).eventually
    (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num))
  filter_upwards [eventually_ge_atTop (2:ℕ),eventually_one_le_nat_log,hm,
    eventually_power 4 (1/10:ℝ) (by norm_num),eventually_power (Real.exp 1) (1/10:ℝ) (by norm_num),
    eventually_power 2 (19/96-1/8:ℝ) (by norm_num),eventually_power x0 (9/10:ℝ) (by norm_num)]
    with N hN hL hmesh h4 he hgap hstart
  let L := Real.log (N:ℝ)
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hn0 := zero_lt_one.trans_le hn
  have hLB : 1≤L^B := one_le_pow₀ hL
  have hJlo : L^B≤(gridSize B N:ℝ) := Nat.le_ceil _
  have hJhi : (gridSize B N:ℝ)≤2*L^B := (Nat.ceil_lt_add_one (by positivity : 0≤L^B)).le.trans (by linarith)
  have hgrid : (gridSize B N:ℝ)≤(N:ℝ)^(1/8:ℝ) := by
    have z := (div_lt_iff₀ (Real.rpow_pos_of_pos hn0 (1/8))).mp hmesh
    change L^B < 1/2*(N:ℝ)^(1/8:ℝ) at z
    linarith
  have smooth (G : ℕ) (hG : (N:ℝ)^(19/96:ℝ)<2*(G:ℝ)) : (N:ℝ)^(1/8:ℝ)≤G := by
    have zz := mul_lt_mul_of_pos_left hgap (Real.rpow_pos_of_pos hn0 (1/8))
    rw [← Real.rpow_add hn0,show (1/8:ℝ)+(19/96-1/8)=19/96 by ring] at zz
    linarith
  have h4' := mul_lt_mul_of_pos_left h4 (Real.rpow_pos_of_pos hn0 (9/10))
  rw [← Real.rpow_add hn0,show (9/10:ℝ)+1/10=1 by norm_num,Real.rpow_one] at h4'
  refine ⟨hN,hL,by linarith,by
    have : (0:ℝ)<gridSize B N := zero_lt_one.trans_le (hLB.trans hJlo)
    exact_mod_cast this,hJlo,hJhi,?_⟩
  intro P V x hx hxhi hp hv
  have hxpos := (Real.rpow_pos_of_pos hn0 (9/10)).trans_le hx
  have hbig : x≤(N:ℝ)^(1+1/10:ℝ) := by
    rw [Real.rpow_add hn0,Real.rpow_one]
    exact hxhi.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right he.le hn0.le)
  have h10 := Real.rpow_le_rpow hxpos.le hbig (by norm_num : (0:ℝ)≤1/10)
  rw [←Real.rpow_mul hn0.le] at h10
  have h18 : x^(1/10:ℝ)≤(N:ℝ)^(1/8:ℝ) :=
    h10.trans (Real.rpow_le_rpow_of_exponent_le hn (by norm_num))
  have hq := Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hx (by norm_num : (0:ℝ)≤9/20)
  rw [←Real.rpow_mul hn0.le] at hq
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hn0 (9/10)) hx
  rw [Real.log_rpow hn0] at hlog
  exact ⟨hstart.le.trans hx,h18.trans (smooth P hp),h18.trans (smooth V hv),
    by exact_mod_cast hgrid.trans (smooth P hp),
    (Real.rpow_le_rpow_of_exponent_le hn (by norm_num)).trans hq,by linarith⟩

/-- A fixed slack of one power of log N pays all restoring constants
after the factor log N from the absolute reciprocal totient budget. -/
theorem eventually_block_cost (A : ℕ) (K delta : ℝ) (hK : 0<K) (hd : 0<delta) :
    let B := A+2
    let D := B+(A+1)
    ∀ᶠ N : ℕ in atTop,∀ x M : ℝ,0<x → x≤Real.exp 1*(N:ℝ) →
      Real.log (N:ℝ)/2≤Real.log x → 0≤M → M≤4*(1+Real.log (N:ℝ)) →
      (Real.log (N:ℝ))^B≤(gridSize B N:ℝ) → (gridSize B N:ℝ)≤2*(Real.log (N:ℝ))^B →
      2*(gridSize B N:ℝ)*(K*x/(Real.log x)^D)+20*M*x/(gridSize B N:ℝ)≤
        delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  dsimp only
  let B := A+2
  let D := B+(A+1)
  let C := 4*K*Real.exp 1*(2:ℝ)^D+160*Real.exp 1
  have ht := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (C/delta)
  filter_upwards [ht,eventually_one_le_nat_log,eventually_ge_atTop (2:ℕ)] with N hfee hl hN
  intro x M hx hxu hlog hM hMu hJlo hJhi
  let L := Real.log (N:ℝ)
  let J := (gridSize B N:ℝ)
  have hL : 0<L := zero_lt_one.trans_le hl
  have hJ : 0<J := (pow_pos hL B).trans_le hJlo
  have hxh : 0<L/2 := by positivity
  have hLX : 0<Real.log x := hxh.trans_le hlog
  have HD : L^D=L^B*L^(A+1) := pow_add _ _ _
  have HB : L^B=L^(A+1)*L := by change L^(A+1+1)=_; rw [pow_succ]
  have hfirst : 2*J*(K*x/(Real.log x)^D)≤4*K*Real.exp 1*(2:ℝ)^D*(N:ℝ)/L^(A+1) := by
    calc
      _ ≤ 2*(2*L^B)*(K*(Real.exp 1*(N:ℝ))/(L/2)^D) := by gcongr
      _ = _ := by
        rw [div_pow,HD]
        field_simp [ne_of_gt hL] <;> ring
  have hsecond : 20*M*x/J≤160*Real.exp 1*(N:ℝ)/L^(A+1) := by
    have hmajor : M≤8*L := hMu.trans (by dsimp only [L]; linarith)
    calc
      _ ≤ 20*(8*L)*(Real.exp 1*(N:ℝ))/L^B := by gcongr
      _ = _ := by
        rw [HB]
        field_simp [ne_of_gt hL] <;> ring
  have hC : C≤delta*L := by simpa only [mul_comm] using (div_le_iff₀ hd).mp hfee
  calc
    _ ≤ _ := add_le_add hfirst hsecond
    _ = C*(N:ℝ)/L^(A+1) := by dsimp only [C]; ring
    _ ≤ (delta*L)*(N:ℝ)/L^(A+1) := by gcongr
    _ = _ := by rw [pow_succ]; field_simp [ne_of_gt hL] <;> ring

end
end ImbalancedChen.P4BOriginalRankTwoCommonBudget
