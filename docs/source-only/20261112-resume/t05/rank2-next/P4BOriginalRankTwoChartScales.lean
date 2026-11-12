import ImbalancedChen.P4BOriginalTwoAtlasSmallPayment

/-! One original pair of dyadic labels, with both prime scales growing.
The gates are tested on the literal physical product. -/
namespace ImbalancedChen.P4BOriginalRankTwoChartScales
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.ExactOriginalSmoothDyadicPartition (R chartBank words_mem cutoffIndex)
open P5Z.ActualEtaPsiOccurrenceBudget (psi eta psi_eq_eta_difference eta_zero eta_one eta_bounds)

def index (N : ℕ) := Nat.log2 N / 2 - 5
def labels (N : ℕ) := [index N,index N+3]
def U (N : ℕ) := R (index N)

theorem second_scale (N : ℕ) : R (index N+3)=8*U N := by
  simp only [U,R,pow_add]
  ring

theorem scales {N : ℕ} (hN : 2^12≤N) :
    labels N∈chartBank N 2 ∧ 1024*(U N)^2≤(N:ℝ) ∧ (N:ℝ)<4096*(U N)^2 := by
  have hn : N≠0 := by omega
  have hlog : 12≤Nat.log2 N := (Nat.le_log2 hn).mpr hN
  have hlo : 2*(index N)+10≤Nat.log2 N := by unfold index; omega
  have hhi : Nat.log2 N<2*(index N)+12 := by unfold index; omega
  have h₁ := (Nat.le_log2 hn).mp hlo
  have h₂ : N<2^(2*(index N)+12) := by
    by_contra! bad
    exact (not_le_of_gt hhi) ((Nat.le_log2 hn).mpr bad)
  have powid (t : ℕ) :
      (2:ℝ)^(2*index N+t)=(U N)^2*(2:ℝ)^t := by
    simp only [Nat.mul_comm 2 (index N),pow_add,pow_mul,U,R]
  have h₁' : (2:ℝ)^(2*index N+10)≤N := by exact_mod_cast h₁
  have h₂' : (N:ℝ)<(2:ℝ)^(2*index N+12) := by exact_mod_cast h₂
  rw [powid] at h₁' h₂'
  constructor
  · apply words_mem _ _ _ rfl
    intro j hj
    simp [labels] at hj
    apply Finset.mem_range.mpr
    rcases hj with rfl|rfl <;> simp only [index,cutoffIndex] <;> omega
  · constructor <;> norm_num at h₁' h₂' ⊢ <;> linarith

theorem U_pos (N : ℕ) : 0<U N := P5Z.ExactOriginalSmoothDyadicPartition.R_pos _

theorem psi_size (t : ℝ) : |psi t|≤1 := by
  rw [psi_eq_eta_difference,abs_le]
  have h1 := eta_bounds t
  have h2 := eta_bounds (2*t)
  constructor <;> linarith

theorem psi_window {t V : ℝ} (hV : 0<V) (h : psi (t/V)≠0) :
    V/2<t ∧ t<2*V := by
  rw [psi_eq_eta_difference] at h
  constructor
  · by_contra! hh
    have h1 : t/V≤1/2 := (div_le_iff₀ hV).mpr (by linarith)
    exact h (by rw [eta_zero (by linarith : 2*(t/V)≤1),eta_zero (by linarith : t/V≤1),sub_self])
  · by_contra! hh
    have h1 : 2≤t/V := (le_div_iff₀ hV).mpr hh
    exact h (by rw [eta_one (by linarith : 2≤2*(t/V)),eta_one h1,sub_self])

theorem eventually_power (c t : ℝ) (ht : 0<t) : ∀ᶠ N : ℕ in atTop,c<(N:ℝ)^t :=
  ((Real.tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop c

theorem eventually_plateau {b kappa kappa0 : ℝ} (hb : 0<b) (hb1 : b<1)
    (hk : 0<kappa) (hk0 : 0<kappa0) :
    ∀ᶠ N : ℕ in atTop,∀ p j : ℕ,psi ((p:ℝ)/U N)≠0 → psi ((j:ℝ)/(8*U N))≠0 →
      p≤j ∧ (j:ℝ)^b<(p:ℝ) ∧ manuscriptHalfProductCutoff kappa N≤((p*j:ℕ):ℝ) ∧
        p*j≤N ∧ eta (((p*j:ℕ):ℝ)/(N:ℝ)^(1-kappa0))=1 := by
  filter_upwards [eventually_ge_atTop (2^12:ℕ),eventually_power 128 ((1-b)/2) (by linarith),
    eventually_power 4096 kappa hk,eventually_power 4096 kappa0 hk0] with N hN hbad hcut htrim
  intro p j hp hj
  obtain ⟨_,hl,hh⟩ := scales hN
  have hU := U_pos N
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  obtain ⟨hpl,hpu⟩ := psi_window hU hp
  obtain ⟨hjl,hju⟩ := psi_window (by positivity : 0<8*U N) hj
  have hs := Real.sq_sqrt hNr.le
  have hsq := Real.sqrt_nonneg (N:ℝ)
  have hs1 : Real.sqrt (N:ℝ)<64*U N := by
    by_contra! bad
    have h := mul_self_le_mul_self (by positivity : 0≤64*U N) bad
    nlinarith only [h,hs,hh]
  have hs2 : 16*U N≤Real.sqrt (N:ℝ) := by
    by_contra! bad
    have h := mul_self_lt_mul_self hsq bad
    nlinarith only [h,hs,hl,sq_nonneg (U N)]
  have hprodLo : (N:ℝ)/2048<(p:ℝ)*(j:ℝ) := by
    have H := mul_lt_mul_of_pos_right hpl (show 0<(j:ℝ) by linarith)
    have J := mul_lt_mul_of_pos_left hjl (show 0<U N/2 by linarith)
    nlinarith only [hh,H,J]
  have hprodHi : (p:ℝ)*(j:ℝ)≤N := by
    have H := mul_le_mul hpu.le hju.le (Nat.cast_nonneg j) (by positivity)
    nlinarith only [H,hl]
  have cut (t : ℝ) (hc : 4096<(N:ℝ)^t) : 2*(N:ℝ)^(1-t)≤(p:ℝ)*(j:ℝ) := by
    have hx : (N:ℝ)^(1-t)*(N:ℝ)^t=(N:ℝ) := by
      rw [← Real.rpow_add hNr,show 1-t+t=1 by ring,Real.rpow_one]
    have H := mul_lt_mul_of_pos_left hc (Real.rpow_pos_of_pos hNr (1-t))
    nlinarith only [H,hx,hprodLo]
  have hpow : (N:ℝ)^(b/2)*(N:ℝ)^((1-b)/2)=Real.sqrt (N:ℝ) := by
    rw [← Real.rpow_add hNr,show b/2+(1-b)/2=1/2 by ring,← Real.sqrt_eq_rpow]
  have hjpow : (j:ℝ)^b≤(N:ℝ)^(b/2) := by
    calc
      _ ≤ (Real.sqrt (N:ℝ))^b := Real.rpow_le_rpow (Nat.cast_nonneg j) (by linarith) hb.le
      _ = _ := by rw [Real.sqrt_eq_rpow,← Real.rpow_mul hNr.le]; congr 1; ring
  have H := mul_lt_mul_of_pos_left hbad (Real.rpow_pos_of_pos hNr (b/2))
  refine ⟨by exact_mod_cast (show (p:ℝ)≤j by linarith),by nlinarith only [H,hpow,hjpow,hs1,hpl],
    by simpa only [manuscriptHalfProductCutoff,Nat.cast_mul] using cut kappa hcut,
    by exact_mod_cast hprodHi,?_⟩
  apply eta_one
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hNr _)).mpr
  simpa only [Nat.cast_mul] using cut kappa0 htrim

end
end ImbalancedChen.P4BOriginalRankTwoChartScales
