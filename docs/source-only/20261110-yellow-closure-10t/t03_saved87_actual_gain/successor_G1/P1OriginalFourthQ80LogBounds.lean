import ImbalancedChen.P2HistoricLogPointInterpreter

/-! The integer logarithm brackets of certify_fourth_prefix_stronger.py.
One floor for each of the 24 summands; divisor 49 in the upper tail. -/
namespace ImbalancedChen.P1OriginalFourthQ80LogBounds
open scoped BigOperators
open Certificates.P2HistoricLogPointInterpreter (oddSum sharp_odd_log_upper)

def scale : ℕ := 2^80
def z (j : ℕ) : ℚ := (j:ℚ)/(8192+j)
def term (j k : ℕ) : ℚ := (scale:ℚ)*2*(z j)^(2*k+1)/((2*k+1:ℕ):ℚ)
def tail (j : ℕ) : ℚ := (scale:ℚ)*2*(z j)^49/(49*(1-(z j)^2))
def lo (j : ℕ) : ℤ := ∑ k ∈ Finset.range 24, ⌊term j k⌋
def hi (j : ℕ) : ℤ := if j = 0 then 0 else lo j + 24 + ⌈tail j⌉
def leftStep (j : ℕ) : ℤ := ⌊(lo j:ℚ)/(8192+j)⌋
def ratio (j : ℕ) : ℚ := (12288+(j:ℚ))/(8192+j)
def penalty (j : ℕ) : ℤ := ⌈ratio j*(hi j:ℚ)⌉

theorem scale_pos : 0 < (scale:ℝ) := by norm_num [scale]
theorem floor_cast_le (a : ℚ) : ((⌊a⌋:ℤ):ℝ) ≤ (a:ℝ) := by exact_mod_cast Int.floor_le a
theorem le_floor_cast_add_one (a : ℚ) : (a:ℝ) ≤ ((⌊a⌋:ℤ):ℝ) + 1 := by
  exact_mod_cast (Int.lt_floor_add_one a).le
theorem le_ceil_cast (a : ℚ) : (a:ℝ) ≤ ((⌈a⌉:ℤ):ℝ) := by exact_mod_cast Int.le_ceil a

theorem z_bounds (j : ℕ) : 0 ≤ (z j:ℝ) ∧ (z j:ℝ) < 1 := by
  have hp : (0:ℚ)<8192+j := by positivity
  have hh : z j < 1 := (div_lt_one hp).2 (by linarith)
  have hl : 0 ≤ z j := div_nonneg (Nat.cast_nonneg _) hp.le
  exact ⟨by exact_mod_cast hl,by exact_mod_cast hh⟩

theorem z_identity (j : ℕ) : (1+(z j:ℝ))/(1-(z j:ℝ)) = 1+(j:ℝ)/4096 := by
  have hz : (1:ℝ)-(z j:ℝ) ≠ 0 := (sub_pos.mpr (z_bounds j).2).ne'
  apply (div_eq_iff hz).2
  simp [z]
  field_simp [show 8192+(j:ℝ) ≠ 0 by positivity] <;> ring

private theorem term_sum (j : ℕ) :
    (∑ k ∈ Finset.range 24, (term j k:ℝ)) = (scale:ℝ) * (2*oddSum (z j:ℝ) 24) := by
  rw [oddSum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [term,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow]
  ring

theorem log_interval (j : ℕ) :
    (lo j:ℝ) ≤ (scale:ℝ)*Real.log (1+(j:ℝ)/4096) ∧
    (scale:ℝ)*Real.log (1+(j:ℝ)/4096) ≤ (hi j:ℝ) := by
  by_cases hj : j = 0
  · subst j
    simp [lo,hi,term,z]
  have hz := z_bounds j
  have hlow := Real.sum_range_le_log_div hz.1 hz.2 24
  change oddSum (z j:ℝ) 24 ≤ (1/2)*Real.log ((1+(z j:ℝ))/(1-(z j:ℝ))) at hlow
  have hupp := sharp_odd_log_upper hz.1 hz.2 24
  rw [z_identity] at hlow hupp
  have hpoly : 2*oddSum (z j:ℝ) 24 ≤ Real.log (1+(j:ℝ)/4096) := by linarith only [hlow]
  have hL : (lo j:ℝ) ≤ ∑ k ∈ Finset.range 24, (term j k:ℝ) := by
    unfold lo
    push_cast
    exact Finset.sum_le_sum (fun k _ => floor_cast_le (term j k))
  have hU : (∑ k ∈ Finset.range 24, (term j k:ℝ)) ≤ (lo j:ℝ)+24 := calc
    _ ≤ ∑ k ∈ Finset.range 24, (((⌊term j k⌋:ℤ):ℝ)+1) :=
      Finset.sum_le_sum (fun k _ => le_floor_cast_add_one (term j k))
    _ = _ := by simp [lo,Finset.sum_add_distrib]
  rw [term_sum] at hL hU
  have htail : (tail j:ℝ) = (scale:ℝ)*(2*(z j:ℝ)^49/(49*(1-(z j:ℝ)^2))) := by
    simp only [tail,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow,
      Rat.cast_sub,Rat.cast_one]
    ring
  have ht := le_ceil_cast (tail j)
  rw [htail] at ht
  have hscaled := mul_le_mul_of_nonneg_left hupp scale_pos.le
  norm_num only [Nat.reduceAdd,Nat.reduceMul,Nat.cast_ofNat] at hscaled
  rw [mul_add] at hscaled
  refine ⟨hL.trans (mul_le_mul_of_nonneg_left hpoly scale_pos.le),?_⟩
  simp only [hi,if_neg hj,Int.cast_add,Int.cast_ofNat]
  linarith only [hscaled,hU,ht]

theorem step_le (j : ℕ) : (leftStep j:ℝ) ≤ (lo j:ℝ)/(8192+(j:ℝ)) := by
  simpa only [leftStep,Rat.cast_div,Rat.cast_intCast,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat]
    using floor_cast_le ((lo j:ℚ)/(8192+j))

theorem ratio_upper (j : ℕ) :
    (ratio j:ℝ)*((scale:ℝ)*Real.log (1+(j:ℝ)/4096)) ≤ (penalty j:ℝ) := by
  have hr : (0:ℚ) ≤ ratio j := by unfold ratio; positivity
  have h' := mul_le_mul_of_nonneg_left (log_interval j).2 (show (0:ℝ) ≤ (ratio j:ℝ) by exact_mod_cast hr)
  exact h'.trans (by simpa only [penalty,Rat.cast_mul,Rat.cast_intCast] using le_ceil_cast (ratio j*(hi j:ℚ)))

end ImbalancedChen.P1OriginalFourthQ80LogBounds
