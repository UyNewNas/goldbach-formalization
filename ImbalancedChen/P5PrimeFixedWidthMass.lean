import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform prime harmonic mass on the preassigned multiplicative window
(x, 64x]. The centre of the window may be chosen after the threshold. -/
namespace ImbalancedChen.P5PrimeFixedWidthMass

noncomputable section
open Filter Topology
open scoped BigOperators

def window (x : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊64*x⌋₊ \ Nat.primesLE ⌊x⌋₊

theorem mem_window {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ window x ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 64*x := by
  simp only [window, Finset.mem_sdiff, Nat.mem_primesLE, Nat.le_floor_iff (by positivity : 0 ≤ 64*x),
    Nat.le_floor_iff hx]
  constructor
  · rintro ⟨⟨hhi, hp⟩, hlo⟩
    exact ⟨hp, lt_of_not_ge (fun h => hlo ⟨h, hp⟩), hhi⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact ⟨⟨hhi, hp⟩, fun h => (not_le_of_gt hlo) h.1⟩

theorem eventually_window_mass :
    ∀ᶠ x : ℝ in atTop, 1/(64*Real.log x) ≤ ∑ p ∈ window x, 1/(p : ℝ) := by
  have hupper := Chebyshev.eventually_primeCounting_le (ε := 1) zero_lt_one
  filter_upwards [hupper, eventually_ge_atTop (128 : ℝ)] with x hupper hx
  have hx0 : 0 < x := by linarith
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  have h64log : 0 < Real.log (64*x) := Real.log_pos (by linarith)
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by
    convert Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hlog4 : Real.log 4 ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlog64 : Real.log (64*x) ≤ 2*Real.log x := by
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 64) (by linarith : 64 ≤ x)]
  have hlogshift : Real.log (64*x+2) ≤ 2*x := by
    calc
      _ ≤ Real.log (128*x) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 128 + Real.log x := Real.log_mul (by norm_num) hx0.ne'
      _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 128),
        Real.log_le_sub_one_of_pos hx0]
  have hnum : 28*x ≤ (64*x-1)*Real.log 2 - Real.log (64*x+2) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 (by linarith : 0 ≤ 64*x-1)]
  have hpi := Chebyshev.pi_ge' (x := 64*x) (by linarith)
  have hlow : 14*x/Real.log x ≤ (Nat.primeCounting ⌊64*x⌋₊ : ℝ) := by
    refine le_trans ?_ hpi
    apply (div_le_div_iff₀ hxlog h64log).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog64 (by linarith : 0 ≤ 14*x),
      mul_le_mul_of_nonneg_right hnum hxlog.le]
  have hhi : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 4*x/Real.log x :=
    hupper.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Real.log 4 + 1 ≤ 4) hx0.le) hxlog.le)
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊64*x⌋₊ := by
    intro q hq
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hq).1.trans (Nat.floor_mono (by linarith)),
      (Nat.mem_primesLE.mp hq).2⟩
  have hcard : (window x).card + Nat.primeCounting ⌊x⌋₊ = Nat.primeCounting ⌊64*x⌋₊ := by
    simpa only [window, Nat.primesLE_card_eq_primeCounting] using Finset.card_sdiff_add_card_eq_card hsub
  have hreal := congrArg (fun z : ℕ => (z : ℝ)) hcard
  push_cast at hreal
  have hcount : x/Real.log x ≤ ((window x).card : ℝ) := by
    linarith [show 0 ≤ x/Real.log x by positivity,
      show 14*x/Real.log x = 14*(x/Real.log x) by ring,
      show 4*x/Real.log x = 4*(x/Real.log x) by ring]
  calc
    _ = (x/Real.log x) * (1/(64*x)) := by field_simp [hx0.ne', hxlog.ne'] <;> ring
    _ ≤ ((window x).card : ℝ) * (1/(64*x)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = ∑ _p ∈ window x, 1/(64*x) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, _, hph⟩ := (mem_window hx0.le).mp hp
      exact one_div_le_one_div_of_le (by exact_mod_cast hpp.pos) hph

end
end ImbalancedChen.P5PrimeFixedWidthMass
