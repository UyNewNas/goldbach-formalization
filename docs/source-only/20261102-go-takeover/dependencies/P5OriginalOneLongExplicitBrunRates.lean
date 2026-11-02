import ImbalancedChen.P5OriginalOneLongSupportAbsorption
import Mathlib

-- UNCOMPILED_ZERO_CREDIT. Original h,z,H rate calculation in section 6/(B2).
-- The exponential-series coefficient bound replaces a Stirling invocation.
-- No rough discrepancy or asymptotic E5 estimate is assumed.

namespace ImbalancedChen
namespace OriginalOneLongExplicitBrunRates

noncomputable section
open Filter Real
open scoped Topology
open OriginalOneLongSupportAbsorption

def L2 (N : ℕ) : ℝ := Real.log (Real.log (N : ℝ))
def order (N : ℕ) : ℕ := 2 * ⌊L2 N ^ 2⌋₊ + 1
def support (z : ℕ → ℝ) (N : ℕ) : ℝ := z N ^ order N
def gap (H : ℕ → ℝ) (N : ℕ) : ℝ := H N ^ order N / (Nat.factorial (order N) : ℝ)

theorem tendsto_L2 : Tendsto L2 atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem order_bounds (N : ℕ) (hL : 1 ≤ L2 N) :
    L2 N ^ 2 ≤ (order N : ℝ) ∧ (order N : ℝ) ≤ 3 * L2 N ^ 2 := by
  have hflo := Nat.floor_le (sq_nonneg (L2 N))
  have hfhi := Nat.lt_floor_add_one (L2 N ^ 2)
  unfold order
  push_cast
  constructor <;> nlinarith [sq_nonneg (L2 N - 1)]

-- Uniform factorial-density bound obtained from ONE nonnegative exponential
-- series term at t=e^2. It has no prime/distribution or Stirling dependency.
theorem factorial_gap_le_exp (H : ℝ) (r : ℕ) (hH : 0 ≤ H) :
    H ^ r / (Nat.factorial r : ℝ) ≤ Real.exp (Real.exp 2 * H - 2 * (r : ℝ)) := by
  have hs := Real.pow_div_factorial_le_exp
    (mul_nonneg (Real.exp_pos 2).le hH) r
  have he : (Real.exp 2 * H) ^ r / (Nat.factorial r : ℝ) =
      Real.exp (2 * (r : ℝ)) * (H ^ r / (Nat.factorial r : ℝ)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show (r : ℝ) * 2 = 2 * (r : ℝ) by ring]
    ring
  rw [he] at hs
  calc
    _ = (Real.exp (2 * (r : ℝ)) * (H ^ r / (Nat.factorial r : ℝ))) /
        Real.exp (2 * (r : ℝ)) := by field_simp
    _ ≤ Real.exp (Real.exp 2 * H) / Real.exp (2 * (r : ℝ)) :=
      div_le_div_of_nonneg_right hs (Real.exp_pos _).le
    _ = _ := (Real.exp_sub _ _).symm

theorem gap_le_exp_neg_L2_sq (N : ℕ) (H : ℝ)
    (hL : max 1 (2 * Real.exp 2) ≤ L2 N) (hH : 0 ≤ H) (hHhi : H ≤ 2 * L2 N) :
    H ^ order N / (Nat.factorial (order N) : ℝ) ≤ Real.exp (-(L2 N ^ 2)) := by
  obtain ⟨hlo, hhi⟩ := order_bounds N ((le_max_left _ _).trans hL)
  have hL0 : 0 ≤ L2 N := by linarith [le_max_left (1 : ℝ) (2 * Real.exp 2)]
  have hexp := Real.exp_pos 2
  have hLexp := (le_max_right (1 : ℝ) (2 * Real.exp 2)).trans hL
  have hHmul := mul_le_mul_of_nonneg_left hHhi hexp.le
  have hLmul := mul_le_mul_of_nonneg_right hLexp hL0
  exact (factorial_gap_le_exp H (order N) hH).trans
    (Real.exp_le_exp.mpr (by nlinarith))

-- Exact original y=z^(h+1)=x^o(1), from the actual chart-cutoff log bound.
theorem support_is_subpower (z : ℕ → ℝ)
    (hz : ∀ᶠ N : ℕ in atTop, 1 ≤ z N)
    (hlogz : ∀ᶠ N : ℕ in atTop,
      Real.log (z N) ≤ 2 * Real.log (N : ℝ) / (L2 N ^ 3)) :
    SubpowerSupport (support z) := by
  intro delta hdelta
  filter_upwards [hz, hlogz,
    tendsto_L2.eventually (eventually_ge_atTop (max 1 (6 / delta))),
    eventually_ge_atTop (1 : ℕ)] with N hzN hlogzN hLN hN
  have hL : 1 ≤ L2 N := (le_max_left _ _).trans hLN
  have hL0 : 0 < L2 N := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hzpos : 0 < z N := by linarith
  have hr := (order_bounds N hL).2
  have hlogY : Real.log (support z N) ≤ 6 * Real.log (N : ℝ) / L2 N := by
    unfold support
    rw [Real.log_pow]
    calc
      _ ≤ (order N : ℝ) * (2 * Real.log (N : ℝ) / L2 N ^ 3) :=
        mul_le_mul_of_nonneg_left hlogzN (Nat.cast_nonneg _)
      _ ≤ (3 * L2 N ^ 2) * (2 * Real.log (N : ℝ) / L2 N ^ 3) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by field_simp [hL0.ne']; ring
  have hdeltaL : 6 ≤ delta * L2 N :=
    (div_le_iff₀ hdelta).1 ((le_max_right (1 : ℝ) (6 / delta)).trans hLN)
  refine ⟨by unfold support; positivity, ?_⟩
  have hlogfinal : Real.log (support z N) ≤ Real.log (N : ℝ) * delta := by
    apply hlogY.trans
    apply (div_le_iff₀ hL0).2
    have hmul := mul_le_mul_of_nonneg_right hdeltaL hlogN
    nlinarith
  rw [← Real.exp_log (pow_pos hzpos _), Real.rpow_def_of_pos hNpos]
  exact Real.exp_le_exp.mpr hlogfinal

-- Exact original epsilon=H^(h+1)/(h+1)! beats EVERY fixed log power.
-- H is the actual prime reciprocal sum; the original elementary bound
-- H<=2*loglog x is the only prime-harmonic input used here.
theorem gap_is_superlog (H : ℕ → ℝ)
    (hH : ∀ᶠ N : ℕ in atTop, 0 ≤ H N ∧ H N ≤ 2 * L2 N) :
    SuperLogGap (gap H) := by
  intro k eta heta
  let bound : ℝ := max (max 1 (2 * Real.exp 2)) (max ((k : ℝ) + 1) (-Real.log eta))
  filter_upwards [hH, tendsto_L2.eventually (eventually_ge_atTop bound),
    eventually_one_le_nat_log] with N hHN hLN hlogN
  have hLbase : max 1 (2 * Real.exp 2) ≤ L2 N := (le_max_left _ _).trans hLN
  have hLk : (k : ℝ) + 1 ≤ L2 N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hLN)
  have hLeta : -Real.log eta ≤ L2 N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hLN)
  have hL0 : 0 ≤ L2 N := by linarith [le_max_left (1 : ℝ) (2 * Real.exp 2)]
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hgap := gap_le_exp_neg_L2_sq N (H N) hLbase hHN.1 hHN.2
  calc
    _ ≤ Real.exp (-(L2 N ^ 2)) * (Real.log (N : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_right hgap (by positivity)
    _ = Real.exp (-(L2 N ^ 2) + (k : ℝ) * L2 N) := by
      rw [show Real.log (N : ℝ) = Real.exp (L2 N) by
        exact (Real.exp_log hlogpos).symm]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (-L2 N) := Real.exp_le_exp.mpr (by
      have hmul := mul_le_mul_of_nonneg_right hLk hL0
      nlinarith)
    _ ≤ Real.exp (Real.log eta) := Real.exp_le_exp.mpr (by linarith)
    _ = eta := Real.exp_log heta

end
end OriginalOneLongExplicitBrunRates
end ImbalancedChen
