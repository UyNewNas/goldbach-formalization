import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# The actual logarithmic Rosser level for the initial Chen sieve

For a fixed real exponent `B`, the distribution cap is the literal natural
floor `Q = floor(sqrt N / (log N)^B)`, and the strict Rosser level is
`D = Q + 1`. We prove `log D / log N -> 1/2` without an analytic hypothesis.
For a fixed `0 < a < 1/4`, this gives `t = log D / log(N^a) -> 1/(2a)`
and all the numerical lower-Rosser gates at one common eventual threshold.

The exponent `B` is real, including in `(log N)^B`. Nonnegativity of `B`
is needed only for the cap `Q <= sqrt N`. The remainder cap is exactly
`D - 1 = Q`; we do not assert the generally false bound `D <= sqrt N`.
There are no external sieve imports or distribution hypotheses here.
-/

namespace ImbalancedChen

open Filter Topology

noncomputable section

private def chenLogLevelUnrounded (B : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B

/-- The actual floor-valued distribution cap, with a real log exponent. -/
def chenInitialLevelCap (B : ℝ) (N : ℕ) : ℕ :=
  Nat.floor (Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B)

/-- The strict Rosser level is one more than the distribution cap. -/
def chenInitialRosserD (B : ℝ) (N : ℕ) : ℕ :=
  chenInitialLevelCap B N + 1

/-- The actual sieve parameter at the power cutoff `z = N^a`. -/
def chenInitialRosserT (B a : ℝ) (N : ℕ) : ℝ :=
  Real.log (chenInitialRosserD B N : ℝ) / Real.log ((N : ℝ) ^ a)

/-- The finite remainder is supported through `Q`, rather than `Q + 1`. -/
theorem chenInitialRosserD_sub_one (B : ℝ) (N : ℕ) :
    chenInitialRosserD B N - 1 = chenInitialLevelCap B N := by
  simp [chenInitialRosserD]

private theorem chenLogLevelUnrounded_pos (B : ℝ) {N : ℕ}
    (hN : (1 : ℝ) < N) : 0 < chenLogLevelUnrounded B N := by
  exact div_pos (Real.sqrt_pos.2 (lt_trans zero_lt_one hN))
    (Real.rpow_pos_of_pos (Real.log_pos hN) B)

private theorem tendsto_nat_log_for_chen_level :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_log_chenLogLevelUnrounded_div_log (B : ℝ) :
    Tendsto (fun N : ℕ => Real.log (chenLogLevelUnrounded B N) /
      Real.log (N : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlogDiv : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hloglog : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) atTop (𝓝 0) :=
    hlogDiv.comp tendsto_nat_log_for_chen_level
  have hlim : Tendsto (fun N : ℕ => (1 / 2 : ℝ) - B *
      (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds.sub (hloglog.const_mul B))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hpow : 0 < (Real.log (N : ℝ)) ^ B := Real.rpow_pos_of_pos hlog B
  dsimp [chenLogLevelUnrounded]
  rw [Real.log_div hsqrt.ne' hpow.ne', Real.log_sqrt (Nat.cast_nonneg N),
    Real.log_rpow hlog B]
  field_simp [hlog.ne'] <;> ring

private theorem eventually_chenInitialRosserD_sandwich (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ chenLogLevelUnrounded B N ∧
      chenLogLevelUnrounded B N < (chenInitialRosserD B N : ℝ) ∧
      (chenInitialRosserD B N : ℝ) ≤ 2 * chenLogLevelUnrounded B N := by
  have hratioPos : ∀ᶠ N : ℕ in atTop,
      0 < Real.log (chenLogLevelUnrounded B N) / Real.log (N : ℝ) :=
    (tendsto_log_chenLogLevelUnrounded_div_log B).eventually
      (lt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hratioPos, eventually_ge_atTop (2 : ℕ)] with N hratio hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hxpos := chenLogLevelUnrounded_pos B hN1
  have hlogx : 0 < Real.log (chenLogLevelUnrounded B N) :=
    (div_pos_iff_of_pos_right (Real.log_pos hN1)).mp hratio
  have hx1 : 1 < chenLogLevelUnrounded B N :=
    (Real.log_pos_iff hxpos.le).mp hlogx
  have hfloor : (chenInitialLevelCap B N : ℝ) ≤ chenLogLevelUnrounded B N :=
    Nat.floor_le hxpos.le
  have hstrict : chenLogLevelUnrounded B N < (chenInitialRosserD B N : ℝ) := by
    simpa only [chenInitialRosserD, chenInitialLevelCap, chenLogLevelUnrounded,
      Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (chenLogLevelUnrounded B N)
  refine ⟨hx1.le, hstrict, ?_⟩
  calc
    (chenInitialRosserD B N : ℝ) = (chenInitialLevelCap B N : ℝ) + 1 := by
      simp only [chenInitialRosserD, Nat.cast_add, Nat.cast_one]
    _ ≤ chenLogLevelUnrounded B N + 1 := add_le_add_right hfloor 1
    _ ≤ 2 * chenLogLevelUnrounded B N := by linarith

/-- Rounding up by `floor + 1` preserves the limiting logarithmic level.
This holds for every fixed real `B`, including negative `B`. -/
theorem tendsto_log_chenInitialRosserD_div_log (B : ℝ) :
    Tendsto (fun N : ℕ => Real.log (chenInitialRosserD B N : ℝ) /
      Real.log (N : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlo := tendsto_log_chenLogLevelUnrounded_div_log B
  have hhi : Tendsto (fun N : ℕ =>
      Real.log (chenLogLevelUnrounded B N) / Real.log (N : ℝ) +
      Real.log 2 / Real.log (N : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [add_zero] using
      hlo.add (tendsto_nat_log_for_chen_level.const_div_atTop (Real.log 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_chenInitialRosserD_sandwich B,
      eventually_ge_atTop (2 : ℕ)] with N hx hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (lt_of_lt_of_le zero_lt_one hx.1) hx.2.1.le)
      (Real.log_pos hN1).le
  · filter_upwards [eventually_chenInitialRosserD_sandwich B,
      eventually_ge_atTop (2 : ℕ)] with N hx hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hxpos : 0 < chenLogLevelUnrounded B N := lt_of_lt_of_le zero_lt_one hx.1
    have hDpos : 0 < (chenInitialRosserD B N : ℝ) := lt_trans hxpos hx.2.1
    have hlog := Real.log_le_log hDpos hx.2.2
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne'] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog (Real.log_pos hN1).le
    simpa only [add_div, add_comm] using hdiv

/-- The logarithm of the actual natural Rosser level diverges. -/
theorem tendsto_log_chenInitialRosserD_atTop (B : ℝ) :
    Tendsto (fun N : ℕ => Real.log (chenInitialRosserD B N : ℝ)) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    (tendsto_log_chenInitialRosserD_div_log B) tendsto_nat_log_for_chen_level
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_mul_cancel₀ _ (Real.log_pos hN1).ne'

/-- The parameter at the actual power cutoff has its expected fixed limit. -/
theorem tendsto_chenInitialRosserT (B : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (chenInitialRosserT B a) atTop (𝓝 (1 / (2 * a))) := by
  have hvalue : (1 / 2 : ℝ) / a = 1 / (2 * a) := by
    field_simp [ha.ne'] <;> ring
  have h : Tendsto (fun N : ℕ =>
      (Real.log (chenInitialRosserD B N : ℝ) / Real.log (N : ℝ)) / a)
      atTop (𝓝 (1 / (2 * a))) := by
    rw [← hvalue]
    exact (tendsto_log_chenInitialRosserD_div_log B).div_const a
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  dsimp [chenInitialRosserT]
  rw [Real.log_rpow hNpos a, div_div]
  congr 1
  ring

/-- All numerical gates hold at one threshold chosen after the fixed real
parameters `B` and `a`. The finite remainder cap is retained literally.
This theorem supplies numerical geometry only, not a sieve lower bound. -/
theorem exists_chenInitialRosser_numeric_gates (B a : ℝ)
    (hB : 0 ≤ B) (ha : 0 < a) (haQuarter : a < 1 / 4) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      2 ≤ chenInitialRosserD B N ∧
      1 < (N : ℝ) ^ a ∧
      2 ≤ chenInitialRosserT B a N ∧
      chenInitialRosserT B a N ^ 13 ≤ Real.log (chenInitialRosserD B N : ℝ) ∧
      Real.exp 1 ≤ Real.log (chenInitialRosserD B N : ℝ) ∧
      chenInitialRosserD B N - 1 = chenInitialLevelCap B N ∧
      (chenInitialLevelCap B N : ℝ) ≤ Real.sqrt (N : ℝ) := by
  have htlim := tendsto_chenInitialRosserT B ha
  have htvalue : (2 : ℝ) < 1 / (2 * a) := by
    apply (lt_div_iff₀ (by linarith : 0 < 2 * a)).mpr
    nlinarith
  have htLower : ∀ᶠ N : ℕ in atTop, 2 < chenInitialRosserT B a N :=
    htlim.eventually (lt_mem_nhds htvalue)
  have htPow : ∀ᶠ N : ℕ in atTop,
      chenInitialRosserT B a N ^ 13 < (1 / (2 * a)) ^ 13 + 1 :=
    (htlim.pow 13).eventually (gt_mem_nhds (lt_add_one _))
  have hlogLarge : ∀ᶠ N : ℕ in atTop,
      (1 / (2 * a)) ^ 13 + 1 ≤ Real.log (chenInitialRosserD B N : ℝ) :=
    (tendsto_log_chenInitialRosserD_atTop B).eventually
      (eventually_ge_atTop ((1 / (2 * a)) ^ 13 + 1))
  have hlogExp : ∀ᶠ N : ℕ in atTop,
      Real.exp 1 ≤ Real.log (chenInitialRosserD B N : ℝ) :=
    (tendsto_log_chenInitialRosserD_atTop B).eventually
      (eventually_ge_atTop (Real.exp 1))
  have hlogOne : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    tendsto_nat_log_for_chen_level.eventually (eventually_ge_atTop 1)
  apply eventually_atTop.mp
  filter_upwards [htLower, htPow, hlogLarge, hlogExp, hlogOne,
    eventually_chenInitialRosserD_sandwich B, eventually_ge_atTop (2 : ℕ)]
    with N ht htPowN hlarge hexp hlog hx hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hD1 : 1 < chenInitialRosserD B N := by
    exact_mod_cast (lt_of_le_of_lt hx.1 hx.2.1)
  have hden : 1 ≤ (Real.log (N : ℝ)) ^ B := Real.one_le_rpow hlog hB
  have hcap : (chenInitialLevelCap B N : ℝ) ≤ chenLogLevelUnrounded B N :=
    Nat.floor_le (chenLogLevelUnrounded_pos B hN1).le
  have hraw : chenLogLevelUnrounded B N ≤ Real.sqrt (N : ℝ) := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hden (Real.sqrt_nonneg (N : ℝ))
  exact ⟨by omega, Real.one_lt_rpow hN1 ha, ht.le, htPowN.le.trans hlarge,
    hexp, chenInitialRosserD_sub_one B N, hcap.trans hraw⟩

end

end ImbalancedChen
