import ImbalancedChen.VariableEnvelopeCertificates
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Buffered coarse caps pay the first Rosser cube

The extended-prefix construction retains first labels below `19/96 - 4e`
and uses `min (299/500 - 2e) (Gamma - 2e)`.  This file proves its strict
first-cube margin for the actual rational and integer box lower bounds.
The one-variable fallback also covers the transition strip across `mu`.
No distribution assertion or third-cube admission is assumed or concluded.
-/

namespace ImbalancedChen.VariableEnvelope

noncomputable section

def extendedFirstStop : ℝ := 19 / 96

def extendedDistributionCap : ℝ := 299 / 500

def bufferedCoarseCap (e Gamma : ℝ) : ℝ :=
  min (extendedDistributionCap - 2 * e) (Gamma - 2 * e)

theorem buffered_distribution_margin {e x : ℝ}
    (hx : x ≤ extendedFirstStop - 4 * e) :
    17 / 4000 + 10 * e ≤ extendedDistributionCap - 2 * e - 3 * x := by
  dsimp [extendedFirstStop, extendedDistributionCap] at *
  linarith

theorem extended_v_margin_above_mu {x : ℝ} (hx : mu ≤ x) :
    v x - 3 * x = (9 / 2) * (extendedFirstStop - x) := by
  rw [v_eq_C hx]
  dsimp [C, extendedFirstStop]
  ring

theorem buffered_v_margin {e x : ℝ} (he : 0 < e)
    (hsmall : 3 * e < 3 / 256)
    (hx : x ≤ extendedFirstStop - 4 * e) :
    3 * e < v x - 3 * x := by
  by_cases hm : x ≤ mu
  · rw [v_eq_A hm]
    dsimp [A, mu] at *
    linarith
  · rw [extended_v_margin_above_mu (le_of_not_ge hm)]
    linarith

theorem three_mul_lt_bufferedCoarseCap {e x Gamma : ℝ} (he : 0 < e)
    (hx : x ≤ extendedFirstStop - 4 * e) (hGamma : 3 * x < Gamma - 2 * e) :
    3 * x < bufferedCoarseCap e Gamma := by
  apply lt_min (by linarith [buffered_distribution_margin hx]) hGamma

/-- A whole-box lower bound with error at most `e` retains a strict cube margin. -/
theorem bufferedCoarseCap_original_lower {e x y z Gamma : ℝ}
    (he : 0 < e) (hsmall : 3 * e < 3 / 256)
    (hx : x ≤ extendedFirstStop - 4 * e) (h : Ordered x y z)
    (herr : original x y z - Gamma ≤ e) :
    3 * x < bufferedCoarseCap e Gamma := by
  apply three_mul_lt_bufferedCoarseCap he hx
  linarith [original_margin h]

/-- Unlike the full envelope, this fallback needs no restriction `x ≤ mu`. -/
theorem bufferedCoarseCap_v_lower {e x Gamma : ℝ}
    (he : 0 < e) (hsmall : 3 * e < 3 / 256)
    (hx : x ≤ extendedFirstStop - 4 * e) (herr : v x - Gamma ≤ e) :
    3 * x < bufferedCoarseCap e Gamma := by
  apply three_mul_lt_bufferedCoarseCap he hx
  linarith [buffered_v_margin he hsmall hx]

theorem rationalBox_buffered_first_cube (b : RationalBox) {e x y z : ℝ}
    (he : 0 < e) (hsmall : 3 * e < 3 / 256)
    (h : b.ValidPoint x y z) (hstop : (b.ux : ℝ) ≤ extendedFirstStop - 4 * e)
    (hwidth : (9 / 2 : ℝ) * b.width ≤ e) :
    3 * x < bufferedCoarseCap e b.lower := by
  exact bufferedCoarseCap_original_lower he hsmall (h.1.2.1.trans hstop) h.2
    ((RationalBox.enclosure_error h).2.1.trans hwidth)

/-- The integer certificate retains its separate rounding error `2 / D`. -/
theorem scaledBox_buffered_first_cube (D M : ℤ) (b : ScaledBox)
    (hD : 0 < D) (hM : 128 * M = 25 * D) {e x y z : ℝ}
    (he : 0 < e) (hsmall : 3 * e < 3 / 256)
    (h : (b.toRational D).ValidPoint x y z)
    (hstop : ((b.toRational D).ux : ℝ) ≤ extendedFirstStop - 4 * e)
    (hprecision : (9 / 2 : ℝ) * (b.toRational D).width + 2 / D ≤ e) :
    3 * x < bufferedCoarseCap e (b.lower D) := by
  exact bufferedCoarseCap_original_lower he hsmall (h.1.2.1.trans hstop) h.2
    ((ScaledBox.enclosure_error D M b hD hM h).2.1.trans hprecision)

theorem rationalInterval_v_error {l u : ℚ} {x : ℝ}
    (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    v x - qVLo l u ≤ (3 / 2 : ℝ) * ((u : ℝ) - l) := by
  have hlu : l ≤ u := by exact_mod_cast hl.trans hu
  have hg : (qVHi l u : ℝ) - qVLo l u ≤ (3 / 2 : ℝ) * ((u : ℝ) - l) := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr (qVHi_sub_qVLo_le hlu)
    push_cast at hh
    exact hh
  linarith [v_le_qVHi hl hu]

/-- A fixed rational interval supplies the fallback cap, including crossing intervals. -/
theorem rationalInterval_buffered_first_cube {l u : ℚ} {e x : ℝ}
    (he : 0 < e) (hsmall : 3 * e < 3 / 256)
    (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ))
    (hstop : (u : ℝ) ≤ extendedFirstStop - 4 * e)
    (hwidth : (3 / 2 : ℝ) * ((u : ℝ) - l) ≤ e) :
    3 * x < bufferedCoarseCap e (qVLo l u) := by
  exact bufferedCoarseCap_v_lower he hsmall (hu.trans hstop)
    ((rationalInterval_v_error hl hu).trans hwidth)

/-- Convert the exponent margin to the literal strict integer-prefix cube test. -/
theorem first_cube_lt_level_of_exponent {N x lambda : ℝ} (p : ℕ)
    (hN : 1 < N) (hp : (p : ℝ) ≤ N ^ x) (hmargin : 3 * x < lambda) :
    (p : ℝ) ^ 3 < N ^ lambda := by
  calc
    (p : ℝ) ^ 3 ≤ (N ^ x) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hp 3
    _ = N ^ (x * 3) := (Real.rpow_mul_natCast (by linarith) x 3).symm
    _ < N ^ lambda := Real.rpow_lt_rpow_of_exponent_lt hN (by linarith)

theorem rationalBox_buffered_prime_cube (b : RationalBox) {e x y z N : ℝ}
    (p : ℕ) (hN : 1 < N) (hp : (p : ℝ) ≤ N ^ x)
    (he : 0 < e) (hsmall : 3 * e < 3 / 256)
    (h : b.ValidPoint x y z) (hstop : (b.ux : ℝ) ≤ extendedFirstStop - 4 * e)
    (hwidth : (9 / 2 : ℝ) * b.width ≤ e) :
    (p : ℝ) ^ 3 < N ^ bufferedCoarseCap e b.lower :=
  first_cube_lt_level_of_exponent p hN hp
    (rationalBox_buffered_first_cube b he hsmall h hstop hwidth)

/-- Certificate acceptance bounds the literal clipped cap, not only the envelope. -/
theorem scaled_marginCheck_clipped_cap (D M NT : ℤ) (b : ScaledBox) {eta : ℚ}
    (hc : b.marginCheck D M NT eta = true) {x y z : ℝ}
    (h : (b.toRational D).ValidPoint x y z) :
    3 * x + eta < (b.clippedLower D M NT : ℝ) := by
  have hh : ((0 < D ∧ 128 * M = 25 * D) ∧ (b.toRational D).feasible = true) ∧
      0 < b.clippedLower D M NT - 3 * ((b.ux : ℚ) / D) - eta := by
    simpa only [ScaledBox.marginCheck, Bool.and_eq_true, decide_eq_true_eq] using hc
  have hcr : (0 : ℝ) < (b.clippedLower D M NT : ℝ) -
      3 * ((b.ux : ℝ) / D) - eta := by exact_mod_cast hh.2
  have hx : x ≤ (b.ux : ℝ) / D := by
    simpa only [ScaledBox.toRational, Rat.cast_div, Rat.cast_intCast] using h.1.2.1
  linarith

end

end ImbalancedChen.VariableEnvelope
