import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalPowerZeroFree

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The quadratic headline's H(q,t) contains 1/|2t| and therefore cannot be
minimized uniformly through t=0. This source proves the actual missing
low-height exclusion, using the genuine horizontal and vertical derivative
estimates and a displayed positive lower bound for the actual L(1).
No zero-free rectangle, SW estimate or left-strip norm is assumed.
-/

namespace ImbalancedChen.Part3.RoughQuadraticLowRectangle20261026b
noncomputable section
open Complex Set
open AnalyticNumberTheory.LargeSieve
open DirichletLGlobalConductorLogValueBound

/-- This cutoff controls every imaginary part in the enlarged rectangle. -/
def rectangleCutoff (q : ℕ) (T : ℝ) : ℕ := q * (⌊T + 1⌋₊ + 1)

def rectangleLog (q : ℕ) (T : ℝ) : ℝ := 1 + Real.log (rectangleCutoff q T)

theorem cutoff_le_rectangleCutoff {q : ℕ} {T t : ℝ} (ht : |t| ≤ T + 1) :
    dirichletLConductorHeightCutoff q t ≤ rectangleCutoff q T := by
  exact Nat.mul_le_mul_left q (Nat.add_le_add_right (Nat.floor_mono ht) 1)

theorem rectangleCutoff_pos (q : ℕ) [NeZero q] (T : ℝ) :
    0 < rectangleCutoff q T := by
  unfold rectangleCutoff
  exact Nat.mul_pos (NeZero.pos q) (Nat.succ_pos _)

theorem one_le_rectangleLog (q : ℕ) [NeZero q] (T : ℝ) :
    1 ≤ rectangleLog q T := by
  have hM : (1 : ℝ) ≤ rectangleCutoff q T := by
    exact_mod_cast rectangleCutoff_pos q T
  exact le_add_of_nonneg_right (Real.log_nonneg hM)

theorem heightLog_le_rectangleLog {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {T t : ℝ}
    (ht : |t| ≤ T + 1) :
    1 + Real.log (dirichletLConductorHeightCutoff q t) ≤ rectangleLog q T := by
  unfold rectangleLog
  exact add_le_add_left (Real.log_le_log
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two
      (two_le_conductorHeightCutoff χ hχ t)))
    (by exact_mod_cast cutoff_le_rectangleCutoff ht)) 1

def lowHeight (q : ℕ) (T r : ℝ) : ℝ := r / (256 * rectangleLog q T ^ 2)

def lowWidth (q : ℕ) (T r : ℝ) : ℝ :=
  min (1 / 2) (min (1 / rectangleLog q T) (lowHeight q T r))

theorem lowHeight_pos (q : ℕ) [NeZero q] (T : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < lowHeight q T r := by
  unfold lowHeight
  exact div_pos hr (mul_pos (by norm_num) (pow_pos
    (lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q T)) 2))

theorem lowWidth_pos (q : ℕ) [NeZero q] (T : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < lowWidth q T r := by
  unfold lowWidth
  exact lt_min (by norm_num) (lt_min
    (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q T)))
    (lowHeight_pos q T hr))

/-- A quantitative box at low height, with all constants before beta and t.
The sole L-value input is a genuine positive lower bound for the actual L(1).
It can subsequently be supplied by the primitive Siegel theorem together
with the actual imprimitive finite Euler correction. -/
theorem quadratic_low_rectangle {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {T r : ℝ} (hr : 0 < r) (hL : r ≤ (χ.LFunction 1).re)
    {β t : ℝ} (ht : |t| ≤ T + 1) (htlow : |t| ≤ lowHeight q T r)
    (hβlo : 1 - lowWidth q T r ≤ β) (hβhi : β ≤ 1) :
    χ.LFunction (β + I * t) ≠ 0 := by
  let D := rectangleLog q T
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q T)
  have hLpos := log_conductorHeightCutoff_pos χ hχ t
  have hlog := heightLog_le_rectangleLog χ hχ ht
  have hlocal : 0 ≤ 1 + Real.log (dirichletLConductorHeightCutoff q t) := by
    linarith
  have hsq : (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ hlocal hlog 2
  have hwHalf : lowWidth q T r ≤ 1 / 2 := min_le_left _ _
  have hwInv : lowWidth q T r ≤ 1 / D :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwLow : lowWidth q T r ≤ lowHeight q T r :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hhalf : 1 / 2 ≤ β := by linarith
  have hinv : 1 / D ≤ 1 / Real.log (dirichletLConductorHeightCutoff q t) :=
    one_div_le_one_div_of_le hLpos (by linarith)
  have hnear : 1 - 1 / Real.log (dirichletLConductorHeightCutoff q t) ≤ β := by
    linarith [hwInv.trans hinv]
  have hh := norm_LFunction_sub_le_sixtyfour_mul_conductorHeightLogSq
    χ hχ hhalf hnear hβhi (by norm_num : (1 : ℝ) ≤ 2)
  have hv := norm_LFunction_vertical_sub_le_sixtyfour_mul_conductorHeightLogSq χ hχ t
  have hpay : 64 * D ^ 2 * lowHeight q T r = r / 4 := by
    unfold lowHeight
    dsimp only [D]
    field_simp [ne_of_gt hD]
    ring
  have hh' : ‖χ.LFunction (1 + t * I) - χ.LFunction (β + t * I)‖ ≤ r / 4 := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * (1 - β) := hh
      _ ≤ 64 * D ^ 2 * lowHeight q T r := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hsq (by norm_num)
        · linarith
        · linarith
        · positivity
      _ = r / 4 := hpay
  have hv' : ‖χ.LFunction (1 + t * I) - χ.LFunction 1‖ ≤ r / 4 := by
    calc
      _ ≤ 64 * (1 + Real.log (dirichletLConductorHeightCutoff q t)) ^ 2 * |t| := hv
      _ ≤ 64 * D ^ 2 * lowHeight q T r :=
        mul_le_mul (mul_le_mul_of_nonneg_left hsq (by norm_num)) htlow
          (abs_nonneg _) (by positivity)
      _ = r / 4 := hpay
  exact LFunction_ne_zero_lowHeight_of_twoSegmentBudgets χ hquad hχ hh' hv'
    (by linarith)

end
end ImbalancedChen.Part3.RoughQuadraticLowRectangle20261026b
