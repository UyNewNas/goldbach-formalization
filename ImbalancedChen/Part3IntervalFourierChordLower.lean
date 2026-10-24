import ImbalancedChen.Part3ActualIntervalGeometricSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.
Jordan's sine chord gives a quantitative denominator bound for the actual
completed-interval phase, then a normalized individual Fourier coefficient
bound. No sum over Fourier frequencies is estimated in this module.
-/

namespace ImbalancedChen.Part3.IntervalFourierChordLowerSourceOnly
noncomputable section
open scoped BigOperators
open ActualIntervalGeometricSumSourceOnly

private lemma chord_norm (N r : ℕ) (hN : 0 < N) :
    ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖ =
      2 * |Real.sin (Real.pi * (r : ℝ) / (N : ℝ))| := by
  have he : phaseBase ((r : ℝ) / (N : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * (r : ℝ) / (N : ℝ) : ℝ) : ℂ)) := by
    unfold phaseBase
    congr 1
    push_cast
    ring
  rw [norm_sub_rev, he, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2 * Real.pi * (r : ℝ) / (N : ℝ)) / 2 =
      Real.pi * (r : ℝ) / (N : ℝ) := by ring
  rw [hhalf]
  simp [Real.norm_eq_abs, abs_mul]

/-- The first half-circle has chord length at least four times r/N. -/
theorem chord_lower_first_half (N r : ℕ)
    (hN : 2 ≤ N) (hr : 1 ≤ r) (hrhalf : r ≤ N / 2) :
    4 * (r : ℝ) / (N : ℝ) ≤
      ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖ := by
  have hNpos : 0 < N := by omega
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hrreal : (0 : ℝ) ≤ (r : ℝ) := by positivity
  have htwor : 2 * r ≤ N := by omega
  have htworReal : (2 : ℝ) * (r : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast htwor
  have hrquot : (r : ℝ) / (N : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hNreal).2
    nlinarith
  have hx0 : 0 ≤ Real.pi * (r : ℝ) / (N : ℝ) := by positivity
  have hxhalf : Real.pi * (r : ℝ) / (N : ℝ) ≤ Real.pi / 2 := by
    calc
      Real.pi * (r : ℝ) / (N : ℝ) =
          Real.pi * ((r : ℝ) / (N : ℝ)) := by ring
      _ ≤ Real.pi * (1 / 2) :=
        mul_le_mul_of_nonneg_left hrquot Real.pi_pos.le
      _ = Real.pi / 2 := by ring
  have hj := Real.mul_le_sin hx0 hxhalf
  have hlin : (2 / Real.pi) *
      (Real.pi * (r : ℝ) / (N : ℝ)) =
      2 * (r : ℝ) / (N : ℝ) := by
    field_simp [Real.pi_pos.ne', hNreal.ne']
    ring
  rw [hlin] at hj
  have hsin : 0 ≤ Real.sin (Real.pi * (r : ℝ) / (N : ℝ)) := by
    have : 0 ≤ 2 * (r : ℝ) / (N : ℝ) := by positivity
    exact this.trans hj
  rw [chord_norm N r hNpos, abs_of_nonneg hsin]
  nlinarith

/-- The full nonzero frequency range uses the shorter circular arc. -/
theorem chord_lower_min (N r : ℕ)
    (hN : 2 ≤ N) (hr : 1 ≤ r) (hrlt : r < N) :
    4 * ((min r (N - r) : ℕ) : ℝ) / (N : ℝ) ≤
      ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖ := by
  by_cases hhalf : r ≤ N / 2
  · have hmin : min r (N - r) = r := by
      apply min_eq_left
      omega
    rw [hmin]
    exact chord_lower_first_half N r hN hr hhalf
  · have hspos : 1 ≤ N - r := by omega
    have hshalf : N - r ≤ N / 2 := by omega
    have hmin : min r (N - r) = N - r := by
      apply min_eq_right
      omega
    rw [hmin]
    have hNpos : 0 < N := by omega
    have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hangle : Real.pi - Real.pi * (r : ℝ) / (N : ℝ) =
        Real.pi * ((N - r : ℕ) : ℝ) / (N : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hrlt)]
      field_simp [hNreal.ne']
      ring
    have hsin : Real.sin (Real.pi * (r : ℝ) / (N : ℝ)) =
        Real.sin (Real.pi * ((N - r : ℕ) : ℝ) / (N : ℝ)) := by
      rw [← Real.sin_pi_sub, hangle]
    rw [chord_norm N r hNpos, hsin,
      ← chord_norm N (N - r) hNpos]
    exact chord_lower_first_half N (N - r) hN hspos hshalf

/-- The normalized coefficient inherits the geometric and chord bounds. -/
theorem normalized_interval_fourier_coeff_bound (N r lo hi : ℕ)
    (hN : 2 ≤ N) (hr : 1 ≤ r) (hrlt : r < N) (hlo : lo ≤ hi) :
    ‖∑ m ∈ Finset.Ico lo hi,
        phaseAt ((r : ℝ) / (N : ℝ)) m‖ / (N : ℝ) ≤
      min (((hi - lo : ℕ) : ℝ) / (N : ℝ))
        (1 / (2 * ((min r (N - r) : ℕ) : ℝ))) := by
  let s : ℕ := min r (N - r)
  let D : ℝ := ‖1 - phaseBase ((r : ℝ) / (N : ℝ))‖
  let S : ℝ := ‖∑ m ∈ Finset.Ico lo hi,
      phaseAt ((r : ℝ) / (N : ℝ)) m‖
  have hsposNat : 0 < s := by
    dsimp [s]
    have hright : 0 < N - r := by omega
    exact lt_min (by omega) hright
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hsposNat
  have hNpos : 0 < N := by omega
  have hNreal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hchord : 4 * (s : ℝ) / (N : ℝ) ≤ D :=
    chord_lower_min N r hN hr hrlt
  have hDpos : 0 < D :=
    lt_of_lt_of_le (by positivity : 0 < 4 * (s : ℝ) / (N : ℝ)) hchord
  have hne : phaseBase ((r : ℝ) / (N : ℝ)) ≠ 1 := by
    intro he
    have hz : D = 0 := by simp [D, he]
    linarith
  have hraw := phase_sum_norm_le_min ((r : ℝ) / (N : ℝ)) hlo hne
  have hlength : S ≤ ((hi - lo : ℕ) : ℝ) := by
    exact (le_min_iff.mp hraw).1
  have hden : S ≤ 2 / D := by
    exact (le_min_iff.mp hraw).2
  have hcross : 4 * (s : ℝ) ≤ (N : ℝ) * D :=
    (div_le_iff₀ hNreal).mp hchord
  have hquot : 2 / D ≤ (N : ℝ) / (2 * (s : ℝ)) := by
    apply (div_le_div_iff₀ hDpos (by positivity : 0 < 2 * (s : ℝ))).2
    nlinarith
  have hlenNorm : S / (N : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right hlength hNreal.le
  have hdenNorm : S / (N : ℝ) ≤ 1 / (2 * (s : ℝ)) := by
    calc
      S / (N : ℝ) ≤
          ((N : ℝ) / (2 * (s : ℝ))) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hden.trans hquot) hNreal.le
      _ = 1 / (2 * (s : ℝ)) := by
        field_simp [hNreal.ne', hspos.ne']
        ring
  exact le_min hlenNorm hdenNorm

end
end ImbalancedChen.Part3.IntervalFourierChordLowerSourceOnly
