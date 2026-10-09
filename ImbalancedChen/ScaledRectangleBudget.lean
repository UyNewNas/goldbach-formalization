import ImbalancedChen.SelectedGridRanges
import ImbalancedChen.LogMeshGridCount

/-!
# Fixed-precision budgets at the enlarged rectangle ambient size

The full selected rectangles have product cap `4N`. This file supplies
the quantitative bookkeeping needed to use a distribution estimate at
that ambient size, while retaining the desired modulus scale at `N`.

For every fixed real supplier exponent `B`, the fixed natural exponent
`ceil B + 1` suffices eventually. The threshold precedes every modulus,
grid ratio and cell. A separate unconditional estimate pays the literal
polylogarithmic grid count, the ambient factor four, and the factor four
from two-prefix recentering. Accuracy `2 * (k + 1) + 3` makes this entire
numerical budget negligible in the genuine singular normalization.
The general accuracy parameter below is natural; a desired real accuracy
can be replaced by its natural ceiling, since `log N >= 1` eventually.

No analytic distribution estimate or target discrepancy bound is assumed
or asserted. The last budget is the coefficient which would multiply
two uniform raw prefix bounds supplied by a separate analytic theorem.
-/

namespace ImbalancedChen

open Filter
open scoped BigOperators

noncomputable section

/-- The logarithms at the original and enlarged ambient sizes are comparable
on every sufficiently large natural input. -/
theorem eventually_log_four_mul_bounds :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧
        Real.log (N : ℝ) ≤ Real.log (4 * (N : ℝ)) ∧
        Real.log (4 * (N : ℝ)) ≤ 4 * Real.log (N : ℝ) := by
  filter_upwards [eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hlog hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hlog, Real.log_le_log hNpos (by nlinarith), ?_⟩
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hNpos.ne']
  have hfour := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith

/-- A single additional natural logarithm power pays enlargement from `N`
to `4N`, for each fixed real supplier exponent. No uniformity in `B` is
claimed: `B` is chosen before the eventual threshold. -/
theorem eventually_scaled_log_denominator_le (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (Real.log (4 * (N : ℝ))) ^ B ≤
        (Real.log (N : ℝ)) ^ (Nat.ceil B + 1) := by
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (4 : ℝ) ^ Nat.ceil B ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop ((4 : ℝ) ^ Nat.ceil B))
  filter_upwards [eventually_log_four_mul_bounds, hlarge] with N hlog hlargeN
  have hlogFour : 1 ≤ Real.log (4 * (N : ℝ)) := hlog.1.trans hlog.2.1
  calc
    (Real.log (4 * (N : ℝ))) ^ B ≤
        (Real.log (4 * (N : ℝ))) ^ (Nat.ceil B : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogFour (Nat.le_ceil B)
    _ = (Real.log (4 * (N : ℝ))) ^ Nat.ceil B := by rw [Real.rpow_natCast]
    _ ≤ (4 * Real.log (N : ℝ)) ^ Nat.ceil B :=
      pow_le_pow_left₀ (by linarith) hlog.2.2 _
    _ = (4 : ℝ) ^ Nat.ceil B * (Real.log (N : ℝ)) ^ Nat.ceil B := mul_pow _ _ _
    _ ≤ Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ Nat.ceil B :=
      mul_le_mul_of_nonneg_right hlargeN (pow_nonneg (by linarith [hlog.1]) _)
    _ = (Real.log (N : ℝ)) ^ (Nat.ceil B + 1) := by rw [pow_succ]; ring

/-- The original square-root/logarithm modulus cap fits the enlarged
ambient cap. Both square roots and both logarithms are literal. -/
theorem eventually_scaled_modulus_cap_le (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ (Nat.ceil B + 1) ≤
        Real.sqrt (4 * (N : ℝ)) / (Real.log (4 * (N : ℝ))) ^ B := by
  filter_upwards [eventually_scaled_log_denominator_le B,
    eventually_log_four_mul_bounds] with N hden hlog
  have hscaledpos : 0 < (Real.log (4 * (N : ℝ))) ^ B :=
    Real.rpow_pos_of_pos (by linarith [hlog.1, hlog.2.1]) B
  calc
    Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ (Nat.ceil B + 1) ≤
        Real.sqrt (N : ℝ) / (Real.log (4 * (N : ℝ))) ^ B :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hscaledpos hden
    _ ≤ Real.sqrt (4 * (N : ℝ)) / (Real.log (4 * (N : ℝ))) ^ B :=
      div_le_div_of_nonneg_right
        (Real.sqrt_le_sqrt (by
          nlinarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N])) hscaledpos.le

/-- A real-exponent application interface: the stronger exponent is fixed
before the threshold, and the threshold is uniform over all natural moduli. -/
theorem exists_eventually_scaled_modulus_gate (B : ℝ) :
    ∃ B' : ℝ, 0 ≤ B' ∧ B ≤ B' ∧
      ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ,
        (Q : ℝ) ≤ Real.sqrt (N : ℝ) / (Real.log (N : ℝ)) ^ B' →
          (Q : ℝ) ≤ Real.sqrt (4 * (N : ℝ)) /
            (Real.log (4 * (N : ℝ))) ^ B := by
  refine ⟨((Nat.ceil B + 1 : ℕ) : ℝ), Nat.cast_nonneg _, ?_, ?_⟩
  · have hceil := Nat.le_ceil B
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  · filter_upwards [eventually_scaled_modulus_cap_le B] with N hcap
    intro Q hQ
    rw [Real.rpow_natCast] at hQ
    exact hQ.trans hcap

/-- The exact natural floor of the original cap obeys the supplier cap;
no positive-cap assumption or rounding loss is inserted. -/
theorem eventually_floor_scaled_modulus_cap_le (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.floor (Real.sqrt (N : ℝ) /
        (Real.log (N : ℝ)) ^ (Nat.ceil B + 1)) : ℝ) ≤
          Real.sqrt (4 * (N : ℝ)) / (Real.log (4 * (N : ℝ))) ^ B := by
  filter_upwards [eventually_scaled_modulus_cap_le B,
    eventually_one_le_nat_log] with N hcap hlog
  exact (Nat.floor_le (div_nonneg (Real.sqrt_nonneg _)
    (pow_nonneg (by linarith) _))).trans hcap

/-- The full explicit cell-count majorant costs exactly `2 * (k + 1)`
logarithm powers. This finite bound retains the final endpoint cell. -/
theorem scaled_grid_count_budget_le (k A N : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hN : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ)) :
    (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 *
      (C * (4 * (N : ℝ)) /
        (Real.log (4 * (N : ℝ))) ^ (2 * (k + 1) + A)) ≤
      36 * C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hlogFour : Real.log (N : ℝ) ≤ Real.log (4 * (N : ℝ)) :=
    Real.log_le_log hNpos (by nlinarith)
  have hu : 1 ≤ (Real.log (N : ℝ)) ^ (k + 1) := one_le_pow₀ hlog
  have hcount : (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 ≤
      9 * ((Real.log (N : ℝ)) ^ (k + 1)) ^ 2 := by
    nlinarith [sq_nonneg ((Real.log (N : ℝ)) ^ (k + 1) - 1)]
  have hden : C * (4 * (N : ℝ)) /
        (Real.log (4 * (N : ℝ))) ^ (2 * (k + 1) + A) ≤
      C * (4 * (N : ℝ)) / (Real.log (N : ℝ)) ^ (2 * (k + 1) + A) :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hlogpos _)
      (pow_le_pow_left₀ hlogpos.le hlogFour _)
  calc
    _ ≤ (9 * ((Real.log (N : ℝ)) ^ (k + 1)) ^ 2) *
        (C * (4 * (N : ℝ)) /
          (Real.log (N : ℝ)) ^ (2 * (k + 1) + A)) :=
      mul_le_mul hcount hden
        (div_nonneg (by positivity) (pow_nonneg (hlogpos.le.trans hlogFour) _))
        (by positivity)
    _ = 36 * C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
      rw [show 2 * (k + 1) + A = (k + 1) * 2 + A by omega,
        pow_add (Real.log (N : ℝ)) ((k + 1) * 2) A,
        pow_mul (Real.log (N : ℝ)) (k + 1) 2]
      field_simp [hlogpos.ne'] <;> ring

/-- The actual selected count pays both raw-prefix budgets, their
factor-two recentering costs, and the enlarged ambient numerator. The
threshold is independent of the source exponents and real cutoff. -/
theorem eventually_actualGrid_scaled_accuracy_budget (k A : ℕ)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, ∀ num den : ℕ, ∀ T : ℝ,
      ((actualGridIntersectingIndices num den N T
        (1 + boundaryLogMesh k N)).card : ℝ) *
        (4 * (C * (4 * (N : ℝ)) /
          (Real.log (4 * (N : ℝ))) ^ (2 * (k + 1) + A))) ≤
        144 * C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  filter_upwards [eventually_actualGrid_logMesh_card_le k,
    eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hcount hlog hN
  intro num den T
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogFour : 0 ≤ Real.log (4 * (N : ℝ)) :=
    Real.log_nonneg (by nlinarith)
  calc
    _ ≤ (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 *
        (4 * (C * (4 * (N : ℝ)) /
          (Real.log (4 * (N : ℝ))) ^ (2 * (k + 1) + A))) :=
      mul_le_mul_of_nonneg_right (hcount num den T).1
        (by positivity)
    _ = (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 *
        ((4 * C) * (4 * (N : ℝ)) /
          (Real.log (4 * (N : ℝ))) ^ (2 * (k + 1) + A)) := by ring
    _ ≤ 36 * (4 * C) * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
      scaled_grid_count_budget_le k A N (by positivity) hNR hlog
    _ = 144 * C * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by ring

/-- A single stronger fixed accuracy, chosen before epsilon and before
`N`, absorbs every selected cell and the complete two-prefix cost. This
is an unconditional numerical budget, not an analytic error hypothesis. -/
theorem eventually_actualGrid_scaled_accuracy_negligible (k : ℕ)
    {C : ℝ} (hC : 0 ≤ C) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ num den : ℕ, ∀ T : ℝ,
        ((actualGridIntersectingIndices num den N T
          (1 + boundaryLogMesh k N)).card : ℝ) *
          (4 * (C * (4 * (N : ℝ)) /
            (Real.log (4 * (N : ℝ))) ^ (2 * (k + 1) + 3))) ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards [eventually_actualGrid_scaled_accuracy_budget k 3 hC,
    eventually_boundaryLogMesh_main_le_singularNormalization (144 * C)
      (k := 5) (by norm_num) epsilon hepsilon,
    eventually_one_le_nat_log] with N hbudget hsmall hlog
  intro num den T
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  calc
    _ ≤ 144 * C * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 := hbudget num den T
    _ = (144 * C) * boundaryLogMesh 5 N * (N : ℝ) *
        (Real.log (N : ℝ)) ^ 2 := by
      unfold boundaryLogMesh
      field_simp [hlogpos.ne'] <;> ring
    _ ≤ epsilon * singularNormalization N := hsmall

end

end ImbalancedChen
