import ImbalancedChen.Part3ClosedHorizontalCuspTail

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Finite-cusp uniform tail tightness for actual closed horizontal graphs. The
only family input is a bound on the sum of physical horizontal energies.
The graph estimates and a common height are proved, not supplied. This does
not identify the finite collection with a quotient cusp decomposition and
does not prove local Rellich compactness or an automorphic discrete spectrum.
-/

noncomputable section
namespace ImbalancedChen.Part3.FiniteCuspTailTightness20261026a

open ImbalancedChen.Part3.ClosedHorizontalCuspTail20261026a

/-- Widths bounded by W give one sharp common coefficient for a finite family. -/
theorem finite_cusp_tail_bound {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) {a Y W : ℝ} (hY : 0 < Y) (haY : a ≤ Y)
    (hw : ∀ i ∈ s, 0 < w i) (hwW : ∀ i ∈ s, w i ≤ W)
    (u : ι → FunctionL2 a) (d : ι → DerivativeL2 a)
    (hgraph : ∀ i ∈ s, (u i, d i) ∈ closedHorizontalGraph (w i) a) :
    (∑ i ∈ s, ‖tailRestriction a Y haY (u i)‖ ^ 2) ≤
      (W ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * ∑ i ∈ s, ‖d i‖ ^ 2 := by
  calc
    _ ≤ ∑ i ∈ s, (w i ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * ‖d i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact closed_horizontal_tail_bound (hw i hi) hY haY (hgraph i hi)
    _ ≤ ∑ i ∈ s, (W ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * ‖d i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hW : 0 ≤ W := le_trans (hw i hi).le (hwW i hi)
      have hsquare : w i ^ 2 ≤ W ^ 2 :=
        (sq_le_sq₀ (hw i hi).le hW).mpr (hwW i hi)
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hsquare (by positivity)) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A common bound for the sum of physical horizontal energies. -/
theorem finite_cusp_tail_bound_of_energy {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) {a Y W E : ℝ} (hY : 0 < Y) (haY : a ≤ Y)
    (hw : ∀ i ∈ s, 0 < w i) (hwW : ∀ i ∈ s, w i ≤ W)
    (u : ι → FunctionL2 a) (d : ι → DerivativeL2 a)
    (hgraph : ∀ i ∈ s, (u i, d i) ∈ closedHorizontalGraph (w i) a)
    (henergy : (∑ i ∈ s, ‖d i‖ ^ 2) ≤ E) :
    (∑ i ∈ s, ‖tailRestriction a Y haY (u i)‖ ^ 2) ≤
      (W ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * E :=
  (finite_cusp_tail_bound s w hY haY hw hwW u d hgraph).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity))

/-- One explicit choice of height works for every family in an energy ball.
The height is chosen before the functions and their derivative witnesses. -/
theorem finite_cusp_uniform_tail_tightness {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a W E : ℝ) (hE : 0 ≤ E)
    (hw : ∀ i ∈ s, 0 < w i) (hwW : ∀ i ∈ s, w i ≤ W)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Y : ℝ) (haY : a ≤ Y), 0 < Y ∧
      ∀ (u : ι → FunctionL2 a) (d : ι → DerivativeL2 a),
        (∀ i ∈ s, (u i, d i) ∈ closedHorizontalGraph (w i) a) →
        (∑ i ∈ s, ‖d i‖ ^ 2) ≤ E →
        (∑ i ∈ s, ‖tailRestriction a Y haY (u i)‖ ^ 2) < ε := by
  let B : ℝ := W ^ 2 * E / (4 * Real.pi ^ 2)
  let Y : ℝ := max a (max 1 (B / ε + 1))
  have haY : a ≤ Y := le_max_left _ _
  have h1Y : 1 ≤ Y := (le_max_left _ _).trans (le_max_right _ _)
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one h1Y
  have hBY : B / ε + 1 ≤ Y := (le_max_right _ _).trans (le_max_right _ _)
  have hBE : B < ε * Y := by
    have hlt : B / ε < Y := by linarith
    exact ((div_lt_iff₀ hε).mp hlt).trans_eq (mul_comm Y ε)
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  have hsmall : (W ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * E < ε := by
    have hdiv : B / Y ^ 2 < ε := (div_lt_iff₀ (sq_pos_of_pos hY)).mpr
      (hBE.trans_le (mul_le_mul_of_nonneg_left hYY hε.le))
    convert hdiv using 1
    dsimp [B]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  refine ⟨Y, haY, hY, ?_⟩
  intro u d hg he
  exact (finite_cusp_tail_bound_of_energy s w hY haY hw hwW u d hg he).trans_lt hsmall

end ImbalancedChen.Part3.FiniteCuspTailTightness20261026a
