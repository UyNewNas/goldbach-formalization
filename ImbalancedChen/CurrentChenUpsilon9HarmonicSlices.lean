import ImbalancedChen.CurrentChenUpsilon9HarmonicMean

/-!
# Actual slices of the ninth harmonic integral

The original mixed affine domain is exactly the moving half-open slice,
with no arithmetic wall deleted.  Compact-cube integrability and the
volume-preserving two-coordinate equivalence pay the genuine Fubini step.
The logarithmic antiderivative is deliberately a separate subsequent step.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Classical

theorem currentChenUpsilon9HarmonicDomain_vec_iff (x y : ℝ) :
    ![x, y] ∈ logPrimeBox (fun _ : Fin 2 => (19 / 125 : ℝ))
        (fun _ => (1 / 2 : ℝ)) ∩ currentChenUpsilon9HarmonicRegion ↔
      x ∈ Ico (19 / 125 : ℝ) (59 / 250 : ℝ) ∧
        y ∈ Ico (59 / 250 : ℝ) ((1 - x) / 2) := by
  constructor
  · rintro ⟨hbox, hregion⟩
    have hx := mem_logPrimeBox.mp hbox (0 : Fin 2)
    change 19 / 125 ≤ x ∧ x < (1 / 2 : ℝ) at hx
    change x < 59 / 250 ∧ 59 / 250 ≤ y ∧ x + 2 * y < 1 at hregion
    exact ⟨⟨hx.1, hregion.1⟩, ⟨hregion.2.1, by linarith only [hregion.2.2]⟩⟩
  · rintro ⟨hx, hy⟩
    refine ⟨mem_logPrimeBox.mpr ?_, ?_⟩
    · intro i
      fin_cases i
      · change 19 / 125 ≤ x ∧ x < (1 / 2 : ℝ)
        exact ⟨hx.1, by linarith only [hx.2]⟩
      · change 19 / 125 ≤ y ∧ y < (1 / 2 : ℝ)
        constructor <;> linarith only [hx.1, hy.1, hy.2]
    · change x < 59 / 250 ∧ 59 / 250 ≤ y ∧ x + 2 * y < 1
      exact ⟨hx.2, hy.1, by linarith only [hy.2]⟩

theorem currentChenUpsilon9HarmonicIntegrand_vec {x y : ℝ}
    (hxy : ![x, y] ∈ logPrimeBox (fun _ : Fin 2 => (19 / 125 : ℝ))
        (fun _ => (1 / 2 : ℝ)) ∩ currentChenUpsilon9HarmonicRegion) :
    currentChenUpsilon9HarmonicKernel ![x, y] * (∏ i, 1 / (![x, y] i)) =
      1 / (x * y * (1 - x - y)) := by
  rw [currentChenUpsilon9HarmonicKernel_eq hxy.2]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_div, mul_inv_rev]
  ring

theorem integrableOn_currentChenUpsilon9HarmonicIntegrand :
    IntegrableOn (fun x : Fin 2 → ℝ => currentChenUpsilon9HarmonicKernel x * ∏ i, 1 / x i)
      (logPrimeBox (fun _ : Fin 2 => (19 / 125 : ℝ)) (fun _ => (1 / 2 : ℝ)) ∩
        currentChenUpsilon9HarmonicRegion) := by
  exact (integrableOn_logPrimeBox_test_cube (by norm_num : (0 : ℝ) < 19 / 125)
    currentChenUpsilon9HarmonicKernel
    continuous_currentChenUpsilon9HarmonicKernel.continuousOn).mono_set inter_subset_left

/-- Fubini on the genuine two-dimensional Lebesgue integral.  Every lower
and upper endpoint is retained as a half-open interval in the exact slice. -/
theorem currentChenUpsilon9HarmonicIntegral_eq_nested :
    currentChenUpsilon9HarmonicIntegral =
      ∫ x in Ico (19 / 125 : ℝ) (59 / 250 : ℝ),
        ∫ y in Ico (59 / 250 : ℝ) ((1 - x) / 2),
          1 / (x * y * (1 - x - y)) := by
  let S := logPrimeBox (fun _ : Fin 2 => (19 / 125 : ℝ)) (fun _ => (1 / 2 : ℝ)) ∩
    currentChenUpsilon9HarmonicRegion
  let G := fun x : Fin 2 → ℝ => currentChenUpsilon9HarmonicKernel x * ∏ i, 1 / x i
  let F := S.indicator G
  have hS : MeasurableSet S :=
    (measurableSet_logPrimeBox _ _).inter measurableSet_currentChenUpsilon9HarmonicRegion
  have hF : Integrable F :=
    integrableOn_currentChenUpsilon9HarmonicIntegrand.integrable_indicator hS
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hPF : Integrable (fun p : ℝ × ℝ => F (E.symm p)) :=
    (hE.symm.integrable_comp_emb E.symm.measurableEmbedding).mpr hF
  have hvec (x y : ℝ) : E.symm (x, y) = ![x, y] := by
    ext i
    fin_cases i <;> rfl
  have hpoint (x y : ℝ) : F ![x, y] =
      (Ico (19 / 125 : ℝ) (59 / 250 : ℝ)).indicator
        (fun x => (Ico (59 / 250 : ℝ) ((1 - x) / 2)).indicator
          (fun y => 1 / (x * y * (1 - x - y))) y) x := by
    change S.indicator G ![x, y] = _
    by_cases hx : x ∈ Ico (19 / 125 : ℝ) (59 / 250 : ℝ)
    · by_cases hy : y ∈ Ico (59 / 250 : ℝ) ((1 - x) / 2)
      · have hxy : ![x, y] ∈ S := (currentChenUpsilon9HarmonicDomain_vec_iff x y).mpr ⟨hx, hy⟩
        rw [indicator_of_mem hxy, indicator_of_mem hx, indicator_of_mem hy]
        exact currentChenUpsilon9HarmonicIntegrand_vec hxy
      · have hxy : ![x, y] ∉ S := fun hxy =>
          hy ((currentChenUpsilon9HarmonicDomain_vec_iff x y).mp hxy).2
        rw [indicator_of_notMem hxy, indicator_of_mem hx, indicator_of_notMem hy]
    · have hxy : ![x, y] ∉ S := fun hxy =>
        hx ((currentChenUpsilon9HarmonicDomain_vec_iff x y).mp hxy).1
      rw [indicator_of_notMem hxy, indicator_of_notMem hx]
  calc
    currentChenUpsilon9HarmonicIntegral = ∫ t, F t := (integral_indicator hS).symm
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, F (E.symm (x, y)) := integral_prod _ hPF
    _ = ∫ x : ℝ, ∫ y : ℝ, F ![x, y] := by simp only [hvec]
    _ = ∫ x : ℝ, (Ico (19 / 125 : ℝ) (59 / 250 : ℝ)).indicator
        (fun x => ∫ y in Ico (59 / 250 : ℝ) ((1 - x) / 2),
          1 / (x * y * (1 - x - y))) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Ico (19 / 125 : ℝ) (59 / 250 : ℝ)
      · rw [indicator_of_mem hx]
        simp_rw [hpoint, indicator_of_mem hx]
        exact integral_indicator measurableSet_Ico
      · rw [indicator_of_notMem hx]
        simp_rw [hpoint, indicator_of_notMem hx]
        exact integral_zero ℝ ℝ
    _ = _ := integral_indicator measurableSet_Ico

end

end ImbalancedChen
