import ImbalancedChen.Part3OriginalPositiveOrbitProduct

/-! The height goes to infinity with the ratio window fixed. All three
positive profiles have the same small-argument price, including before
either limit. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
open Set Filter MeasureTheory Complex
open scoped BigOperators Topology
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalPositiveHeightTest20261112 (original)
open OriginalPositiveRatioWindows20261112 (unit unit_mass ratio)
open OriginalPositiveStrip20261112 (residual)

theorem original_pointwise (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (n : ℕ)
    {q : ℝ} (hq : 0<q) :
    Tendsto (fun R : ℝ => induced (original ell hY R n) q) atTop
      (𝓝 (response (ratio ell hY n) q)) := by
  obtain ⟨A,hA,price⟩ := uniform_response_price ell hY
  let H := ratio ell hY n
  have I := unit.smooth.continuous.integrable_of_hasCompactSupport unit.compact
  have lim : Tendsto (fun R : ℝ => ∫ l : ℝ,unit.function l*sample H R q l) atTop
      (𝓝 (∫ l : ℝ,unit.function l*response H q)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun l : ℝ => ‖unit.function l‖*(A*q))
    · exact Eventually.of_forall (fun R => unit.smooth.continuous.aestronglyMeasurable.mul
        (sample_measurable H R q).aestronglyMeasurable)
    · exact Eventually.of_forall (fun R => ae_of_all _ fun l => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (sample_price H (price n) R hq l hA) (norm_nonneg _))
    · exact I.norm.mul_const _
    · exact ae_of_all _ fun l => (sample_limit H hq l).const_mul (unit.function l)
  simpa only [original,induced_formula _ _ _ hq,integral_mul_const,unit_mass,one_mul,H] using lim

theorem joint_price (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ B : ℝ,0≤B ∧
      (∀ (n : ℕ) (R q : ℝ),0<q → ‖induced (original ell hY R n) q‖≤B*q) ∧
      (∀ (n : ℕ) (q : ℝ),0<q → ‖response (ratio ell hY n) q‖≤B*q) ∧
      (∀ q : ℝ,0<q → ‖residual ell Y q‖≤B*q) := by
  obtain ⟨A,hA,price⟩ := uniform_response_price ell hY
  let M := ∫ l : ℝ,‖unit.function l‖
  have hM : 0≤M := integral_nonneg (fun _ => norm_nonneg _)
  let B := (M+1)*A
  have AB : A≤B := by dsimp only [B]; nlinarith only [mul_nonneg hM hA]
  have MB : M*A≤B := by dsimp only [B]; nlinarith only [hA]
  have hw (n : ℕ) {q : ℝ} (hq : 0<q) : ‖response (ratio ell hY n) q‖≤B*q :=
    (price n q hq).trans (mul_le_mul_of_nonneg_right AB hq.le)
  refine ⟨B,hA.trans AB,?_,fun n _ hq => hw n hq,fun q hq => ?_⟩
  · intro n R q hq
    rw [original,induced_formula _ _ _ hq]
    calc
      _ ≤ ∫ l : ℝ,‖unit.function l‖*(A*q) := by
        apply norm_integral_le_of_norm_le
          ((unit.smooth.continuous.integrable_of_hasCompactSupport unit.compact).norm.mul_const _)
        exact ae_of_all _ fun l => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (sample_price _ (price n) R hq l hA) (norm_nonneg _)
      _ = M*A*q := by rw [integral_mul_const]; dsimp only [M]; ring
      _ ≤ B*q := mul_le_mul_of_nonneg_right MB hq.le
  · exact le_of_tendsto (response_limit ell hY hq.le).norm (Eventually.of_forall fun n => hw n hq)

end ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
end
