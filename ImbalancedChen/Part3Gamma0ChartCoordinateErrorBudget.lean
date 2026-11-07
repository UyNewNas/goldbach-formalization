import ImbalancedChen.Part3Gamma0QuotientChartReconstruction
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual inverse-class SL(2,Z) chart coordinates preserve the canonical
hyperbolic measure. This converts the proved genuine quotient finite
partition reconstruction error into a sum of local physical chart errors
on the SAME truncated modular cell. The finite class/index factor is
retained exactly. The global tail is left as the genuine quotient tail;
no finite-cusp identification, energy-domain equality, or global Rellich
embedding is inferred from this chart-coordinate theorem.
-/

namespace ImbalancedChen.Part3.Gamma0ChartCoordinateErrorBudget20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators ENNReal
open Gamma0FiniteChartReconstruction20261026b
open Gamma0QuotientChartReconstruction20261026b
open Gamma0QuotientCellPushforward20261025a

theorem chartCoordinate_measurePreserving (N : ℕ) [NeZero N] (i : ChartIndex N) :
    MeasurePreserving (chartCoordinate N i)
      (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane) := by
  change MeasurePreserving
    (fun z : UpperHalfPlane =>
      (Matrix.SpecialLinearGroup.mapGL ℝ (chartMatrix N i)⁻¹) • z) volume volume
  exact measurePreserving_smul _ _

theorem chartCoordinate_measurableEmbedding (N : ℕ) [NeZero N] (i : ChartIndex N) :
    MeasurableEmbedding (chartCoordinate N i) := by
  change MeasurableEmbedding
    (fun z : UpperHalfPlane =>
      (Matrix.SpecialLinearGroup.mapGL ℝ (chartMatrix N i)⁻¹) • z)
  exact measurableEmbedding_const_smul _

/-- No integrability or measurability premise on the chart error is needed:
the actual action is a measure-preserving measurable embedding. -/
theorem actual_chart_square_error_change_variables (N : ℕ) [NeZero N] (Y : ℝ)
    (i : ChartIndex N) (f v : UpperHalfPlane → ℂ) :
    (∫⁻ z in rawChartCell N Y i,
      ENNReal.ofReal (‖f z - v (chartCoordinate N i z)‖ ^ 2)) =
      ∫⁻ w in truncatedModularCell Y,
        ENNReal.ofReal (‖f (chartMatrix N i • w) - v w‖ ^ 2) := by
  have h := (chartCoordinate_measurePreserving N i).setLIntegral_comp_preimage_emb
    (chartCoordinate_measurableEmbedding N i)
    (fun w => ENNReal.ofReal (‖f (chartMatrix N i • w) - v w‖ ^ 2))
    (truncatedModularCell Y)
  simpa only [rawChartCell, chartCoordinate, smul_inv_smul] using h

/-- Finite quotient reconstruction is controlled by actual chart pullback
errors in the original dx dy/y² normalization. -/
theorem quotient_core_error_le_actual_chart_errors (N : ℕ) [NeZero N] (Y : ℝ)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i)) :
    (∫⁻ q in quotientCore N Y,
      ENNReal.ofReal (‖F q - quotientReconstruct N Y v q‖ ^ 2)
        ∂carrierPushforward N) ≤
      ∑ i : ChartIndex N, ∫⁻ w in truncatedModularCell Y,
        ENNReal.ofReal
          (‖F (orbitProjection N (chartMatrix N i • w)) - v i w‖ ^ 2) := by
  have h := quotient_reconstruction_square_error_budget N Y F hF v hv
  simpa only [actual_chart_square_error_change_variables] using h

/-- Uniform per-chart errors have exactly the genuine finite Gamma0 index
cost. The arithmetic index is not replaced by the number of named cusps. -/
theorem quotient_core_error_le_index_mul (N : ℕ) [NeZero N] (Y : ℝ)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i))
    (ε : ℝ≥0∞)
    (he : ∀ i : ChartIndex N, (∫⁻ w in truncatedModularCell Y,
      ENNReal.ofReal
        (‖F (orbitProjection N (chartMatrix N i • w)) - v i w‖ ^ 2)) ≤ ε) :
    (∫⁻ q in quotientCore N Y,
      ENNReal.ofReal (‖F q - quotientReconstruct N Y v q‖ ^ 2)
        ∂carrierPushforward N) ≤
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ε := by
  apply (quotient_core_error_le_actual_chart_errors N Y F hF v hv).trans
  calc
    _ ≤ ∑ _i : ChartIndex N, ε := Finset.sum_le_sum (fun i _ => he i)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, chartIndex_card]

/-- The final global error budget retains the actual quotient complement.
Proving its uniform smallness for the all-cusps true zero-mode family is
a separate genuine geometric/energy obligation. -/
theorem global_error_le_actual_chart_errors_add_tail (N : ℕ) [NeZero N] (Y : ℝ)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i)) :
    (∫⁻ q, ENNReal.ofReal (‖F q - quotientReconstruct N Y v q‖ ^ 2)
        ∂carrierPushforward N) ≤
      (∑ i : ChartIndex N, ∫⁻ w in truncatedModularCell Y,
        ENNReal.ofReal
          (‖F (orbitProjection N (chartMatrix N i • w)) - v i w‖ ^ 2)) +
      ∫⁻ q in (quotientCore N Y)ᶜ, ENNReal.ofReal (‖F q‖ ^ 2)
        ∂carrierPushforward N := by
  have h := global_reconstruction_square_error_budget N Y F hF v hv
  simpa only [actual_chart_square_error_change_variables] using h

end
end ImbalancedChen.Part3.Gamma0ChartCoordinateErrorBudget20261026b
