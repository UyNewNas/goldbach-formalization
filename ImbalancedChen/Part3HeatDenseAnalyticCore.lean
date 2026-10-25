import ImbalancedChen.Part3NativeOperatorPowersHeatSmoothing
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Positive-time heat vectors are analytic for the genuine native operator:
all native powers exist, and their factorial power series is absolutely
summable with explicit positive radius s/2. The proof uses the internally
proved n!s^-n operator bounds and a geometric series, not an analytic-vector
premise. Strong heat convergence proves density. Commutation with the
actual resolvent preserves the native graph; smoothing both coordinates
then proves that these analytic vectors form a genuine dense graph core.
-/

namespace ImbalancedChen.Part3.HeatDenseAnalyticCore20261025a
noncomputable section
open Set Filter Topology
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.GenericPositiveResolventHeatGenerator20261025a
open ImbalancedChen.Part3.GenericHeatAllPowersCalculus20261025a
open ImbalancedChen.Part3.NativeOperatorPowersHeatSmoothing20261025a
open ImbalancedChen.Part3.GenericFriedrichsOperator20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The classical absolute factorial-series criterion, with every term
required to be the actual value of the corresponding native power. -/
def IsAnalyticVector (A : H →ₗ.[ℂ] H) (u : H) : Prop :=
  ∃ w : ℕ → H, w 0 = u ∧
    (∀ n : ℕ, (u, w n) ∈ (nativePower A n).graph) ∧
      ∃ r : ℝ, 0 < r ∧ Summable (fun n : ℕ => r ^ n * ‖w n‖ / (n.factorial : ℝ))

variable (D : ResolventData H)

theorem heat_factorial_series_summable {s : ℝ} (hs : 0 < s) (f : H) :
    Summable (fun n : ℕ => (s / 2) ^ n * ‖heatPowerOperator D s n f‖ / (n.factorial : ℝ)) := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖f‖) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_right ‖f‖
  apply hgeom.of_nonneg_of_le
  · intro n
    exact div_nonneg
      (mul_nonneg (pow_nonneg (half_pos hs).le n) (norm_nonneg _)) (Nat.cast_nonneg _)
  · intro n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hnorm := heatPowerOperator_norm_le D hs n f
    calc
      _ ≤ (s / 2) ^ n * (((n.factorial : ℝ) / s ^ n) * ‖f‖) / (n.factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnorm (pow_nonneg (half_pos hs).le n)) hfac.le
      _ = (1 / 2 : ℝ) ^ n * ‖f‖ := by
        simp only [div_pow, one_pow]
        field_simp [hs.ne', hfac.ne']
        <;> ring

/-- No analytic-vector estimate is supplied: the positive radius and
absolute power-series convergence are consequences of the true bounds. -/
theorem heat_isAnalyticVector {s : ℝ} (hs : 0 < s) (f : H) :
    IsAnalyticVector (friedrichsR D.R) (heatOperator D s f) := by
  refine ⟨fun n => heatPowerOperator D s n f, ?_, ?_, s / 2, half_pos hs, ?_⟩
  · exact congrArg (fun B : H →L[ℂ] H => B f) (heatPowerOperator_zero_order D hs)
  · intro n
    exact heat_mem_nativePower_graph D hs n f
  · exact heat_factorial_series_summable D hs f

theorem dense_analyticVectors : Dense {u : H | IsAnalyticVector (friedrichsR D.R) u} := by
  intro f
  apply mem_closure_of_tendsto (tendsto_heatOperator_at_zero D f)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact heat_isAnalyticVector D hs f

/-- The genuine heat operator preserves the actual native graph, with
commuting action on its input and output coordinates. -/
theorem heat_preserves_native_graph (s : ℝ) {u v : H}
    (huv : (u, v) ∈ (friedrichsR D.R).graph) :
    (heatOperator D s u, heatOperator D s v) ∈ (friedrichsR D.R).graph := by
  have hR := (friedrichsR_mem_graph_iff D.R D.injective).1 huv
  apply (friedrichsR_mem_graph_iff D.R D.injective).2
  rw [← (heatOperator D s).map_add u v, ← heatOperator_resolvent_apply D s, hR]

def analyticGraph (A : H →ₗ.[ℂ] H) : Set (H × H) :=
  {p | p ∈ A.graph ∧ IsAnalyticVector A p.1}

/-- Density in the actual operator graph, not merely in the ambient
Hilbert space. Both coordinates are smoothed and converge strongly. -/
theorem native_graph_mem_closure_analyticGraph {u v : H}
    (huv : (u, v) ∈ (friedrichsR D.R).graph) :
    (u, v) ∈ closure (analyticGraph (friedrichsR D.R)) := by
  apply mem_closure_of_tendsto
    ((tendsto_heatOperator_at_zero D u).prodMk_nhds (tendsto_heatOperator_at_zero D v))
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ⟨heat_preserves_native_graph D s huv, heat_isAnalyticVector D hs u⟩

/-- The analytic vectors therefore form a genuine graph core for the
native self-adjoint Friedrichs operator built from the actual resolvent. -/
theorem closure_analyticGraph_eq_nativeGraph :
    closure (analyticGraph (friedrichsR D.R)) =
      ((friedrichsR D.R).graph : Set (H × H)) := by
  have hclosed := friedrichsR_isClosed D.R D.injective
  change IsClosed ((friedrichsR D.R).graph : Set (H × H)) at hclosed
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hp => hp.1) hclosed
  · rintro ⟨u, v⟩ huv
    exact native_graph_mem_closure_analyticGraph D huv

end
end ImbalancedChen.Part3.HeatDenseAnalyticCore20261025a
