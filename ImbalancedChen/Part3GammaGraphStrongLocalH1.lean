import ImbalancedChen.Part3GammaGraphLocalGradientLinear

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native actual graph convergence yields STRONG ordinary local H1
convergence on every fixed open positive rectangle. The proof applies
the genuinely constructed bounded linear local-gradient map to graph
differences, not a fresh weak-subsequence extraction. A quantitative
Lipschitz bound and uniqueness against every local weak witness are
included. The graph norm is the inherited product max norm. -/

namespace ImbalancedChen.Part3.GammaGraphStrongLocalH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open ProductConvolutionSecondDerivatives20261026a RestrictedL2WeakDerivative20261026b
open GammaGraphLocalGradientLinear20261026b

theorem graphGradientCLM_opNorm_le (N : ℕ) [NeZero N] (r : PositiveRectangle) :
    ‖graphGradientCLM N r‖≤Real.sqrt (2*graphGradientConstant N r) :=
  (graphGradientCLM N r).opNorm_le_bound (Real.sqrt_nonneg _)
    (fun p => (chosenGraphGradient_spec N r p).1)

/-- Any other pair of local weak derivatives agrees as actual local L2
classes with the selected map, so the construction is choice independent. -/
theorem graphGradient_eq_any_weak_witness (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (p : ActualGraph N) (G : LocalGradientPair r)
    (hx : HasRestrictedDerivative r.region (graphValueCLM N r p) G.1 xDirection)
    (hy : HasRestrictedDerivative r.region (graphValueCLM N r p) G.2 yDirection) :
    graphGradientCLM N r p=G := by
  apply Prod.ext
  · exact restricted_derivative_unique r.region_open (chosenGraphGradient_spec N r p).2.1 hx
  · exact restricted_derivative_unique r.region_open (chosenGraphGradient_spec N r p).2.2 hy

/-- The explicit local elliptic constant controls differences of actual
native graph pairs, hence controls strong local gradient convergence. -/
theorem graphGradient_difference_le (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (p q : ActualGraph N) :
    ‖graphGradientCLM N r p-graphGradientCLM N r q‖≤
      Real.sqrt (2*graphGradientConstant N r)*
        max ‖p.val.1-q.val.1‖ ‖p.val.2-q.val.2‖ := by
  calc
    _ = ‖graphGradientCLM N r (p-q)‖ := by rw [map_sub]
    _ ≤ Real.sqrt (2*graphGradientConstant N r)*‖p-q‖ :=
      (chosenGraphGradient_spec N r (p-q)).1
    _ = _ := rfl

def graphLocalH1CLM (N : ℕ) [NeZero N] (r : PositiveRectangle) :
    ActualGraph N →L[ℂ] (LocalL2 r.region × LocalGradientPair r) :=
  (graphValueCLM N r).prod (graphGradientCLM N r)

theorem graph_input_output_tendsto_strong_localH1 (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (p : ℕ → ActualGraph N) (q : ActualGraph N)
    (hinput : Tendsto (fun n => (p n).val.1) atTop (𝓝 q.val.1))
    (houtput : Tendsto (fun n => (p n).val.2) atTop (𝓝 q.val.2)) :
    Tendsto (fun n => graphLocalH1CLM N r (p n)) atTop (𝓝 (graphLocalH1CLM N r q)) := by
  have hgraph : Tendsto p atTop (𝓝 q) :=
    tendsto_subtype_rng.2 (hinput.prodMk_nhds houtput)
  exact ((graphLocalH1CLM N r).continuous.tendsto q).comp hgraph

theorem graph_input_output_tendsto_strong_local_gradient (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (p : ℕ → ActualGraph N) (q : ActualGraph N)
    (hinput : Tendsto (fun n => (p n).val.1) atTop (𝓝 q.val.1))
    (houtput : Tendsto (fun n => (p n).val.2) atTop (𝓝 q.val.2)) :
    Tendsto (fun n => graphGradientCLM N r (p n)) atTop (𝓝 (graphGradientCLM N r q)) := by
  have hgraph : Tendsto p atTop (𝓝 q) :=
    tendsto_subtype_rng.2 (hinput.prodMk_nhds houtput)
  exact ((graphGradientCLM N r).continuous.tendsto q).comp hgraph

/-- Explicit actual inputs and outputs may be used directly, without
the caller supplying a graph-subtype convergence proof. -/
theorem actual_graph_pair_convergence_strong_localH1 (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (f w : ℕ → QuotientL2 N) (f₀ w₀ : QuotientL2 N)
    (hgraph : ∀ n,(f n,w n)∈(actualClosedGammaMaass N).graph)
    (hgraph₀ : (f₀,w₀)∈(actualClosedGammaMaass N).graph)
    (hf : Tendsto f atTop (𝓝 f₀)) (hw : Tendsto w atTop (𝓝 w₀)) :
    Tendsto (fun n => graphLocalH1CLM N r ⟨(f n,w n),hgraph n⟩) atTop
      (𝓝 (graphLocalH1CLM N r ⟨(f₀,w₀),hgraph₀⟩)) :=
  graph_input_output_tendsto_strong_localH1 N r
    (fun n => ⟨(f n,w n),hgraph n⟩) ⟨(f₀,w₀),hgraph₀⟩ hf hw

end
end ImbalancedChen.Part3.GammaGraphStrongLocalH120261026b
