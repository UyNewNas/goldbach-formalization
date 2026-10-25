import ImbalancedChen.Part3MaassFiniteCoreL2LinearOperator
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Algebra.Module.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The topological closure of the actual finite Maass L² graph is a closed
submodule of H × H. Genuine Green symmetry, nonnegativity and shifted
coercivity extend to this closure by continuity. In particular a null-input
graph limit annihilates every actual finite compact test. No density
premise or assertion of single-valuedness of the closed relation is made.
The missing actual-domain density theorem is needed to conclude closability.
-/

namespace ImbalancedChen.Part3.MaassFiniteCoreGraphClosure20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2Symmetry20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a

def actualFiniteGraphSubmodule : Submodule ℂ (HyperbolicL2 × HyperbolicL2) where
  carrier := finiteTensorL2Graph
  zero_mem' := finiteTensorL2Graph_zero
  add_mem' := by
    intro p q hp hq
    exact finiteTensorL2Graph_add hp hq
  smul_mem' := by
    intro c p hp
    exact finiteTensorL2Graph_smul c hp

/-- The actual topological graph closure; at this stage it is a closed
linear relation and is not yet claimed to be the graph of an operator. -/
def closedTensorGraph : Submodule ℂ (HyperbolicL2 × HyperbolicL2) :=
  actualFiniteGraphSubmodule.topologicalClosure

theorem mem_closedTensorGraph_iff (p : HyperbolicL2 × HyperbolicL2) :
    p ∈ closedTensorGraph ↔ p ∈ closure finiteTensorL2Graph := Iff.rfl

theorem isClosed_closedTensorGraph :
    IsClosed (closedTensorGraph : Set (HyperbolicL2 × HyperbolicL2)) :=
  actualFiniteGraphSubmodule.isClosed_topologicalClosure

theorem actualGraph_mem_closedTensorGraph {p : HyperbolicL2 × HyperbolicL2}
    (hp : p ∈ finiteTensorL2Graph) : p ∈ closedTensorGraph :=
  subset_closure hp

/-- The true Green test identity survives topological graph limits.
The test pair lies in the actual compact core, without a test identity premise. -/
theorem closedTensorGraph_core_weak_pairing {f g u v : HyperbolicL2}
    (hfg : (f, g) ∈ closedTensorGraph) (huv : (u, v) ∈ finiteTensorL2Graph) :
    inner ℂ g u = inner ℂ f v := by
  have hclosed : IsClosed {p : HyperbolicL2 × HyperbolicL2 |
      inner ℂ p.2 u = inner ℂ p.1 v} :=
    isClosed_eq (continuous_snd.inner continuous_const)
      (continuous_fst.inner continuous_const)
  have hsub : finiteTensorL2Graph ⊆ {p : HyperbolicL2 × HyperbolicL2 |
      inner ℂ p.2 u = inner ℂ p.1 v} := by
    intro p hp
    exact finiteTensorL2Graph_symmetric hp huv
  exact (closure_minimal hsub hclosed) hfg

/-- Symmetry extends in both graph variables. This is symmetry of a
closed relation; it does not supply uniqueness of its output coordinate. -/
theorem closedTensorGraph_symmetric {f g u v : HyperbolicL2}
    (hfg : (f, g) ∈ closedTensorGraph) (huv : (u, v) ∈ closedTensorGraph) :
    inner ℂ g u = inner ℂ f v := by
  have hclosed : IsClosed {p : HyperbolicL2 × HyperbolicL2 |
      inner ℂ g p.1 = inner ℂ f p.2} :=
    isClosed_eq (continuous_const.inner continuous_fst)
      (continuous_const.inner continuous_snd)
  have hsub : finiteTensorL2Graph ⊆ {p : HyperbolicL2 × HyperbolicL2 |
      inner ℂ g p.1 = inner ℂ f p.2} := by
    intro p hp
    exact closedTensorGraph_core_weak_pairing hfg hp
  exact (closure_minimal hsub hclosed) huv

theorem closedTensorGraph_nonneg {f g : HyperbolicL2}
    (hfg : (f, g) ∈ closedTensorGraph) : 0 ≤ (inner ℂ f g).re := by
  have hclosed : IsClosed {p : HyperbolicL2 × HyperbolicL2 |
      0 ≤ (inner ℂ p.1 p.2).re} :=
    isClosed_le continuous_const
      (Complex.continuous_re.comp (continuous_fst.inner continuous_snd))
  have hsub : finiteTensorL2Graph ⊆ {p : HyperbolicL2 × HyperbolicL2 |
      0 ≤ (inner ℂ p.1 p.2).re} := by
    intro p hp
    exact finiteTensorL2Graph_nonneg hp
  exact (closure_minimal hsub hclosed) hfg

theorem closedTensorGraph_shifted_coercive {f g : HyperbolicL2}
    (hfg : (f, g) ∈ closedTensorGraph) :
    ‖f‖ ^ 2 ≤ (inner ℂ f (f + g)).re := by
  have hclosed : IsClosed {p : HyperbolicL2 × HyperbolicL2 |
      ‖p.1‖ ^ 2 ≤ (inner ℂ p.1 (p.1 + p.2)).re} :=
    isClosed_le (continuous_fst.norm.pow 2)
      (Complex.continuous_re.comp
        (continuous_fst.inner (continuous_fst.add continuous_snd)))
  have hsub : finiteTensorL2Graph ⊆ {p : HyperbolicL2 × HyperbolicL2 |
      ‖p.1‖ ^ 2 ≤ (inner ℂ p.1 (p.1 + p.2)).re} := by
    intro p hp
    exact finiteTensorL2Graph_shifted_coercive hp
  exact (closure_minimal hsub hclosed) hfg

/-- The exact null-input obstruction: every possible vertical fiber of
the closed graph is orthogonal to all actual finite compact test inputs. -/
theorem closedTensorGraph_zero_input_annihilates_actualDomain {g : HyperbolicL2}
    (hg : ((0 : HyperbolicL2), g) ∈ closedTensorGraph) (u : actualTensorDomain) :
    inner ℂ g (u : HyperbolicL2) = 0 := by
  simpa only [inner_zero_left] using
    closedTensorGraph_core_weak_pairing hg (actualTensorLaplacian_mem_graph u)

theorem mem_closedTensorGraph_of_tendsto {F G : ℕ → HyperbolicL2} {f g : HyperbolicL2}
    (hgraph : ∀ n, (F n, G n) ∈ finiteTensorL2Graph)
    (hF : Filter.Tendsto F Filter.atTop (nhds f))
    (hG : Filter.Tendsto G Filter.atTop (nhds g)) :
    (f, g) ∈ closedTensorGraph :=
  isClosed_closedTensorGraph.mem_of_tendsto (hF.prodMk_nhds hG)
    (Filter.Eventually.of_forall fun n => actualGraph_mem_closedTensorGraph (hgraph n))

theorem null_input_limit_annihilates_actualDomain {F G : ℕ → HyperbolicL2}
    {g : HyperbolicL2} (hgraph : ∀ n, (F n, G n) ∈ finiteTensorL2Graph)
    (hF : Filter.Tendsto F Filter.atTop (nhds 0))
    (hG : Filter.Tendsto G Filter.atTop (nhds g)) (u : actualTensorDomain) :
    inner ℂ g (u : HyperbolicL2) = 0 :=
  closedTensorGraph_zero_input_annihilates_actualDomain
    (mem_closedTensorGraph_of_tendsto hgraph hF hG) u

end

end ImbalancedChen.Part3.MaassFiniteCoreGraphClosure20261025a
